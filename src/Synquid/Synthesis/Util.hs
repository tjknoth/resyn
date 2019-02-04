{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module Synquid.Synthesis.Util where 

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Error
import Synquid.Util
import Synquid.Pretty
import Synquid.Tokens
import Synquid.Solver.Monad
import Synquid.Solver.TypeConstraint
import qualified Synquid.Solver.Util as TCSolver 

import Data.Maybe
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Char
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens
import Control.Monad.Extra (mapMaybeM)
import Data.Key (mapWithKeyM)
import Debug.Trace

{- Types -}

-- | Choices for the type of terminating fixpoint operator
data FixpointStrategy =
    DisableFixpoint   -- ^ Do not use fixpoint
  | FirstArgument     -- ^ Fixpoint decreases the first well-founded argument
  | AllArguments      -- ^ Fixpoint decreases the lexicographical tuple of all well-founded argument in declaration order
  | Nonterminating    -- ^ Fixpoint without termination check

-- | Choices for the order of e-term enumeration
data PickSymbolStrategy = PickDepthFirst | PickInterleave

-- | Parameters of program exploration
data ExplorerParams = ExplorerParams {
  _eGuessDepth :: Int,                    -- ^ Maximum depth of application trees
  _scrutineeDepth :: Int,                 -- ^ Maximum depth of application trees inside match scrutinees
  _matchDepth :: Int,                     -- ^ Maximum nesting level of matches
  _auxDepth :: Int,                       -- ^ Maximum nesting level of auxiliary functions (lambdas used as arguments)
  _fixStrategy :: FixpointStrategy,       -- ^ How to generate terminating fixpoints
  _polyRecursion :: Bool,                 -- ^ Enable polymorphic recursion?
  _predPolyRecursion :: Bool,             -- ^ Enable recursion polymorphic in abstract predicates?
  _abduceScrutinees :: Bool,              -- ^ Should we match eagerly on all unfolded variables?
  _unfoldLocals :: Bool,                  -- ^ Unfold binders introduced by matching (to use them in match abduction)?
  _partialSolution :: Bool,               -- ^ Should implementations that only cover part of the input space be accepted?
  _incrementalChecking :: Bool,           -- ^ Solve subtyping constraints during the bottom-up phase
  _consistencyChecking :: Bool,           -- ^ Check consistency of function's type with the goal before exploring arguments?
  _splitMeasures :: Bool,                 -- ^ Split subtyping constraints between datatypes into constraints over each measure
  _context :: RProgram -> RProgram,       -- ^ Context in which subterm is currently being generated (used only for logging and symmetry reduction)
  _symmetryReduction :: Bool,             -- ^ Should partial applications be memoized to check for redundancy?
  _sourcePos :: SourcePos,                -- ^ Source position of the current goal
  _explorerLogLevel :: Int,               -- ^ How verbose logging is
  _shouldCut :: Bool,                     -- ^ Should cut the search upon synthesizing a functionally correct branch
  _numPrograms :: Int,                    -- ^ Number of programs to search for
  _resourceArgs :: ResourceArgs           -- ^ Arguments relevant to resource analysis
}

makeLenses ''ExplorerParams

type Requirements = Map Id [RType]

-- | State of program exploration
data ExplorerState = ExplorerState {
  _typingState :: TypingState,                     -- ^ Type-checking state
  _auxGoals :: [Goal],                             -- ^ Subterms to be synthesized independently
  _solvedAuxGoals :: Map Id RProgram,              -- Synthesized auxiliary goals, to be inserted into the main program
  _lambdaLets :: Map Id (Environment, UProgram),   -- ^ Local bindings to be checked upon use (in type checking mode)
  _requiredTypes :: Requirements,                  -- ^ All types that a variable is required to comply to (in repair mode)
  _symbolUseCount :: Map Id Int                    -- ^ Number of times each symbol has been used in the program so far
} deriving (Eq, Ord)

makeLenses ''ExplorerState

-- | Persistent state accross explorations
newtype PersistentState = PersistentState { _typeErrors :: [ErrorMessage] }

makeLenses ''PersistentState

-- | Computations that explore program space, parametrized by the the horn solver @s@
type Explorer s = StateT ExplorerState (
                    ReaderT (ExplorerParams, TypingParams, Reconstructor s) (
                    LogicT (StateT PersistentState s)))

-- | This type encapsulates the 'reconstructTopLevel' function of the type checker,
-- which the explorer calls for auxiliary goals
newtype Reconstructor s = Reconstructor (Goal -> Explorer s RProgram) 

type TypeExplorer s = Environment -> RType -> Explorer s RProgram


throwErrorWithDescription :: MonadHorn s => Doc -> Explorer s a
throwErrorWithDescription msg = do
  pos <- asks . view $ _1 . sourcePos
  throwError $ ErrorMessage TypeError pos msg

-- | Record type error and backtrack
throwError :: MonadHorn s => ErrorMessage -> Explorer s a
throwError e = do
  writeLog 2 $ text "TYPE ERROR:" <+> plain (emDescription e)
  lift . lift . lift $ typeErrors %= (e :)
  mzero

-- | Impose typing constraint @c@ on the programs
addConstraint c = typingState %= addTypingConstraint c

-- | When constant-time flag is set, add the appropriate constraint 
addCTConstraint :: MonadHorn s => Environment -> Id -> Explorer s ()
addCTConstraint env tag = do 
  checkCT <- asks . view $ _1 . resourceArgs . constantTime
  let c = ConstantRes env tag
  when checkCT $ addConstraint c

-- | Embed a type-constraint checker computation @f@ in the explorer; on type error, record the error and backtrack
runInSolver :: MonadHorn s => TCSolver s a -> Explorer s a
runInSolver f = do
  tParams <- asks . view $ _2
  tState <- use typingState
  res <- lift . lift . lift . lift $ runTCSolver tParams tState f 
  case res of
    Left err -> throwError err
    Right (res, st) -> do
      typingState .= st
      return res

freshId :: MonadHorn s => String -> Explorer s String
freshId = runInSolver . TCSolver.freshId

freshVar :: MonadHorn s => Environment -> String -> Explorer s String
freshVar env prefix = runInSolver $ TCSolver.freshVar env prefix

inContext ctx = local (over (_1 . context) (. ctx))

-- | Return the current valuation of @u@;
-- in case there are multiple solutions,
-- order them from weakest to strongest in terms of valuation of @u@ and split the computation
currentValuation :: MonadHorn s => Formula -> Explorer s Valuation
currentValuation u = do
  runInSolver solveAllCandidates
  cands <- use (typingState . candidates)
  let candGroups = groupBy (\c1 c2 -> val c1 == val c2) $ sortBy (\c1 c2 -> setCompare (val c1) (val c2)) cands
  msum $ map pickCandidiate candGroups
  where
    val c = valuation (solution c) u
    pickCandidiate cands' = do
      typingState . candidates .= cands'
      return $ val (head cands')

-- | Replace all bound type and predicate variables with fresh free variables
-- (if @top@ is @False@, instantiate with bottom refinements instead of top refinements)
instantiate :: MonadHorn s => Environment -> RSchema -> Bool -> [Id] -> Explorer s RType
instantiate env sch top argNames = do
  t <- instantiate' Map.empty Map.empty sch
  writeLog 3 (text "INSTANTIATE" <+> pretty sch $+$ text "INTO" <+> pretty t)
  return t
  where
    instantiate' subst pSubst t@(ForallT a sch) = do
      a' <- freshId "A"
      addConstraint $ WellFormed env (vartSafe a' ftrue) (show (text "Instantiate" <+> plain (pretty t)))
      instantiate' (Map.insert a (vartSafe a' (BoolLit top)) subst) pSubst sch
    instantiate' subst pSubst (ForallP (PredSig p argSorts _) sch) = do
      let argSorts' = map (sortSubstitute (asSortSubst subst)) argSorts
      fml <- if top
              then do
                p' <- freshId (map toUpper p)
                addConstraint $ WellFormedPredicate env argSorts' p'
                return $ Pred BoolS p' (zipWith Var argSorts' deBrujns)
              else return ffalse
      instantiate' subst (Map.insert p fml pSubst) sch
    instantiate' subst pSubst (Monotype t) = go subst pSubst argNames t
    go subst pSubst argNames (FunctionT x tArg tRes cost) = do
      x' <- case argNames of
              [] -> freshVar env "x"
              (argName : _) -> return argName
      liftM2 (\t r -> FunctionT x' t r cost) (go subst pSubst [] tArg) (go subst pSubst (drop 1 argNames) (renameVar (isBoundTV subst) x x' tArg tRes))
    go subst pSubst _ t = return $ typeSubstitutePred pSubst . typeSubstitute subst $ t
    isBoundTV subst a = (a `Map.member` subst) || (a `elem` (env ^. boundTypeVars))

-- | 'symbolType' @env x sch@: precise type of symbol @x@, which has a schema @sch@ in environment @env@;
-- if @x@ is a scalar variable, use "_v == x" as refinement;
-- if @sch@ is a polytype, return a fresh instance
symbolType :: MonadHorn s => Environment -> Id -> RSchema -> Explorer s RType
symbolType env x (Monotype t@(ScalarT b _ p))
    | isLiteral x = return t -- x is a literal of a primitive type, it's type is precise
    | isJust (lookupConstructor x env) = return t -- x is a constructor, it's type is precise
    | otherwise = return $ ScalarT b (varRefinement x (toSort b)) p -- x is a scalar variable or monomorphic scalar constant, use _v = x
symbolType env _ sch = freshInstance sch
  where
    freshInstance sch = if arity (toMonotype sch) == 0
      then instantiate env sch False [] -- Nullary polymorphic function: it is safe to instantiate it with bottom refinements, since nothing can force the refinements to be weaker
      else instantiate env sch True []

-- | Perform an exploration, and once it succeeds, do not backtrack (assuming flag is set)
cut :: MonadHorn s => Explorer s a -> Explorer s a
cut e = do 
  b <- asks . view $ _1 . shouldCut
  if b then once e else e

safeAddVariable :: Monad s => String -> RType -> Environment -> Explorer s Environment
safeAddVariable x t@FunctionT{} env = return $ addVariable x t env
safeAddVariable x typ env = do
  (typingState . universalFmls) %= Set.insert (Var (toSort (baseTypeOf typ)) x) 
  return $ addVariable x typ env

-- | Synthesize auxiliary goals accumulated in @auxGoals@ and store the result in @solvedAuxGoals@
generateAuxGoals :: MonadHorn s => Explorer s ()
generateAuxGoals = do
  goals <- use auxGoals
  unless (null goals) $ writeLog 3 $ text "Auxiliary goals are:" $+$ vsep (map pretty goals)
  case goals of
    [] -> return ()
    (g : gs) -> do
        auxGoals .= gs
        writeLog 2 $ text "PICK AUXILIARY GOAL" <+> pretty g
        Reconstructor reconstructTopLevel <- asks . view $ _3
        p <- reconstructTopLevel g
        solvedAuxGoals %= Map.insert (gName g) (etaContract p)
        generateAuxGoals
  where
    etaContract p = case etaContract' [] (content p) of
                      Nothing -> p
                      Just f -> Program f (typeOf p)
    etaContract' [] (PFix _ p)                                               = etaContract' [] (content p)
    etaContract' binders (PFun x p)                                          = etaContract' (x:binders) (content p)
    etaContract' (x:binders) (PApp pFun (Program (PSymbol y) _)) | x == y    = etaContract' binders (content pFun)
    etaContract' [] f@(PSymbol _)                                            = Just f
    etaContract' binders p                                                   = Nothing

checkResourceVar :: Monad s 
                 => Environment
                 -> String 
                 -> RType
                 -> Explorer s Bool 
checkResourceVar env x t = do 
  tstate <- use typingState 
  -- TODO: figure out how to use lenses so I can skip the intermediate bind lmao
  tparams <- asks . view $ _2 
  let isRV = TCSolver.isResourceVariable env tstate (_cegisDomain tparams) x t 
  return isRV

-- THIS IS FUCKED
makeResourceVar :: Monad s  
                => Environment 
                -> Maybe (RBase) 
                -> String 
                -> Explorer s (String, [Formula])
makeResourceVar env vvtype name = do
  let universalsInScope = toMonotype <$> TCSolver.nonGhostScalars env 
  let mkUFml (x, t) = do
        isRV <- checkResourceVar env x t
        return $ if isRV 
          then Just $ Var ((toSort . baseTypeOf) t) x
          else Nothing 
  domain <- mapMaybeM mkUFml (Map.assocs universalsInScope)
  return (name, domain)
  -- Shouldn't be necessary to have _v in scope... 
  --   there will always be an assumption of the form _v == x, 
  --   where x is some variable in context.
  {- return $ case vvtype of 
    Nothing -> (name, domain)
    Just b  -> (name, Var (toSort b) valueVarName : domain)
  -}

insertRVar (name, info) = Map.insert name info

freshPot :: MonadHorn s 
         => Environment 
         -> Maybe RBase
         -> Explorer s Formula
freshPot env vtype = freshResAnnotation env vtype potentialPrefix

freshMul :: MonadHorn s 
         => Environment 
         -> Maybe RBase
         -> Explorer s Formula
freshMul env vtype = freshResAnnotation env vtype multiplicityPrefix

freshFreePotential :: MonadHorn s 
                   => Environment 
                   -> Explorer s Formula
freshFreePotential env = freshResAnnotation env Nothing freePotentialPrefix

freshResAnnotation :: MonadHorn s
                   => Environment
                   -> Maybe RBase 
                   -> String
                   -> Explorer s Formula
freshResAnnotation env vtype prefix = do 
  x <- freshId prefix 
  rvar <- makeResourceVar env vtype x 
  (typingState . resourceVars) %= insertRVar rvar 
  return $ Var IntS x


-- | 'freshPotentials' @sch r@ : Replace potentials in schema @sch@ by unwrapping the foralls. If @r@, recursively replace potential annotations in the entire type. Otherwise, just replace top-level annotations.
freshPotentials :: MonadHorn s 
                => Environment 
                -> RSchema 
                -> Bool 
                -> Explorer s RSchema
freshPotentials env (Monotype t) isTransfer = 
  Monotype <$> freshPotentials' env t isTransfer
freshPotentials env (ForallT x t) isTransfer = 
  ForallT x <$> freshPotentials env t isTransfer
freshPotentials env (ForallP x t) isTransfer = 
  ForallP x <$> freshPotentials env t isTransfer

-- Replace potentials in a TypeSkeleton
freshPotentials' :: MonadHorn s 
                 => Environment 
                 -> RType 
                 -> Bool 
                 -> Explorer s RType
freshPotentials' env (ScalarT base fml (Ite g t f)) isTransfer = do
  t' <- freshPot env (if isTransfer then Nothing else Just base) 
  f' <- freshPot env (if isTransfer then Nothing else Just base) 
  base' <- if isTransfer then return base else freshMultiplicities env base isTransfer 
  return $ ScalarT base' fml $ Ite g t' f' 
freshPotentials' env (ScalarT base fml pot) isTransfer = do 
  pot' <- freshPot env (if isTransfer then Nothing else Just base)
  base' <- if isTransfer then return base else freshMultiplicities env base isTransfer 
  return $ ScalarT base' fml pot'
freshPotentials' _ t _ = return t

-- Replace potentials in a BaseType
freshMultiplicities :: MonadHorn s 
                    => Environment 
                    -> RBase 
                    -> Bool 
                    -> Explorer s (RBase)
freshMultiplicities env b@(TypeVarT s x m) _ = do 
  m' <- freshMul env Nothing
  return $ TypeVarT s x m'
freshMultiplicities env (DatatypeT x ts ps) isTransfer = do
  ts' <- mapM (\t -> freshPotentials' env t isTransfer) ts
  return $ DatatypeT x ts' ps
freshMultiplicities _ t _ = return t

addScrutineeToEnv :: (MonadHorn s, MonadSMT s) 
                  => Environment 
                  -> RProgram 
                  -> RType 
                  -> Explorer s (Formula, Environment)
addScrutineeToEnv env pScr tScr = do 
  --checkres <- asks . view $ _1 . resourceArgs . checkRes
  (x, env') <- toVar (addScrutinee pScr env) pScr
  varName <- freshId "x"
  let tScr' = addPotential (typeMultiply fzero tScr) (fromMaybe fzero (topPotentialOf tScr))
  return (x, env')

-- | Generate subtyping constraint
addSubtypeConstraint :: (MonadHorn s, MonadSMT s) 
                     => Environment 
                     -> RType 
                     -> RType 
                     -> Bool 
                     -> Id 
                     -> Explorer s ()
addSubtypeConstraint env ltyp rtyp consistency tag = 
  addConstraint $ Subtype env ltyp rtyp consistency tag

-- Split a context and generate sharing constraints
shareContext :: (MonadHorn s, MonadSMT s) 
             => Environment 
             -> String 
             -> Explorer s (Environment, Environment)
shareContext env label = do
  --traceM $ show $ symbolsOfArity 0 env 
  symsl <- safeFreshPotentials env False
  symsr <- safeFreshPotentials env False
  (fpl, fpr) <- shareFreePotential env False (env ^. freePotential) label
  
  let ghosts = _ghostSymbols env

  let envl = mkResourceEnv symsl ghosts fpl
  let envr = mkResourceEnv symsr ghosts fpr
  addConstraint $ SharedEnv env envl envr label
  return (env { _symbols = symsl, _freePotential = fpl }, env { _symbols = symsr, _freePotential = fpr })

shareFreePotential :: (MonadHorn s, MonadSMT s)
                   => Environment
                   -> Bool
                   -> Formula 
                   -> String
                   -> Explorer s (Formula, Formula) 
shareFreePotential env genConstraint fp@(Ite g _ _) label = do 
  fp1 <- freshFreePotential env
  fp2 <- freshFreePotential env
  fp3 <- freshFreePotential env
  fp4 <- freshFreePotential env
  let fp' = Ite g fp1 fp3 
  let fp'' = Ite g fp2 fp4
  let env = emptyEnv { _freePotential = fp }
  let env' = emptyEnv { _freePotential = fp' }
  let env'' = emptyEnv { _freePotential = fp'' }
  when genConstraint $
    addConstraint $ SharedEnv env env' env'' label
  return (fp', fp'')
shareFreePotential env genConstraint fp label = do 
  fp' <- freshFreePotential env
  fp'' <- freshFreePotential env
  let env = emptyEnv { _freePotential = fp }
  let env' = emptyEnv { _freePotential = fp' }
  let env'' = emptyEnv { _freePotential = fp'' }

  when genConstraint $ 
    addConstraint $ SharedEnv env env' env'' label
  return (fp', fp'')

-- Transfer potential between variables in a context if necessary
transferPotential :: (MonadHorn s, MonadSMT s)
                  => Environment 
                  -> String 
                  -> Explorer s Environment
transferPotential env label = do 
  fp <- freshFreePotential env --transferFreePotential env 
  syms' <- safeFreshPotentials env True
  let env' = mkResourceEnv syms' (_ghostSymbols env) fp
  
  addConstraint $ Transfer env env' label
  return $ env { _symbols = syms', _freePotential = fp }

transferFreePotential :: (MonadHorn s, MonadSMT s)
                      => Environment
                      -> Explorer s Formula
transferFreePotential env = do 
  let scalars = Map.elems $ TCSolver.nonGhostScalars env 
  let conds = mapMaybe (getConditional . toMonotype) scalars
  case conds of 
    [] -> freshFreePotential env
    Ite g _ _ : _ -> do 
      fpt <- freshFreePotential env 
      fpf <- freshFreePotential env 
      return $ Ite g fpt fpf

safeFreshPotentials :: (MonadHorn s, MonadSMT s)
                    => Environment
                    -> Bool
                    -> Explorer s SymbolMap
safeFreshPotentials env isTransfer = do 
  let ghosts = env ^. ghostSymbols
  let replace (x, sch) = if Set.member x ghosts 
      then return (x, sch)
      else do 
        sch' <- freshPotentials env sch isTransfer
        return (x, sch')
  let syms = env ^. symbols
  let scalars = Map.assocs $ fromMaybe Map.empty $ Map.lookup 0 syms 
  scalars' <- mapM replace scalars
  return $ Map.insert 0 (Map.fromList scalars') syms

storeCase :: Monad s 
          => Environment 
          -> Case RType 
          -> Explorer s ()
storeCase env (Case cons args _) = do 
  let resSort = resultSort $ toMonotype $ allSymbols env Map.! cons
  let mkArgVar x = flip Var x $ toSort $ baseTypeOf $ toMonotype $ symbolsOfArity 0 env Map.! x
  (typingState . matchCases) %= Set.insert (Cons resSort cons (map mkArgVar args))

mapTuple f (x, y) = (f x, f y)

-- | 'toVar' @p env@: a variable representing @p@ (can be @p@ itself or a fresh ghost)
toVar :: (MonadSMT s, MonadHorn s) 
      => Environment 
      -> RProgram 
      -> Explorer s (Formula, Environment)
toVar env (Program (PSymbol name) t) = return (symbolAsFormula env name t, env)
toVar env (Program _ t) = do
  g <- freshId "G"
  return (Var (toSort $ baseTypeOf t) g, addLetBound g t env)

freePotentialPrefix = "fp"

writeLog level msg = do
  maxLevel <- asks . view $ _1 . explorerLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return () 