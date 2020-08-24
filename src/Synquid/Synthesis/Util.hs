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
import Synquid.Solver.Types
-- import Synquid.Solver.TypeConstraint

import           Data.Maybe
import           Data.List
import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Set (Set)
import           Data.Char
import           Control.Monad.Logic
import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Lens
import           Control.Monad.Extra (mapMaybeM)
import           Debug.Trace

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
  _explorerResourceArgs :: ResourceParams -- ^ Arguments relevant to resource analysis
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
addTypingConstraint c = over typingConstraints (nub . (c :))

-- | Impose typing constraint @c@ on the programs
addConstraint c = typingState %= addTypingConstraint c

-- | When constant-time flag is set, add the appropriate constraint
addCTConstraint :: MonadHorn s => Environment -> Explorer s ()
addCTConstraint env = do
  checkCT <- asks . view $ _1 . explorerResourceArgs . constantTime
  let c = ConstantRes env 
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

-- freshId :: MonadHorn s => String -> Explorer s String
-- freshId = runInSolver . freshId

-- freshVar :: MonadHorn s => Environment -> String -> Explorer s String
-- freshVar env prefix = runInSolver $ freshVar env prefix

inContext ctx = local (over (_1 . context) (. ctx))

{- 
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
-}

-- | Replace all bound type and predicate variables with fresh free variables
-- (if @top@ is @False@, instantiate with bottom refinements instead of top refinements)
instantiate :: MonadHorn s => Environment -> RSchema -> Bool -> [Id] -> Explorer s RType
instantiate env sch top argNames = do
  t <- instantiate' Map.empty Map.empty sch
  writeLog 3 (text "INSTANTIATE" <+> pretty sch $+$ text "INTO" <+> pretty t)
  return t
  where
    instantiate' subst pSubst t@(ForallT a sch) = do
      a' <- runInSolver $ freshId "A"
      addConstraint $ WellFormed env (vartSafe a' ftrue) 
      instantiate' (Map.insert a (vartSafe a' (BoolLit top)) subst) pSubst sch
{-  instantiate' subst pSubst (ForallP (PredSig p argSorts _) sch) = do -- APs: changed 
      let argSorts' = map (sortSubstitute (asSortSubst subst)) argSorts
      fml <- if top
              then do
                p' <- runInSolver $ freshId (map toUpper p)
                addConstraint $ WellFormedPredicate env argSorts' p'
                return $ Pred BoolS p' (zipWith Var argSorts' deBrujns)
              else return ffalse
      instantiate' subst (Map.insert p fml pSubst) sch
-}
    instantiate' subst pSubst (ForallP (PredSig p argSorts resSort) sch) = do
      let argSorts' = map (sortSubstitute (asSortSubst subst)) argSorts
      fml <- if top
              then do
                p' <- runInSolver $ freshId (map toUpper p)
                addConstraint $ WellFormedPredicate env argSorts' resSort p'
                return $ Pred resSort p' (zipWith Var argSorts' deBrujns)
              else return $ if resSort == BoolS then ffalse else pbot 
      instantiate' subst (Map.insert p fml pSubst) sch
    instantiate' subst pSubst (Monotype t) = go subst pSubst argNames t
    go subst pSubst argNames (FunctionT x tArg tRes cost) = do
      x' <- case argNames of
              [] -> runInSolver $ freshVar env "x"
              (argName : _) -> return argName
      liftM2 (\t r -> FunctionT x' t r cost) (go subst pSubst [] tArg) (go subst pSubst (drop 1 argNames) (renameVar (isBoundTV subst) x x' tArg tRes))
    go subst pSubst _ t@(ScalarT baseT r p) = 
      return $ typeSubstitutePred pSubst . typeSubstitute subst $ t
    go _ _ _ t = error $ unwords ["instantiating contextual type:", show (pretty t)]
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
  (typingState . persistentState . universalVars) %= Set.insert x -- (Var (toSort (baseTypeOf typ)) x)
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
                 -> TCSolver s Bool
checkResourceVar env x t = do
  -- tstate <- use typingState
  tstate <- get
  tparams <- ask
  -- TODO: figure out how to use lenses so I can skip the intermediate bind
  -- tparams <- asks . view $ _2
  domain <- view $ resourceArgs . rSolverDomain
  let isRV = isResourceVariable env tstate domain x t
  return isRV

mkResourceVar :: MonadHorn s
              => Environment
              -> Maybe (RBase)
              -> String
              -> TCSolver s (String, [Formula])
mkResourceVar env vvtype name = do
  let universalsInScope = toMonotype <$> nonGhostScalars env
  let mkUFml (x, t) = do
        isRV <- checkResourceVar env x t
        return $ if isRV
          then Just $ Var ((toSort . baseTypeOf) t) x
          else Nothing
  domain <- mapMaybeM mkUFml (Map.assocs universalsInScope)
  return $ case vvtype of
    Nothing -> (name, domain)
    Just b  -> (name, Var (toSort b) valueVarName : domain)

insertRVar (name, info) = Map.insert name info

safeFreshPot :: MonadHorn s 
             => Environment 
             -> Maybe RBase 
             -> Formula
             -> TCSolver s Formula
safeFreshPot env vtype original 
  | original == fzero = return fzero
  | otherwise = freshPot env vtype

freshPot :: MonadHorn s
         => Environment
         -> Maybe RBase
         -> TCSolver s Formula
freshPot env vtype = freshResAnnotation env vtype potentialPrefix

freshMul :: MonadHorn s
         => Environment
         -> Maybe RBase
         -> TCSolver s Formula
freshMul env vtype = freshResAnnotation env vtype multiplicityPrefix

freshFreePotential :: MonadHorn s
                   => Environment
                   -> TCSolver s Formula
freshFreePotential env = freshResAnnotation env Nothing freePotentialPrefix

freshCondFreePotential :: MonadHorn s
                       => Environment
                       -> TCSolver s Formula
freshCondFreePotential env = freshResAnnotation env Nothing condFreePotentialPrefix


freshResAnnotation :: MonadHorn s
                   => Environment
                   -> Maybe RBase
                   -> String
                   -> TCSolver s Formula
freshResAnnotation env vtype prefix = do
  x <- freshId prefix
  rvar <- mkResourceVar env vtype x
  persistentState . resourceVars %= insertRVar rvar
  let fresh = Var IntS x
  let env' = 
        case vtype of
          Nothing -> env
          Just b  -> addVariable valueVarName (ScalarT b ftrue defPotential) env
  modify $ addTypingConstraint $ WellFormedPotential env' fresh
  return fresh

-- | 'schFreshPotentials' @env sch r@ : Replace potentials in schema @sch@ by unwrapping the foralls.
--    If @r@, recursively replace potential annotations in the entire type. Otherwise, just replace top-level annotations.
schFreshPotentials :: MonadHorn s
                   => Environment
                   -> RSchema
                   -> TCSolver s RSchema
schFreshPotentials env (Monotype t) =
  Monotype <$> freshPotentialsType env t 
schFreshPotentials env (ForallT x t) =
  ForallT x <$> schFreshPotentials env t 
schFreshPotentials env (ForallP x t) =
  ForallP x <$> schFreshPotentials env t 

-- Replace potentials in a TypeSkeleton

-- Retain conditional structure of potentials in a type when freshening
freshPotentialsType :: MonadHorn s
                    => Environment
                    -> RType
                    -> TCSolver s RType
freshPotentialsType env t = do
  pass <- use predAssignment
  let (ScalarT base fml p) = typeSubstitutePred pass t
  base' <- freshPotentialsBase env base
  p' <- freshPotentialsType' env base p -- (substitutePredicate pass p)
  return $ ScalarT base' fml p'

freshPotentialsType' :: MonadHorn s => Environment -> RBase -> Formula -> TCSolver s Formula
freshPotentialsType' env base pot = 
  case itesOf pot of
    [] -> safeFreshPot env (Just base) pot
    -- xs -> sumFormulas <$> mapM (\(Ite g t f) -> Ite g <$> safeFreshPot env (Just base) t <*> safeFreshPot env (Just base) f) xs
    xs -> sumFormulas <$> mapM (\(Ite g t f) -> Ite g <$> freshPot env (Just base) <*> freshPot env (Just base)) xs

-- Retain conditional structure of formula when freshening
freshPotentials :: MonadHorn s => Environment -> Maybe RBase -> Formula -> TCSolver s Formula
freshPotentials env rb (Ite g t f) = Ite g <$> freshPot env rb <*> freshPot env rb
freshPotentials env rb f = freshPot env rb

-- Replace potentials in a BaseType
freshPotentialsBase :: MonadHorn s
                    => Environment
                    -> RBase
                    -> TCSolver s RBase
freshPotentialsBase env b@(TypeVarT s x m) = do
  m' <- freshMul env Nothing
  return $ TypeVarT s x m'
freshPotentialsBase env (DatatypeT name ts ps) = do
  ts' <- mapM (freshPotentialsType env) ts
  ps' <- freshAPs env name ps
  return $ DatatypeT name ts' ps'
freshPotentialsBase _ t = return t

freshPred :: MonadHorn s => Environment -> [Sort] -> Sort -> TCSolver s Formula
freshPred env argSorts resSort = do
  p' <- freshId "P"
  modify $ addTypingConstraint (WellFormedPredicate env argSorts resSort p')
  let args = [] -- zipWith Var argSorts deBrujns -- TODO: why not?
  when (resSort == IntS) $
    modify $ addTypingConstraint (WellFormedPotential env (Pred resSort p' args))
  return $ Pred resSort p' args

freshAPs :: MonadHorn s => Environment -> String -> [Formula] -> TCSolver s [Formula]
freshAPs env dt ps = 
  let (DatatypeDef _ pParams _ _ _ _) = (env ^. datatypes) Map.! dt
      adjust p sig = if predSigResSort sig == IntS then freshAP env p (predSigArgSorts sig) else return p
   in zipWithM adjust ps pParams

freshAP :: MonadHorn s => Environment -> Formula -> [Sort] -> TCSolver s Formula
freshAP env (Ite g t f) args = Ite g <$> freshPred env args IntS <*> freshPred env args IntS 
freshAP env p args = freshPred env args IntS

addScrutineeToEnv :: (MonadHorn s, MonadSMT s)
                  => Environment
                  -> RProgram
                  -> RType
                  -> Explorer s (Formula, Environment)
addScrutineeToEnv env pScr tScr = do
  --checkres <- asks . view $ _1 . resourceArgs . checkRes
  (x, env') <- toVar (addScrutinee pScr env) pScr
  varName <- runInSolver $ freshId "x"
  -- TODO: is this wrong?? probably not bc of sharing + unification? Had tscr' defined but not used...
  -- Should tscr' be added to env'?
  -- let tScr' = addPotential (typeMultiply fzero tScr) (fromMaybe fzero (topPotentialOf tScr))
  return (x, env')

-- | Generate subtyping constraint
addSubtypeConstraint :: (MonadHorn s, MonadSMT s)
                     => Environment
                     -> RType
                     -> RType
                     -> Bool
                     -> Explorer s ()
addSubtypeConstraint env ltyp rtyp consistency =
  addConstraint $ Subtype env ltyp rtyp consistency 

-- Split a context and generate sharing constraints
shareContext :: (MonadHorn s, MonadSMT s)
             => Environment
             -> Explorer s (Environment, Environment)
shareContext env = do
  --symsl <- safeFreshPotentials env False
  --symsr <- safeFreshPotentials env False
  symsl <- runInSolver $ freshSharingPotential env
  symsr <- runInSolver $ freshSharingPotential env
  (fpl, fpr) <- shareFreePotential env (env ^. freePotential) 
  (cfpl, cfpr) <- shareCondFP env (env ^. condFreePotential) 
  let ghosts = _ghostSymbols env

  -- Don't need to re-share fp and cfp:
  let envl = mkResourceEnv symsl ghosts fzero []
  let envr = mkResourceEnv symsr ghosts fzero []
  addConstraint $ SharedEnv env envl envr 
  return (env { _symbols = symsl, _freePotential = fpl, _condFreePotential = cfpl }
        , env { _symbols = symsr, _freePotential = fpr, _condFreePotential = cfpr })

shareFreePotential :: (MonadHorn s, MonadSMT s)
                   => Environment
                   -> Formula
                   -> Explorer s (Formula, Formula)
shareFreePotential env fp@(Ite g _ _) =
  error "shareFreePotential: conditional expression"
shareFreePotential env fp = do
  fp' <- runInSolver $ freshFreePotential env
  fp'' <- runInSolver $ freshFreePotential env
  addConstraint $ SharedForm env fp fp' fp'' 
  return (fp', fp'')

shareCondFP :: (MonadHorn s, MonadSMT s)
            => Environment
            -> [Formula]
            -> Explorer s ([Formula], [Formula])
shareCondFP env fmls =
  let share f = do
        f1 <- runInSolver $ freshCondFP env f
        f2 <- runInSolver $ freshCondFP env f
        addConstraint $ SharedForm env f f1 f2 
        return (f1, f2)
  in  unzip <$> mapM share fmls

-- Transfer potential between variables in a context if necessary
transferPotential :: (MonadHorn s, MonadSMT s)
                  => Environment
                  -> Explorer s Environment
transferPotential env = do
  fp <- runInSolver $ freshFreePotential env
  (syms', cfps) <- runInSolver $ freshRestructuredPotentials env
  let env' = mkResourceEnv syms' (_ghostSymbols env) fp cfps
  addConstraint $ Transfer env env' 
  return $ env { _symbols = syms', _freePotential = fp, _condFreePotential = cfps }

-- When transferring potentials, replace top-level annotations but also
--   collect all conditional top-level annotations from the top-level to
--   extend condFreePotential
freshRestructuredPotentials :: (MonadHorn s, MonadSMT s)
                            => Environment
                            -> TCSolver s (SymbolMap, [Formula])
freshRestructuredPotentials env = do
  let ghosts = env ^. ghostSymbols
  let cfps = Map.elems $ Map.mapMaybeWithKey (gatherCondPotential ghosts) (symbolsOfArity 0 env)
  cfps' <- mapM (freshCondFP env) cfps
  -- syms' <- safeFreshPotentials env True
  let syms' = zeroTopLevel env
  return (syms', cfps')

gatherCondPotential :: Set String -> String -> RSchema -> Maybe Formula
gatherCondPotential ghosts x sch =
  let getCond (ScalarT _ _ (Ite g t f)) = Just (Ite g t f)
      getCond _                         = Nothing in
  if x `Set.member` ghosts
    then Nothing
    else
      let varSort = toSort . baseTypeOf . toMonotype
          sub = Map.singleton valueVarName (Var (varSort sch) x) in
      substitute sub <$> (getCond . toMonotype) sch

shareAndExtractFP :: (MonadHorn s, MonadSMT s)
                  => Environment
                  -> Formula
                  -> [Formula]
                  -> Explorer s (Environment, Environment, Formula)
shareAndExtractFP env fp cfps = do 
  (fp', fp'')  <- shareFreePotential env fp 
  (cfp', cfp'') <- shareCondFP env cfps 
  (env1, env2) <- shareContext (env { _freePotential = fp', _condFreePotential = cfp' }) 
  let fpout = fp'' |+| sumFormulas cfp''
  return (env1, env2, fpout)


freshCondFP :: MonadHorn s
            => Environment
            -> Formula
            -> TCSolver s Formula
freshCondFP env (Ite g f1 f2) = do
  f1' <- freshCondFP env f1
  f2' <- freshCondFP env f2
  return $ Ite g f1' f2'
freshCondFP env _ = freshCondFreePotential env

-- When sharing, share 0 \/ 0,0 to reduce number of constraints
freshSharingPotential :: MonadHorn s => Environment -> TCSolver s SymbolMap
freshSharingPotential env = do 
  let ghosts = env ^. ghostSymbols
  let replace (x, sch) = if x `Set.member` ghosts 
        then return (x, sch)
        else do 
          sch' <- schFreshPotentials env sch 
          return (x, sch')
  let syms = env ^. symbols 
  let scalars = Map.assocs $ fromMaybe Map.empty $ Map.lookup 0 syms
  scalars' <- mapM replace scalars 
  return $ Map.insert 0 (Map.fromList scalars') syms

-- When transferring, replace top-level annotations with zeros -- all potential flows into "free potential"
zeroTopLevel :: Environment -> SymbolMap
zeroTopLevel env = 
  let remove (ScalarT b r _) = ScalarT b r fzero 
      scalars = symbolsOfArity 0 env in 
  Map.insert 0 (fmap remove <$> scalars) (env ^. symbols)

storeCase :: Monad s
          => Environment
          -> Case RType
          -> Explorer s ()
storeCase env (Case cons args _) = do
  let resSort = resultSort $ toMonotype $ allSymbols env Map.! cons
  let mkArgVar x = flip Var x $ toSort $ baseTypeOf $ toMonotype $ symbolsOfArity 0 env Map.! x
  (typingState . matchCases) %= Set.insert (Cons resSort cons (map mkArgVar args))


-- | 'toVar' @p env@: a variable representing @p@ (can be @p@ itself or a fresh ghost)
toVar :: (MonadSMT s, MonadHorn s)
      => Environment
      -> RProgram
      -> Explorer s (Formula, Environment)
toVar env (Program (PSymbol name) t) = return (symbolAsFormula env name t, env)
toVar env (Program _ t) = do
  g <- runInSolver $ freshId "G"
  return (Var (toSort $ baseTypeOf t) g, addLetBound g t env)


freePotentialPrefix = "fr"
condFreePotentialPrefix = "cnd"

writeLog level msg = do
  maxLevel <- asks . view $ _1 . explorerLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return ()

-- | Assumptions encoded in an environment
embedding :: Monad s => Environment -> Set Id -> Bool -> Bool -> TCSolver s (Set Formula)
embedding env vars includeQuantified isRes = do
    tass <- use typeAssignment
    pass <- use predAssignment
    qmap <- use qualifierMap
    let ass = Set.map (substitutePredicate pass) (env ^. assumptions)
    let allVars = vars `Set.union` potentialVars qmap (conjunction ass)
    return $ addBindings env tass pass qmap ass allVars
  where
    addBindings env tass pass qmap fmls vars = 
      if Set.null vars
        then fmls
        else let (x, rest) = Set.deleteFindMin vars in
             case Map.lookup x (allSymbols env) of
                Nothing -> addBindings env tass pass qmap fmls rest -- Variable not found (useful to ignore value variables)
                Just (Monotype t) -> case typeSubstitute tass t of
                  ScalarT baseT fml pot ->
                    let fml' = if isRes then adjustFml fml else fml
                        --fml' = fml --if substituteValueVars then substitute (Map.singleton valueVarName (Var IntS x)) fml else fml
                        fmls' = Set.fromList $ map (substitute (Map.singleton valueVarName (Var (toSort baseT) x)) . substitutePredicate pass)
                                          (fml' : allMeasurePostconditions includeQuantified baseT env) 
                        newVars = Set.delete x $ setConcatMap (potentialVars qmap) fmls' in 
                    addBindings env tass pass qmap (fmls `Set.union` fmls') (rest `Set.union` newVars)
                  LetT y tDef tBody -> addBindings (addGhostVariable x tBody . addGhostVariable y tDef . removeVariable x $ env) tass pass qmap fmls vars
                  AnyT -> Set.singleton ffalse
                  _ -> error $ unwords ["embedding: encountered non-scalar variable", x, "in 0-arity bucket"]
                Just sch -> addBindings env tass pass qmap fmls rest -- TODO: why did this work before?
    adjustFml = removePreds (Map.keys (allRMeasures env))
    allSymbols = symbolsOfArity 0 

embedEnv :: Monad s => Environment -> Formula -> Bool -> Bool -> TCSolver s (Set Formula)
embedEnv env fml consistency isRes = do 
  qmap <- use qualifierMap
  let relevantVars = potentialVars qmap fml
  embedding env relevantVars consistency isRes

embedSynthesisEnv :: MonadHorn s 
                  => Environment 
                  -> Formula 
                  -> Bool 
                  -> TCSolver s (Set Formula)
embedSynthesisEnv env fml consistency = do 
  let env' = env { _measureDefs = Map.empty } -- don't instantiate measures 
  embedEnv env' fml consistency True

allUnknowns :: Environment -> Set Formula 
allUnknowns env = Set.filter isUnknownForm $ env ^. assumptions

assignUnknowns :: MonadHorn s => Set Formula -> TCSolver s (Set Formula)
assignUnknowns fmls = do 
  sol <- solution . head <$> use candidates
  return $ Set.map fromJust $ Set.filter isJust $ Set.map (fmap conjunction . getUnknown sol) fmls
  where 
    getUnknown solution (Unknown _ u) = Map.lookup u solution

assignUnknownsInFml :: MonadHorn s => Formula -> TCSolver s Formula
assignUnknownsInFml fml = do
  sol <- solution . head <$> use candidates
  return $ applySolution sol fml
  
-- | 'instantiateConsAxioms' @env fml@ : If @fml@ contains constructor applications, return the set of instantiations of constructor axioms for those applications in the environment @env@
instantiateConsAxioms :: Environment -> Bool -> Maybe Formula -> Formula -> Set Formula
instantiateConsAxioms env forRes mVal fml =
  let inst = instantiateConsAxioms env forRes mVal 
      allMeasures dt e = Map.assocs $
        if forRes 
          then allRMeasuresOf dt e
          else allMeasuresOf dt e
  in case fml of
    Cons resS@(DataS dtName _) ctor args -> 
      Set.unions $ Set.fromList (map (measureAxiom resS ctor args) (allMeasures dtName env)) 
                   : map (instantiateConsAxioms env forRes Nothing) args
    Unary op e -> inst e
    Binary op e1 e2 -> inst e1 `Set.union` inst e2
    Ite e0 e1 e2 -> inst e0 `Set.union` inst e1 `Set.union` inst e2
    SetLit _ elems -> Set.unions (map inst elems)
    Pred _ p args -> Set.unions $ map inst args
    _ -> Set.empty
  where
    measureAxiom resS ctor args (mname, MeasureDef inSort _ defs constArgs _) =
      let
        MeasureCase _ vars body = head $ filter (\(MeasureCase c _ _) -> c == ctor) defs
        sParams = map varSortName (sortArgsOf inSort) -- sort parameters in the datatype declaration
        sArgs = sortArgsOf resS -- actual sort argument in the constructor application
        body' = noncaptureSortSubstFml sParams sArgs body -- measure definition with actual sorts for all subexpressions
        newValue = fromMaybe (Cons resS ctor args) mVal
        subst = Map.fromList $ (valueVarName, newValue) : zip vars args 
       
        -- Universally quantified arguments:
        mkVar = uncurry (flip Var)
        constVars = map mkVar constArgs
        qBody = foldr All body' constVars

      in substitute subst qBody

bottomValuation :: QMap -> Formula -> Formula
bottomValuation qmap fml = applySolution bottomSolution fml
  where
    unknowns = Set.toList $ unknownsOf fml
    bottomSolution = Map.fromList $ zip (map unknownName unknowns) (map (Set.fromList . lookupQualsSubst qmap) unknowns)

-- | 'potentialVars' @qmap fml@ : variables of @fml@ if all unknowns get strongest valuation according to @quals@
potentialVars :: QMap -> Formula -> Set Id
potentialVars qmap fml = Set.map varName $ varsOf $ bottomValuation qmap fml

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: Monad s => String -> TCSolver s Id
freshId prefix = do
  i <- uses (persistentState . idCount) (Map.findWithDefault 0 prefix)
  persistentState . idCount %= Map.insert prefix (i + 1)
  return $ prefix ++ show i

-- | 'freshVersion' @prefix@ : fresh identifier starting with @prefix@, using an underscore
--    to differentiate from normal freshIds -- only used for resource constraints.
freshVersion :: Monad s => String -> TCSolver s Id
freshVersion prefix = do
  i <- uses (persistentState . versionCount) (Map.findWithDefault 0 prefix)
  persistentState . versionCount %= Map.insert prefix (i + 1)
  return $ prefix ++ "_" ++ show i


freshVar :: Monad s => Environment -> String -> TCSolver s Id
freshVar env prefix = do
  x <- freshId prefix
  if Map.member x (allSymbols env)
    then freshVar env prefix
    else return x

freshValueVarSub :: Monad s => Sort -> TCSolver s Substitution
freshValueVarSub s = Map.singleton valueVarName <$> (Var s <$> freshValueVarId)

freshValueVarId :: Monad s => TCSolver s String
freshValueVarId = freshId valueVarName

nonGhostScalars env = Map.filterWithKey (nonGhost env) $ symbolsOfArity 0 env

nonGhost env x _ = Set.notMember x (env^.ghostSymbols)

safeAddGhostVar :: Monad s => String -> RType -> Environment -> TCSolver s Environment
safeAddGhostVar name t@FunctionT{} env = return $ addGhostVariable name t env
safeAddGhostVar name t@AnyT{} env = return $ addGhostVariable name t env
safeAddGhostVar name t env = do 
  tstate <- get 
  domain <- view (resourceArgs . rSolverDomain)
  --return $ addGhostVariable name t env
  if isResourceVariable env tstate domain name t
    then do 
      persistentState . universalVars %= Set.insert name -- (Var (toSort (baseTypeOf t)) name)
      return $ addGhostVariable name t env
    else return $ addGhostVariable name t env

isResourceVariable :: Environment 
                   -> TypingState 
                   -> RDomain
                   -> String
                   -> RType 
                   -> Bool 
isResourceVariable env tstate Constant x t = False
isResourceVariable env tstate Dependent x t = 
  (x /= valueVarName) && not (Map.member x (_unresolvedConstants env))

