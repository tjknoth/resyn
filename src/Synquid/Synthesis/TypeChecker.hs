-- | Refinement type reconstruction for programs with holes
module Synquid.Synthesis.TypeChecker (
  reconstruct, 
  reconstructTopLevel
) where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Error
import Synquid.Synthesis.Explorer
import Synquid.Synthesis.Util
import Synquid.Util
import Synquid.Pretty
import Synquid.Resolver
import Synquid.Solver.Monad
import Synquid.Solver.Types
import Synquid.Solver.TypeConstraint hiding (freshId, freshVar)

import qualified Data.Map as Map
import           Data.Map (Map)
import           Control.Monad.Logic
import           Control.Monad.Reader
import           Control.Lens
import qualified Data.Set as Set

import Debug.Pretty.Simple

-- | 'reconstruct' @eParams tParams pts goal@ : reconstruct missing types and terms in the body of @goal@ so that it represents a valid type judgment;
-- return a type error if that is impossible
reconstruct :: (MonadSMT s, MonadHorn s, RMonad s) 
            => ExplorerParams 
            -> TypingParams 
            -> Maybe PersistentTState
            -> Goal 
            -> s (Either ErrorMessage [(RProgram, TypingState)])
reconstruct eParams tParams mpts goal = do
    let goal' = adjustGoalEnv goal
    initTS <- initTypingState goal' mpts
    runExplorer (eParams { _sourcePos = gSourcePos goal' }) tParams (Reconstructor reconstruct') initTS (go goal')
  where
    reconstruct' = if tParams^.(resourceArgs . enumerate) then reconstructAndCheck else reconstructTopLevel
    go g = do
      pMain <- reconstruct' g { gDepth = _auxDepth eParams }  -- Reconstruct the program
      p <- flip insertAuxSolutions pMain <$> use solvedAuxGoals      -- Insert solutions for auxiliary goals stored in @solvedAuxGoals@
      runInSolver $ finalizeProgram p                                -- Substitute all type/predicates variables and unknowns
    adjustGoalEnv goal = 
      let argmap = getAllCArgsFromSchema (gEnvironment goal) (gSpec goal)
          genv' = (gEnvironment goal) { _measureConstArgs = argmap }
      in  goal { gEnvironment = genv' }

reconstructAndCheck :: (MonadSMT s, MonadHorn s, RMonad s)
                    => Goal 
                    -> Explorer s RProgram 
reconstructAndCheck g = do
  p <- reconstructTopLevel g
  runInSolver finalSolveRCs 
  return p

reconstructTopLevel :: (MonadSMT s, MonadHorn s, RMonad s) 
                    => Goal 
                    -> Explorer s RProgram
reconstructTopLevel (Goal funName env (ForallT a sch) impl depth pos infers isolve s) = reconstructTopLevel (Goal funName (addTypeVar a env) sch impl depth pos infers isolve s)
reconstructTopLevel (Goal funName env (ForallP sig sch) impl depth pos infers isolve s) = do
  -- check if pred is resource var
  when (predSigResSort sig == IntS) $ -- add int-valued pred param as resource var 
    runInSolver $ persistentState . resourceVars %= insertRVar (predSigName sig, [])
  reconstructTopLevel (Goal funName (addBoundPredicate sig env) sch impl depth pos infers isolve s)
reconstructTopLevel (Goal funName env (Monotype typ@FunctionT{}) impl depth _ infers _ synth) = local (set (_1 . auxDepth) depth) reconstructFix
  where
    reconstructFix = do
      let typ' = renameAsImpl (isBound env) impl typ
      recCalls <- runInSolver (currentAssignment typ') >>= recursiveCalls synth
      polymorphic <- asks . view $ _1 . polyRecursion
      predPolymorphic <- asks . view $ _1 . predPolyRecursion
      let tvs = env ^. boundTypeVars
      let pvs = env ^. boundPredicates
      let predGeneralized sch = if predPolymorphic then foldr ForallP sch pvs else sch -- Version of @t'@ generalized in bound predicate variables of the enclosing function
      let typeGeneralized sch = if polymorphic then foldr ForallT sch tvs else sch -- Version of @t'@ generalized in bound type variables of the enclosing function
      let env' = foldr (\(f, t) -> addPolyVariable f (typeGeneralized . predGeneralized . Monotype $ t) . (shapeConstraints %~ Map.insert f (shape typ'))) env recCalls
      let ctx p = if null recCalls then p else Program (PFix (map fst recCalls) p) typ'
      p <- inContext ctx  $ reconstructI env' typ' impl
      return $ ctx p

    -- | 'recursiveCalls' @t@: name-type pairs for recursive calls to a function with type @t@ (0 or 1)
    recursiveCalls False t = return [(funName, t)]
    recursiveCalls _ t = do
      fixStrategy <- asks . view $ _1 . fixStrategy
      case fixStrategy of
        AllArguments -> do recType <- fst <$> recursiveTypeTuple t ffalse; if recType == t then return [] else return [(funName, recType)]
        FirstArgument -> do recType <- recursiveTypeFirst t; if recType == t then return [] else return [(funName, recType)]
        DisableFixpoint -> return []
        Nonterminating -> return [(funName, t)]

    -- | 'recursiveTypeTuple' @t fml@: type of the recursive call to a function of type @t@ when a lexicographic tuple of all recursible arguments decreases;
    -- @fml@ denotes the disjunction @x1' < x1 || ... || xk' < xk@ of strict termination conditions on all previously seen recursible arguments to be added to the type of the last recursible argument;
    -- the function returns a tuple of the weakend type @t@ and a flag that indicates if the last recursible argument has already been encountered and modified
    recursiveTypeTuple (FunctionT x tArg tRes cost) fml = 
      case terminationRefinement x tArg of
        Nothing -> do
          (tRes', seenLast) <- recursiveTypeTuple tRes fml
          return (FunctionT x tArg tRes' cost, seenLast)
        Just (argLt, argLe) -> do
          y <- runInSolver $ freshVar env "x"
          let yForVal = Map.singleton valueVarName (Var (toSort $ baseTypeOf tArg) y)
          (tRes', seenLast) <- recursiveTypeTuple (renameVar (isBound env) x y tArg tRes) (fml `orClean` substitute yForVal argLt)
          if seenLast
            then return (FunctionT y (addRefinement tArg argLe) tRes' cost, True) -- already encountered the last recursible argument: add a nonstrict termination refinement to the current one
            -- else return (FunctionT y (addRefinement tArg (fml `orClean` argLt)) tRes', True) -- this is the last recursible argument: add the disjunction of strict termination refinements
            else if fml == ffalse
                  then return (FunctionT y (addRefinement tArg argLt) tRes' cost, True)
                  else return (FunctionT y (addRefinement tArg (argLe `andClean` (fml `orClean` argLt))) tRes' cost, True) -- TODO: this version in incomplete (does not allow later tuple values to go up), but is much faster
    recursiveTypeTuple t _ = return (t, False)

    -- | 'recursiveTypeFirst' @t fml@: type of the recursive call to a function of type @t@ when only the first recursible argument decreases
    recursiveTypeFirst (FunctionT x tArg tRes cost) = 
      case terminationRefinement x tArg of
        Nothing -> (\t -> FunctionT x tArg t cost) <$> recursiveTypeFirst tRes
        Just (argLt, _) -> do
          y <- runInSolver $ freshVar env "x"
          return $ FunctionT y (addRefinement tArg argLt) (renameVar (isBound env) x y tArg tRes) cost
    recursiveTypeFirst t = return t

    -- | If argument is recursible, return its strict and non-strict termination refinements, otherwise @Nothing@
    terminationRefinement argName (ScalarT IntT fml _) = Just ( valInt |>=| IntLit 0  |&|  valInt |<| intVar argName,
                                                              valInt |>=| IntLit 0  |&|  valInt |<=| intVar argName)
    terminationRefinement argName (ScalarT dt@(DatatypeT name _ _) fml _) = case env ^. datatypes . to (Map.! name) . wfMetric of
      Nothing -> Nothing
      Just mName -> let
                      metric x = Pred IntS mName [x]
                      argSort = toSort dt
                    in Just ( metric (Var argSort valueVarName) |>=| IntLit 0  |&| metric (Var argSort valueVarName) |<| metric (Var argSort argName),
                              metric (Var argSort valueVarName) |>=| IntLit 0  |&| metric (Var argSort valueVarName) |<=| metric (Var argSort argName))
    terminationRefinement _ _ = Nothing

reconstructTopLevel (Goal _ env (Monotype t) impl depth _ _ _ _) = 
  local (set (_1 . auxDepth) depth) $ reconstructI env t impl

-- | 'reconstructI' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is a (possibly) introduction term
-- (top-down phase of bidirectional reconstruction)
reconstructI :: (MonadSMT s, MonadHorn s, RMonad s) 
             => Environment 
             -> RType 
             -> UProgram 
             -> Explorer s RProgram
reconstructI env t (Program p AnyT) = reconstructI' env t p
reconstructI env t (Program p t') = do
  t'' <- checkAnnotation env t t' p
  reconstructI' env t'' p

reconstructI' env t PErr = generateError env
reconstructI' env t PHole = generateError env `mplus` generateI env t
reconstructI' env t (PLet x iDef@(Program (PFun _ _) _) iBody) = do -- lambda-let: remember and type-check on use
  lambdaLets %= Map.insert x (env, iDef)
  let ctx p = Program (PLet x uHole p) t
  pBody <- inContext ctx $ reconstructI env t iBody
  return $ ctx pBody
--reconstructI' env t (PTick c body) = 
--  let env' = over freePotential (`subtractFormulas` IntLit c) env
--   in reconstructI env' t body
reconstructI' env t@(LetT x tDef tBody) impl = 
  reconstructI' (addVariable x tDef env) tBody impl
reconstructI' env t@(FunctionT _ tArg tRes c) impl = case impl of
  PFun y impl -> exploreFunction env (FunctionT y tArg tRes c) (\e t -> reconstructI e t impl) 
  PSymbol f -> do
    fun <- etaExpand t f
    reconstructI' env t $ content fun
  _ -> throwErrorWithDescription $ text "Cannot assign function type" </> squotes (pretty t) </>
                    text "to non-lambda term" </> squotes (pretty $ untyped impl)
reconstructI' env t@ScalarT{} impl = case impl of
  PFun _ _ -> throwErrorWithDescription $ text "Cannot assign non-function type" </> squotes (pretty t) </>
                           text "to lambda term" </> squotes (pretty $ untyped impl)

  PLet x iDef iBody -> do -- E-term let (since lambda-let was considered before)
    pDef <- inContext (\p -> Program (PLet x p (Program PHole t)) t) $ reconstructETopLevel env AnyT iDef
    let (env', tDef) = embedContext env (typeOf pDef)
    env'' <- safeAddVariable x tDef env' 
    pBody <- inContext (\p -> Program (PLet x pDef p) t) $ reconstructI env'' t iBody
    return $ Program (PLet x pDef pBody) t
   
  PIf (Program PHole AnyT) iThen iElse -> do
    (cEnv, bEnv) <- shareContext env 
    cUnknown <- Unknown Map.empty <$> runInSolver (freshId "C")
    addConstraint $ WellFormedCond bEnv cUnknown
    pThen <- inContext (\p -> Program (PIf (Program PHole boolAll) p (Program PHole t)) t) 
      $ reconstructI (addAssumption cUnknown bEnv) t iThen
    cond <- conjunction <$> currentValuation cUnknown
    pCond <- inContext (\p -> Program (PIf p uHole uHole) t) 
      $ generateConditionFromFml cEnv cond
    pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond pThen p) t) 
      $ reconstructI (addAssumption (fnot cond) bEnv) t iElse
    return $ Program (PIf pCond pThen pElse) t
  
  PIf iCond iThen iElse -> do
    (cEnv, bEnv) <- shareContext env 
    pCond <- inContext (\p -> Program (PIf p (Program PHole t) (Program PHole t)) t) 
      $ reconstructIE cEnv (ScalarT BoolT ftrue defPotential) iCond
    let (bEnv', ScalarT BoolT cond _) = embedContext bEnv $ typeOf pCond
    pThen <- inContext (\p -> Program (PIf pCond p (Program PHole t)) t) 
      $ reconstructI (addAssumption (substitute (Map.singleton valueVarName ftrue) cond) bEnv') t iThen
    pElse <- inContext (\p -> Program (PIf pCond pThen p) t) 
      $ reconstructI (addAssumption (substitute (Map.singleton valueVarName ffalse) cond) bEnv') t iElse
    return $ Program (PIf pCond pThen pElse) t

  PMatch iScr iCases -> do
    (consNames, consTypes) <- unzip <$> checkCases Nothing iCases
    let scrT = refineTop env $ shape $ lastType $ head consTypes
    (cEnv, bEnv) <- shareContext env 
    pScrutinee <- inContext (\p -> Program (PMatch p []) t) 
      $ reconstructIE cEnv scrT iScr
    let (bEnv', tScr) = embedContext bEnv (typeOf pScrutinee)
    let scrutineeSymbols = symbolList pScrutinee
    let isGoodScrutinee = not (head scrutineeSymbols `elem` consNames) &&                 -- Is not a value
                          any (not . flip Set.member (env ^. constants)) scrutineeSymbols -- Has variables (not just constants)
    unless isGoodScrutinee $ throwErrorWithDescription $ text "Match scrutinee" </> squotes (pretty pScrutinee) </> text "is constant"
    (x, bEnv'') <- addScrutineeToEnv bEnv' pScrutinee tScr
    let exploreCase = reconstructCase bEnv'' x pScrutinee t 
    pCases <- zipWithM exploreCase iCases consTypes
    return $ Program (PMatch pScrutinee pCases) t

  _ -> reconstructIE env t (untyped impl)

  where
    -- Check that all constructors are known and belong to the same datatype
    checkCases mName (Case consName args _ : cs) = case Map.lookup consName (allSymbols env) of
      Nothing -> throwErrorWithDescription $ text "Not in scope: data constructor" </> squotes (text consName)
      Just consSch -> do
                        consT <- instantiate env consSch True args -- Set argument names in constructor type to user-provided binders
                        -- let consT' = typeMultiply fzero consT
                        case lastType consT of
                          (ScalarT (DatatypeT dtName _ _) _ _) -> do
                            case mName of
                              Nothing -> return ()
                              Just name -> 
                                unless (dtName == name) $ throwErrorWithDescription $ text "Expected constructor of datatype" </> squotes (text name) </> text "and got constructor" </> squotes (text consName) </> text "of datatype" </> squotes (text dtName)
                            if arity (toMonotype consSch) /= length args
                              then throwErrorWithDescription $ text "Constructor" </> squotes (text consName)
                                            </> text "expected" </> pretty (arity (toMonotype consSch)) </> text "binder(s) and got" <+> pretty (length args)
                              else ((consName, consT) :) <$> checkCases (Just dtName) cs
                          _ -> throwErrorWithDescription $ text "Not in scope: data constructor" </> squotes (text consName)
    checkCases _ [] = return []

reconstructCase :: (MonadSMT s, MonadHorn s, RMonad s) 
                => Environment 
                -> Formula 
                -> UProgram 
                -> RType 
                -> Case RType 
                -> RType 
                -> Explorer s (Case RType)
reconstructCase env scrVar pScrutinee t c@(Case consName args iBody) consT = cut $ do
  -- matchConsType simply assigns type variables appropriately
  runInSolver $ matchConsType env (lastType consT) (typeOf pScrutinee)
  consT' <- runInSolver $ currentAssignment consT 
  (syms, ass) <- caseSymbols env scrVar args consT'
  caseEnv <- foldM (\e (x, t) -> safeAddVariable x t e) (addAssumption ass env) syms
  storeCase caseEnv c
  pCaseExpr <- local (over (_1 . matchDepth) (-1 +)) $
               inContext (\p -> Program (PMatch pScrutinee [Case consName args p]) t) $
               reconstructI caseEnv t iBody
  return $ Case consName args pCaseExpr

-- | Transition from I-terms to E-terms in reconstruction process
reconstructIE :: (MonadSMT s, MonadHorn s, RMonad s) 
              => Environment 
              -> RType 
              -> UProgram
              -> Explorer s RProgram
reconstructIE env typ p = do 
  env' <- transferPotential env 
  reconstructETopLevel env' typ p

-- | 'reconstructE' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is an elimination term
-- (bottom-up phase of bidirectional reconstruction)
reconstructETopLevel :: (MonadSMT s, MonadHorn s, RMonad s) 
                     => Environment 
                     -> RType 
                     -> UProgram 
                     -> Explorer s RProgram
reconstructETopLevel env t impl = do
  (Program pTerm pTyp) <- reconstructE env t impl
  generateAuxGoals
  pTyp' <- runInSolver $ currentAssignment pTyp
  return (Program pTerm pTyp')

reconstructE :: (MonadSMT s, MonadHorn s, RMonad s) 
             => Environment 
             -> RType 
             -> UProgram 
             -> Explorer s RProgram
reconstructE env t (Program p AnyT) = reconstructE' env t p
reconstructE env t (Program p t') = do
  t'' <- checkAnnotation env t t' p
  reconstructE' env t'' p

reconstructE' env typ PHole = do
  d <- asks . view $ _1 . eGuessDepth
  generateEUpTo env typ d

reconstructE' env typ (PSymbol name) =
  case lookupSymbol name (arity typ) (hasSet typ) env of
    Nothing -> throwErrorWithDescription $ text "Not in scope:" </> text name
    Just sch -> retrieveAndCheckVarType name sch typ env 
reconstructE' env typ (PTick c body) = 
  let env' = over freePotential (`subtractFormulas` IntLit c) env in
  do 
    pBody' <- inContext (\p -> Program (PTick c uHole) typ) $ reconstructE env' typ body
    return $ Program (PTick c pBody') (typeOf pBody') 
reconstructE' env typ p@(PApp iFun iArg) = do
  x <- runInSolver $ freshVar env "x"
  let fp = env ^. freePotential
  let cfps = env ^. condFreePotential
  --(fp', fp'') <- shareFreePotential env fp $ show $ plain $ pretty p
  --(env1, env2) <- shareContext (env { _freePotential = fp' }) $ show $ plain $ pretty p
  (env1, env2, fp'') <- shareAndExtractFP env fp cfps 
  pFun <- inContext (\p -> Program (PApp p uHole) typ) 
    $ reconstructE env1 (FunctionT x AnyT typ defCost) iFun
  let tp@(FunctionT x _ _ _) = typeOf pFun
  let (FunctionT _ tArg' tRes' _) = shiftCost tp
  pApp <- if isFunctionType tArg'
    then do -- Higher-order argument: its value is not required for the function type, enqueue an auxiliary goal
      d <- asks . view $ _1 . auxDepth
      pArg <- generateHOArg env2 (d - 1) tArg' iArg
      return (Program (PApp pFun pArg) tRes')
    else do -- First-order argument: generate now
      let tArg'' = subtractPotential tArg' fp''
      pArg <- inContext (\p -> Program (PApp pFun p) tRes') 
        $ reconstructE env2 tArg'' iArg
      let tRes'' = appType env pArg x tRes'
      return (Program (PApp pFun pArg) tRes'') 
  checkE env typ pApp
  return pApp
  where
    generateHOArg env d tArg iArg = case content iArg of
      PSymbol f -> do
        lets <- use lambdaLets
        case Map.lookup f lets of
          Nothing -> do -- This is a function from the environment, with a known type: add its eta-expansion as an aux goal
                      impl <- etaExpand tArg f
                      _ <- enqueueGoal env tArg impl d
                      return ()
          Just (env', def) -> auxGoals %= (Goal f env' (Monotype tArg) def d noPos [] False True :) -- This is a locally defined function: add an aux goal with its body
        return iArg
      _ -> enqueueGoal env tArg iArg d -- HO argument is an abstraction: enqueue a fresh goal

reconstructE' env typ impl = 
  throwErrorWithDescription $ text "Expected application term of type" </> squotes (pretty typ) </>
                                          text "and got" </> squotes (pretty $ untyped impl)

-- | 'checkAnnotation' @env t t' p@ : if user annotation @t'@ for program @p@ is a subtype of the goal type @t@,
-- return resolved @t'@, otherwise fail
checkAnnotation :: (MonadSMT s, MonadHorn s, RMonad s) 
                => Environment 
                -> RType 
                -> RType 
                -> BareProgram RType 
                -> Explorer s RType
checkAnnotation env t t' p = do
  tass <- use (typingState . typeAssignment)
  potentialSyms <- use (typingState . persistentState . resourceVars)
  case resolveRefinedType (typeSubstituteEnv tass env) t' (Set.fromList (Map.keys potentialSyms)) of
    Left err -> throwError err
    Right t'' -> do
      ctx <- asks . view $ _1 . context
      writeLog 2 $ text "Checking consistency of type annotation" <+> pretty t'' <+> text "with" <+> pretty t <+> text "in" $+$ pretty (ctx (Program p t''))
      addSubtypeConstraint env t'' t True 

      fT <- runInSolver $ finalizeType t
      fT'' <- runInSolver $ finalizeType t''
      pos <- asks . view $ _1 . sourcePos
      typingState . errorContext .= (pos, text "when checking consistency of type annotation" </> pretty fT'' </> text "with" </> pretty fT </> text "in" $+$ pretty (ctx (Program p t'')))
      runInSolver solveTypeConstraints
      typingState . errorContext .= (noPos, empty)

      tass' <- use (typingState . typeAssignment)
      return $ intersection (isBound env) t'' (typeSubstitute tass' t)

-- | 'etaExpand' @t@ @f@: for a symbol @f@ of a function type @t@, the term @\X0 . ... \XN . f X0 ... XN@ where @f@ is fully applied
etaExpand t f = do
  args <- replicateM (arity t) (runInSolver (freshId "X"))
  let body = foldl (\e1 e2 -> untyped $ PApp e1 e2) (untyped (PSymbol f)) (map (untyped . PSymbol) args)
  return $ foldr (\x p -> untyped $ PFun x p) body args

-- | 'insertAuxSolution' @pAuxs pMain@: insert solutions stored in @pAuxs@ indexed by names of auxiliary goals @x@ into @pMain@;
-- @pMain@ is assumed to contain either a "let x = ??" or "f x ...", where "x" is an auxiliary goal name
insertAuxSolutions :: Map Id RProgram -> RProgram -> RProgram
insertAuxSolutions pAuxs (Program body t) = flip Program t $
  case body of
    PLet y def p -> case Map.lookup y pAuxs of
                      Nothing -> PLet y (ins def) (ins p)
                      Just pAux -> PLet y pAux (insertAuxSolutions (Map.delete y pAuxs) p)
    PSymbol y -> case Map.lookup y pAuxs of
                    Nothing -> body
                    Just pAux -> content pAux
    PApp p1 p2 -> PApp (ins p1) (ins p2)
    PFun y p -> PFun y (ins p)
    PIf c p1 p2 -> PIf (ins c) (ins p1) (ins p2)
    PMatch s cases -> PMatch (ins s) (map (\(Case c args p) -> Case c args (ins p)) cases)
    PFix ys p -> PFix ys (ins p)
    _ -> body
  where
    ins = insertAuxSolutions pAuxs
