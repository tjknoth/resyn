{-# LANGUAGE FlexibleContexts, TupleSections #-}

-- | Generating synthesis constraints from specifications, qualifiers, and program templates
module Synquid.Synthesis.Explorer where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Error
import Synquid.Util
import Synquid.Pretty
import Synquid.Tokens
import Synquid.Solver.Monad
import Synquid.Solver.TypeConstraint
import Synquid.Synthesis.Util 

import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens


-- | 'runExplorer' @eParams tParams initTS go@ : execute exploration @go@ with explorer parameters @eParams@, typing parameters @tParams@ in typing state @initTS@
runExplorer :: (MonadSMT s, MonadHorn s) 
            => ExplorerParams 
            -> TypingParams 
            -> Reconstructor s 
            -> TypingState 
            -> Explorer s a 
            -> s (Either ErrorMessage [a])
runExplorer eParams tParams topLevel initTS go = do
  let n = _numPrograms eParams
  (ress, PersistentState errs) <- runStateT (observeManyT n (runReaderT (evalStateT go initExplorerState) (eParams, tParams, topLevel))) (PersistentState [])
  case ress of
    [] -> return $ Left $ head errs
    res -> return $ Right res--(res : _) -> return $ Right res
  where
    initExplorerState = ExplorerState initTS [] Map.empty Map.empty Map.empty Map.empty

-- | 'generateI' @env t@ : explore all terms that have refined type @t@ in environment @env@
-- (top-down phase of bidirectional typechecking)
generateI :: (MonadSMT s, MonadHorn s, RMonad s) 
          => Environment 
          -> RType 
          -> Explorer s RProgram
generateI env t@(FunctionT x tArg tRes _) = exploreFunction env t generateI 
generateI env t@ScalarT{} = do
  maEnabled <- asks . view $ _1 . abduceScrutinees -- Is match abduction enabled?
  d <- asks . view $ _1 . matchDepth
  maPossible <- runInSolver $ hasPotentialScrutinees env -- Are there any potential scrutinees in scope?
  if maEnabled && d > 0 && maPossible then generateMaybeMatchIf env t else generateMaybeIf env t

-- | Either generate lambda expression or reconstruct type of existing implementation
exploreFunction :: (MonadSMT s, MonadHorn s) 
                => Environment 
                -> RType 
                -> TypeExplorer s 
                -> Explorer s RProgram
exploreFunction env t@(FunctionT x tArg tRes _) explore = do 
  let ctx p = Program (PFun x p) t
  env' <- safeAddVariable x tArg env
  pBody <- inContext ctx $ explore (unfoldAllVariables env') tRes
  return $ ctx pBody
exploreFunction _ t _ = throwErrorWithDescription $ text "exploreFunction: called with non-function type" <+> pretty t

-- | Generate a possibly conditional term type @t@, depending on whether a condition is abduced
generateMaybeIf :: (MonadSMT s, MonadHorn s, RMonad s) 
                => Environment 
                -> RType 
                -> Explorer s RProgram
generateMaybeIf env t = ifte generateThen (uncurry6 generateElse) (generateMatch env t) -- If at least one solution without a match exists, go with it and continue with the else branch; otherwise try to match
  where
    -- | Guess an E-term and abduce a condition for it
    generateThen = do
      (cEnv, bEnv) <- shareContext env 
      cUnknown <- Unknown Map.empty <$> runInSolver (freshId "C")
      addConstraint $ WellFormedCond bEnv cUnknown
      -- Do not backtrack: if we managed to find a solution for a nonempty subset of inputs, we go with it
      pThen <- cut $ generateIE (addAssumption cUnknown bEnv) t 
      cond <- conjunction <$> currentValuation cUnknown
      return (cEnv, bEnv, t, cond, unknownName cUnknown, pThen)

-- | Proceed after solution @pThen@ has been found under assumption @cond@
generateElse :: (MonadSMT s, MonadHorn s, RMonad s) 
             => Environment 
             -> Environment 
             -> RType 
             -> Formula 
             -> Id 
             -> RProgram 
             -> Explorer s RProgram
generateElse cEnv bEnv t cond condUnknown pThen = if cond == ftrue
  then return 
  pThen -- @pThen@ is valid under no assumptions: return it
  else do -- @pThen@ is valid under a nontrivial assumption, proceed to look for the solution for the rest of the inputs
    pCond <- inContext (\p -> Program (PIf p uHole uHole) t) 
      $ generateConditionFromFml cEnv cond
    cUnknown <- Unknown Map.empty <$> runInSolver (freshId "C")
    runInSolver $ addFixedUnknown (unknownName cUnknown) (Set.singleton $ fnot cond) -- Create a fixed-valuation unknown to assume @!cond@
    pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond pThen p) t) 
      $ generateI (addAssumption cUnknown bEnv) t
    ifM (tryEliminateBranching pElse (runInSolver $ setUnknownRecheck (unknownName cUnknown) Set.empty (Set.singleton condUnknown)))
      (return pElse)
      (return $ Program (PIf pCond pThen pElse) t)

tryEliminateBranching branch recheck = 
  if isHole branch
      then return False
      else ifte -- If synthesis of the branch succeeded, try to remove the branching construct
            recheck -- Re-check Horn constraints after retracting the branch guard
            (const $ return True) -- constraints still hold: @branch@ is a valid solution overall
            (return False) -- constraints don't hold: the guard is essential 

generateConditionFromFml :: (MonadHorn s, MonadSMT s, RMonad s) 
                         => Environment 
                         -> Formula 
                         -> Explorer s RProgram
generateConditionFromFml env fml = do
  conjuncts <- genConjuncts env allConjuncts
  return $ addRef (valBool |=| fml) (foldl1 conjoin conjuncts)
  where
    addRef f (Program p t) = Program p (addRefinement t f)
    allConjuncts = Set.toList $ conjunctsOf fml
    genConjuncts env [] = return []
    genConjuncts env (c:cs) = do 
      p <- genConjunct env c
      (p :) <$> genConjuncts env cs
    genConjunct env c = if isExecutable c
                          -- TODO: this is wrong! guard's resource aren't analyzed if formula is executable 
                          then return $ fmlToProgram c
                          else cut $ generateE' env (ScalarT BoolT (valBool |=| c) defPotential) 1
    andSymb = Program (PSymbol $ binOpTokens Map.! And) (toMonotype $ binOpType And)
    conjoin p1 p2 = Program (PApp (Program (PApp andSymb p1) boolAll) p2) boolAll

-- | If partial solutions are accepted, try @gen@, and if it fails, just leave a hole of type @t@; otherwise @gen@
optionalInPartial :: (MonadSMT s, MonadHorn s, RMonad s) 
                  => RType 
                  -> Explorer s RProgram 
                  -> Explorer s RProgram
optionalInPartial t gen = ifM (asks . view $ _1 . partialSolution) (ifte gen return (return $ Program PHole t)) gen

-- | Generate a match term of type @t@
generateMatch env t = do
  d <- asks . view $ _1 . matchDepth
  if d == 0
    then mzero
    else do
      -- guard, and branch environments (if-abduction)
      (ifCEnv, ifBEnv) <- shareContext env 
      -- scrutinee, case environments (match expression)
      (matchCEnv, matchBEnv) <- shareContext ifBEnv 
      (Program p tScr) <- local (over _1 (\params -> set eGuessDepth (view scrutineeDepth params) params))
                      $ inContext (\p -> Program (PMatch p []) t)
                      $ generateIE matchCEnv anyDatatype -- Generate a scrutinee of an arbitrary type
      let (matchBEnv', tScr') = embedContext matchBEnv tScr
      let pScrutinee = Program p tScr'

      case tScr of
        (ScalarT (DatatypeT scrDT _ _) _ pot) -> do -- Type of the scrutinee is a datatype
          let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors

          let scrutineeSymbols = symbolList pScrutinee
          let isGoodScrutinee = not (null ctors) &&                                               -- Datatype is not abstract
                                (pScrutinee `notElem` (env ^. usedScrutinees)) &&              -- Hasn't been scrutinized yet
                                (head scrutineeSymbols `notElem` ctors) &&                     -- Is not a value
                                any (not . flip Set.member (env ^. constants)) scrutineeSymbols -- Has variables (not just constants)
          guard isGoodScrutinee
          (x, matchBEnv'') <- addScrutineeToEnv matchBEnv' pScrutinee tScr
          -- First case generated separately in an attempt to abduce a condition for the whole match
          (pCase, cond, condUnknown) <- cut $ generateFirstCase matchBEnv'' x pScrutinee t (head ctors)            
          -- Generate a case for each of the remaining constructors under the assumption
          pCases <- map fst <$> mapM (cut . generateCase (addAssumption cond matchBEnv'') x pScrutinee t) (tail ctors) 
          let pThen = Program (PMatch pScrutinee (pCase : pCases)) t
          generateElse ifCEnv ifBEnv t cond condUnknown pThen                                                               -- Generate the else branch

        _ -> mzero -- Type of the scrutinee is not a datatype: it cannot be used in a match

generateFirstCase env scrVar pScrutinee t consName = 
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- instantiate env consSch True []
      runInSolver $ matchConsType env (lastType consT) (typeOf pScrutinee)
      consT' <- runInSolver $ currentAssignment consT
      binders <- replicateM (arity consT') (runInSolver (freshVar env "x"))
      (syms, ass) <- caseSymbols env scrVar binders consT'
      caseEnv <- foldM (\e (x, t) -> safeAddVariable x t e) (addAssumption ass env) syms
      storeCase caseEnv (Case consName binders uHole)
      ifte  (do -- Try to find a vacuousness condition:
              deadUnknown <- Unknown Map.empty <$> runInSolver (freshId "C")
              addConstraint $ WellFormedCond env deadUnknown
              err <- inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t) $ generateError (addAssumption deadUnknown caseEnv)
              deadValuation <- conjunction <$> currentValuation deadUnknown
              ifte (generateError (addAssumption deadValuation env)) (const mzero) (return ()) -- The error must be possible only in this case
              return (err, deadValuation, unknownName deadUnknown))
            (\(err, deadCond, deadUnknown) -> return (Case consName binders err, deadCond, deadUnknown))
            (do
              pCaseExpr <- local (over (_1 . matchDepth) (-1 +))
                            $ inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t)
                            $ generateI caseEnv t
              return (Case consName binders pCaseExpr, ftrue, dontCare))

-- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
generateCase :: (MonadSMT s, MonadHorn s, RMonad s) 
             => Environment 
             -> Formula 
             -> RProgram 
             -> RType 
             -> Id 
             -> Explorer s (Case RType, Explorer s ())
generateCase env scrVar pScrutinee t consName = 
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- instantiate env consSch True []
      runInSolver $ matchConsType env (lastType consT) (typeOf pScrutinee)
      consT' <- runInSolver $ currentAssignment consT
      binders <- replicateM (arity consT') (runInSolver (freshVar env "x"))
      (syms, ass) <- caseSymbols env scrVar binders consT'
      unfoldSyms <- asks . view $ _1 . unfoldLocals

      cUnknown <- Unknown Map.empty <$> runInSolver (freshId "M")
      runInSolver $ addFixedUnknown (unknownName cUnknown) (Set.singleton ass) -- Create a fixed-valuation unknown to assume @ass@

      caseEnv <- (if unfoldSyms then unfoldAllVariables else id) <$> foldM (\e (x, t) -> safeAddVariable x t e) (addAssumption cUnknown env) syms
      storeCase caseEnv (Case consName binders uHole)
      pCaseExpr <- optionalInPartial t $ local (over (_1 . matchDepth) (-1 +))
                                       $ inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t)
                                       $ generateError caseEnv `mplus` generateI caseEnv t

      let recheck = if disjoint (symbolsOf pCaseExpr) (Set.fromList binders)
                      then runInSolver $ setUnknownRecheck (unknownName cUnknown) Set.empty Set.empty -- ToDo: provide duals here
                      else mzero
      return (Case consName binders pCaseExpr, recheck) 

-- | 'caseSymbols' @scrutinee binders consT@: a pair that contains (1) a list of bindings of @binders@ to argument types of @consT@
-- and (2) a formula that is the return type of @consT@ applied to @scrutinee@
caseSymbols env x [] (ScalarT _ fml _) = let subst = substitute (Map.singleton valueVarName x) in
  return ([], subst fml)
caseSymbols env x (name : names) (FunctionT y tArg tRes _) = do
  (syms, ass) <- caseSymbols env x names (renameVar (isBound env) y name tArg tRes)
  return ((name, tArg) : syms, ass)

-- | Generate a possibly conditional possibly match term, depending on which conditions are abduced
generateMaybeMatchIf :: (MonadSMT s, MonadHorn s, RMonad s) 
                     => Environment 
                     -> RType 
                     -> Explorer s RProgram
generateMaybeMatchIf env t = (generateOneBranch >>= generateOtherBranches) `mplus` generateMatch env t -- might need to backtrack a successful match due to match depth limitation
  where
    -- | Guess an E-term and abduce a condition and a match-condition for it
    generateOneBranch = do
      (ifCEnv, ifBEnv) <- shareContext env 
      (matchCEnv, matchBEnv) <- shareContext ifBEnv 
      -- TODO: hopefully not an issue that we use env here?
      matchUnknown <- Unknown Map.empty <$> runInSolver (freshId "M")
      addConstraint $ WellFormedMatchCond matchBEnv matchUnknown
      condUnknown <- Unknown Map.empty <$> runInSolver (freshId "C")
      addConstraint $ WellFormedCond matchBEnv condUnknown
      cut $ do
        p0 <- generateEOrError (addAssumption matchUnknown . addAssumption condUnknown $ matchBEnv) t
        matchValuation <- Set.toList <$> currentValuation matchUnknown
        let matchVars = Set.toList $ Set.unions (map varsOf matchValuation)
        condValuation <- currentValuation condUnknown
        let badError = isError p0 && length matchVars /= 1 -- null matchValuation && (not $ Set.null condValuation) -- Have we abduced a nontrivial vacuousness condition that is not a match branch?
        writeLog 3 $ text "Match valuation" <+> pretty matchValuation <+> if badError then text ": discarding error" else empty
        guard $ not badError -- Such vacuousness conditions are not productive (do not add to the environment assumptions and can be discovered over and over infinitely)
        let matchConds = map (conjunction . (\var -> filter (Set.member var . varsOf) matchValuation)) matchVars -- group by vars
        d <- asks . view $ _1 . matchDepth -- Backtrack if too many matches, maybe we can find a solution with fewer
        guard $ length matchConds <= d
        return (matchCEnv, matchBEnv, ifCEnv, ifBEnv, matchConds, conjunction condValuation, unknownName condUnknown, p0)

    generateEOrError env typ = generateError env `mplus` generateIE env typ

    -- | Proceed after solution @p0@ has been found under assumption @cond@ and match-assumption @matchCond@
    generateOtherBranches (matchCEnv, matchBEnv, ifCEnv, ifBEnv, matchConds, cond, condUnknown, p0) = do
      pThen <- cut $ generateMatchesFor matchCEnv (addAssumption cond matchBEnv) matchConds p0 t
      generateElse ifCEnv ifBEnv t cond condUnknown pThen

    -- TODO: do the constraints generated by the scrutinee (which is only a variable)
    --   matter? should they?

    generateMatchesFor matchCEnv matchBEnv [] pBaseCase t = return pBaseCase
    generateMatchesFor matchCEnv matchBEnv (matchCond : rest) pBaseCase t = do
      let (Binary Eq matchVar@(Var _ x) (Cons _ c _)) = matchCond
      scrT <- runInSolver $ currentAssignment (toMonotype $ symbolsOfArity 0 env Map.! x)
      let (ScalarT (DatatypeT scrDT _ _) _ _)  = scrT
      let pScrutinee = Program (PSymbol x) scrT
      let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors
      let matchBEnv' = addScrutinee pScrutinee matchBEnv
      storeCase matchBEnv' $ Case c [] uHole
      pBaseCase' <- cut $ inContext (\p -> Program (PMatch pScrutinee [Case c [] p]) t) 
                            $ generateMatchesFor matchCEnv (addAssumption matchCond matchBEnv') rest pBaseCase t
      return $ Case c [] pBaseCase

      let genOtherCases previousCases ctors =
            case ctors of
              [] -> return $ Program (PMatch pScrutinee previousCases) t
              (ctor:rest) -> do
                (c, recheck) <- cut 
                  $ generateCase matchBEnv' matchVar pScrutinee t ctor
                ifM (tryEliminateBranching (expr c) recheck)
                  (return $ expr c)
                  (genOtherCases (previousCases ++ [c]) rest)

      genOtherCases [Case c [] pBaseCase] (delete c ctors)

-- | Transition from I-terms to E-terms
generateIE :: (MonadSMT s, MonadHorn s, RMonad s) 
           => Environment 
           -> RType 
           -> Explorer s RProgram
generateIE env typ = do 
  env' <- transferPotential env 
  generateE env' typ 

-- | 'generateE' @env typ@ : explore all elimination terms of type @typ@ in environment @env@
-- (bottom-up phase of bidirectional typechecking)
generateE :: (MonadSMT s, MonadHorn s, RMonad s) 
          => Environment 
          -> RType 
          -> Explorer s RProgram
generateE env typ = do
  d <- asks . view $ _1 . eGuessDepth
  generateE' env typ d

generateE' env typ d = do
  (Program pTerm pTyp) <- generateEUpTo env typ d                      -- Generate the E-term
  runInSolver $ isFinal .= True 
             >> solveTypeConstraints 
             >> isFinal .= False  -- Final type checking pass that eliminates all free type variables
  newGoals <- uses auxGoals (map gName)                                      -- Remember unsolved auxiliary goals
  generateAuxGoals                                                           -- Solve auxiliary goals
  pTyp' <- runInSolver $ currentAssignment pTyp                              -- Finalize the type of the synthesized term
  addLambdaLets pTyp' (Program pTerm pTyp') newGoals                   -- Check if some of the auxiliary goal solutions are large and have to be lifted into lambda-lets
  where
    addLambdaLets t body [] = return body
    addLambdaLets t body (g:gs) = do
      pAux <- uses solvedAuxGoals (Map.! g)
      if programNodeCount pAux > 5
        then addLambdaLets t (Program (PLet g uHole body) t) gs
        else addLambdaLets t body gs

-- | 'generateEUpTo' @env typ d@ : explore all applications of type shape @shape typ@ in environment @env@ of depth up to @d@
generateEUpTo :: (MonadSMT s, MonadHorn s, RMonad s) 
              => Environment 
              -> RType 
              -> Int 
              -> Explorer s RProgram
generateEUpTo env typ d = msum $ map (enumerateAt env typ) [0..d]

-- | Perform a gradual check that @p@ has type @typ@ in @env@:
-- if @p@ is a scalar, perform a full subtyping check;
-- if @p@ is a (partially applied) function, check as much as possible with unknown arguments
checkE :: (MonadSMT s, MonadHorn s, RMonad s) 
       => Environment 
       -> RType 
       -> RProgram 
       -> Explorer s ()
checkE env typ p@(Program pTerm pTyp) = do
  ctx <- asks . view $ _1 . context
  writeLog 1 $ linebreak <+> linebreak <+> special "Checking" <+> pretty p <+> text "::" <+> pretty typ <+> text "in" $+$ pretty (ctx (untyped PHole))
  writeLog 3 $ text "from env with top-level potentials:" <+> prettyScalarTypes (env^.symbols) <+> pretty (_freePotential env)

  -- ifM (asks $ _symmetryReduction . fst) checkSymmetry (return ())

  incremental <- asks . view $ _1 . incrementalChecking -- Is incremental type checking of E-terms enabled?
  consistency <- asks . view $ _1 . consistencyChecking -- Is consistency checking enabled?
  
  -- Add subtyping check, unless it's a function type and incremental checking is diasbled:
  when (incremental || arity typ == 0)
    $ addSubtypeConstraint env pTyp typ False 

  -- Add consistency constraint for function types:
  when (consistency && arity typ > 0) 
    (addSubtypeConstraint env pTyp typ True)
  fTyp <- runInSolver $ finalizeType typ
  pos <- asks . view $ _1 . sourcePos
  typingState . errorContext .= (pos, text "when checking" </> pretty p </> text "::" </> pretty fTyp </> text "in" $+$ pretty (ctx p))
  runInSolver solveTypeConstraints
  typingState . errorContext .= (noPos, empty)
  

enumerateAt :: (MonadSMT s, MonadHorn s, RMonad s) 
            => Environment 
            -> RType 
            -> Int
            -> Explorer s RProgram
enumerateAt env typ 0 = do
    let symbols = Map.toList $ symbolsOfArity (arity typ) env
    useCounts <- use symbolUseCount
    -- Filter set constructors out of symbols for enumeration 
    let symbols' = filter (\(x, _) -> x `notElem` setConstructors) $ if arity typ == 0
        then sortBy (mappedCompare (\(x, _) -> (Set.member x (env ^. constants), Map.findWithDefault 0 x useCounts))) symbols
         else sortBy (mappedCompare (\(x, _) -> (not $ Set.member x (env ^. constants), Map.findWithDefault 0 x useCounts))) symbols
    msum $ map pickSymbol symbols'
  where
    pickSymbol (name, sch) = do
      when (Set.member name (env ^. letBound)) mzero
      p <- retrieveAndCheckVarType name sch typ env
      writeLog 1 $ linebreak $+$ text "Trying" <+> pretty p 
      return p

enumerateAt env typ d = do
  let maxArity = fst $ Map.findMax (env ^. symbols)
  guard $ arity typ < maxArity
  generateAllApps
  where
    generateAllApps =
      generateApp (\e t -> generateEUpTo e t (d - 1)) (\e t -> enumerateAt e t (d - 1)) `mplus`
        generateApp (\e t -> enumerateAt e t d) (\e t -> generateEUpTo e t (d - 1))

    generateApp genFun genArg = do
      x <- runInSolver $ freshId "X"
      let fp = env ^. freePotential 
      let cfps = env ^. condFreePotential 
      --(fp', fp'') <- shareFreePotential env fp $ show $ text "genApp ::" <+> plain (pretty typ)
      --(env1, env2) <- shareContext (env { _freePotential = fp' }) $ show $ text "genApp ::" <+> plain (pretty typ)
      (env1, env2, fp'') <- shareAndExtractFP env fp cfps 
      fun <- inContext (\p -> Program (PApp p uHole) typ)
             $ genFun env1 (FunctionT x AnyT typ defCost) -- Find all functions that unify with (? -> typ)
      let tp@(FunctionT x _ _ _) = typeOf fun
      let (FunctionT _ tArg' tRes' _) = shiftCost tp
      pApp <- if isFunctionType tArg'
        then do -- Higher-order argument: its value is not required for the function type, return a placeholder and enqueue an auxiliary goal
          d <- asks . view $ _1 . auxDepth
          when (d <= 0) $ writeLog 2 (text "Cannot synthesize higher-order argument: no auxiliary functions allowed") >> mzero
          arg <- enqueueGoal env2 tArg' (untyped PHole) (d - 1)
          return (Program (PApp fun arg) tRes')
        else do -- First-order argument: generate now
          let mbCut = id -- if Set.member x (varsOfType tRes) then id else cut
          let tArg'' = subtractPotential tArg' fp''
          arg <- local (over (_1 . eGuessDepth) (-1 +))
                 $ inContext (\p -> Program (PApp fun p) tRes')
                 $ mbCut (genArg env2 tArg'')
          writeLog 3 (text "Synthesized argument" <+> pretty arg <+> text "of type" <+> pretty (typeOf arg))
          let tRes'' = appType env arg x tRes'
          return (Program (PApp fun arg) tRes'') 
      checkE env typ pApp
      return pApp

-- | Given a name, schema, and environment, retrieve the variable type from the environment and check against the provided goal type 
retrieveAndCheckVarType :: (MonadHorn s, MonadSMT s, RMonad s) 
                        => Id 
                        -> RSchema 
                        -> RType
                        -> Environment 
                        -> Explorer s RProgram
retrieveAndCheckVarType name sch typ env = do 
  let (isVariable, tempenv) = removeSymbol name env
  let env' = if isVariable 
      then addPolyVariable name (schemaMultiply fzero sch) tempenv 
      else env
  t <- symbolType env name sch
  symbolUseCount %= Map.insertWith (+) name 1
  case Map.lookup name (env ^. shapeConstraints) of
    Nothing -> return ()
    Just sc -> addSubtypeConstraint env (refineBot env $ shape t) (refineTop env sc) False 
  let p = Program (PSymbol name) t
  checkE env' typ p
  addCTConstraint env'
  return p

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
      (typingState . candidates) .= cands'
      return $ val (head cands')



-- | Make environment inconsistent (if possible with current unknown assumptions)
generateError :: (MonadSMT s, MonadHorn s, RMonad s) 
              => Environment 
              -> Explorer s RProgram
generateError env = do
  ctx <- asks . view $ _1. context
  writeLog 1 $ text "Checking" <+> pretty (show errorProgram) <+> text "in" $+$ pretty (ctx errorProgram)
  tass <- use (typingState . typeAssignment)
  let env' = typeSubstituteEnv tass env
  addSubtypeConstraint env (int $ conjunction $ map trivial (allScalars env')) (int ffalse) False 
  pos <- asks . view $ _1 . sourcePos
  typingState . errorContext .= (pos, text "when checking" </> pretty errorProgram </> text "in" $+$ pretty (ctx errorProgram))
  runInSolver solveTypeConstraints 
  typingState . errorContext .= (noPos, empty)
  return errorProgram
  where
    trivial var = var |=| var

-- | 'appType' @env p x tRes@: a type semantically equivalent to [p/x]tRes;
-- if @p@ is not a variable, instead of a literal substitution use the contextual type LET x : (typeOf p) IN tRes
appType :: Environment -> RProgram -> Id -> RType -> RType
appType env (Program (PSymbol name) t) x tRes = substituteInType (isBound env) (Map.singleton x $ symbolAsFormula env name t) tRes
appType env (Program _ t) x tRes = contextual x (typeMultiply fzero t) tRes

isPolyConstructor (Program (PSymbol name) t) = isTypeName name && (not . Set.null . typeVarsOf $ t)

enqueueGoal env typ impl depth = do
  g <- runInSolver $ freshVar env "f"
  auxGoals %= (Goal g env (Monotype typ) impl depth noPos [] False True :)
  return $ Program (PSymbol g) typ
