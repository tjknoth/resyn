{-# LANGUAGE FlexibleContexts #-}

-- | Incremental solving of subtyping and well-formedness constraints
module Synquid.Solver.TypeConstraint (
  ErrorMessage,
  typingConstraints,
  typeAssignment,
  qualifierMap,
  candidates,
  errorContext,
  addFixedUnknown,
  setUnknownRecheck,
  simplifyAllConstraints,
  solveAllCandidates,
  matchConsType,
  hasPotentialScrutinees,
  currentAssignment,
  finalizeType,
  finalizeProgram,
  allScalars,
  processAllConstraints,
  generateAllHornClauses,
  processAllPredicates,
  checkTypeConsistency,
  solveTypeConstraints,
  finalSolveRCs,
  initTypingState
) where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.Util
import Synquid.Resolver (addAllVariables)
import Synquid.Synthesis.Util hiding (throwError, writeLog)
import Synquid.Solver.Monad
import Synquid.Solver.Resource
import Synquid.Solver.Types
import Synquid.Solver.CEGIS (initCEGISState)

import           Data.Maybe
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Map.Ordered as OMap
import           Data.Map.Ordered (OMap)
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Except (throwE)
import           Control.Lens hiding (both)
import           Debug.Trace

import Debug.Pretty.Simple

-- | Initial typing state in the initial environment @env@ given @goal@
initTypingState :: MonadHorn s => Goal -> Maybe PersistentTState -> s TypingState
initTypingState goal mpts = do
  let env = gEnvironment goal
  initCand <- initHornSolver env
  -- If we're doing inference, our initial typing state has to contain
  -- the resource vars that we'll later use for inference.
  let rvars = gInferredPotlVars goal
  -- let dpts = PersistentTState {
  --   _idCount = Map.empty,
  --   _resourceConstraints = [],
  --   _resourceVars = Map.fromList [(p, []) | p <- rvars],
  --   _inferredRVars = OMap.fromList [(p, Nothing) | p <- rvars],
  --   }

  let dpts = PersistentTState {
    _idCount = Map.empty,
    _versionCount = Map.empty,
    _resourceConstraints = [],
    _resourceVars = Map.fromList [(p, []) | p <- rvars],
    _inferredRVars = OMap.fromList [(p, Nothing) | p <- rvars],
    _universalVars = initialFormulas env, 
    _universalMeasures = Set.empty
  }

  let pts = maybe dpts id mpts

  return TypingState {
    _persistentState = pts,
    _typingConstraints = [],
    _typeAssignment = Map.empty,
    _predAssignment = Map.empty,
    _qualifierMap = Map.empty,
    _candidates = [initCand],
    _initEnv = env,
    _isFinal = False,
    _matchCases = Set.empty,
    _cegisState = initCEGISState,
    _solveResConstraints = OMap.null (_inferredRVars pts) || gInferSolve goal,
    _simpleConstraints = [],
    _hornClauses = [],
    _consistencyChecks = [],
    _errorContext = (noPos, empty)
  }

-- Sorta hacky to make sure we look at _v as well as other relevant universally quantified
--   expressions
initialFormulas :: Environment -> Set Id
initialFormulas = {- Set.insert valueVarName . -} Set.fromList . Map.keys . nonGhostScalars -- . Map.mapWithKey toFml . nonGhostScalars 

{- Top-level constraint solving interface -}

-- | Solve @typingConstraints@: either strengthen the current candidates and return shapeless type constraints or fail
solveTypeConstraints :: (MonadSMT s, MonadHorn s, RMonad s) => TCSolver s ()
solveTypeConstraints = do

  simplifyAllConstraints
  processAllPredicates
  processAllConstraints

  scs <- use simpleConstraints
  writeLog 2 $ nest 4 $ text "Simple Constraints" $+$ vsep (map pretty (filter printable scs))

  generateAllHornClauses

  solveHornClauses
  checkTypeConsistency

  res <- view (resourceArgs . shouldCheckResources) 
  eac <- view (resourceArgs . enumerate) 
  solve <- use solveResConstraints
  when res $
    if eac || not solve
      then processRCs scs
      else checkResources scs 

  hornClauses .= []
  consistencyChecks .= []

-- Solve resource constraints on final pass of enumerate-and-check algorithm
finalSolveRCs :: (MonadSMT s, MonadHorn s, RMonad s) => TCSolver s ()
finalSolveRCs = do
  res <- view (resourceArgs . shouldCheckResources) 
  solve <- use solveResConstraints
  when (res && solve) $
    checkResources [SharedForm emptyEnv fzero fzero fzero]

{- Implementation -}

-- | Decompose and unify typing constraints;
-- return shapeless type constraints: constraints involving only free type variables, which impose no restrictions yet, but might in the future
simplifyAllConstraints :: MonadHorn s => TCSolver s ()
simplifyAllConstraints = do
  tcs <- use typingConstraints
  writeLog 3 $ nest 4 $ text "Typing Constraints" $+$ vsep (map pretty (filter printable tcs))
  typingConstraints .= []
  tass <- use typeAssignment
  mapM_ simplifyConstraint tcs

  -- If type assignment has changed, we might be able to process more shapeless constraints:
  tass' <- use typeAssignment
  writeLog 2 $ nest 2 $ text "Type assignment" $+$ vMapDoc text pretty tass'

  when (Map.size tass' > Map.size tass) simplifyAllConstraints

-- | Assign unknowns to all free predicate variables
processAllPredicates :: MonadHorn s => TCSolver s ()
processAllPredicates = do
  tcs <- use typingConstraints
  typingConstraints .= []
  mapM_ processPredicate tcs

  pass <- use predAssignment
  writeLog 3 (nest 2 $ text "Pred assignment" $+$ vMapDoc text pretty pass)

-- | Eliminate type and predicate variables, generate qualifier maps
processAllConstraints :: MonadHorn s => TCSolver s ()
processAllConstraints = do
  tcs <- use simpleConstraints
  simpleConstraints .= []
  mapM_ processConstraint tcs

-- | Convert simple subtyping constraints into horn clauses
generateAllHornClauses :: (MonadHorn s, MonadSMT s) => TCSolver s ()
generateAllHornClauses = do
  tcs <- use simpleConstraints
  simpleConstraints .= []
  mapM_ generateHornClauses tcs

-- | Refine the current liquid assignments using the horn clauses
solveHornClauses :: MonadHorn s => TCSolver s ()
solveHornClauses = do
  clauses <- use hornClauses
  qmap <- use qualifierMap
  cands <- use candidates
  env <- use initEnv
  cands' <- lift . lift . lift $ refineCandidates clauses qmap (instantiateConsAxioms env False Nothing) cands

  when (null cands') (throwError $ text "Cannot find sufficiently strong refinements")
  candidates .= cands'

solveAllCandidates :: MonadHorn s => TCSolver s ()
solveAllCandidates = do
  cands <- use candidates
  cands' <- concat <$> mapM solveCandidate cands
  candidates .= cands'
  where
    solveCandidate c@(Candidate s valids invalids _) =
      if Set.null invalids
        then return [c]
        else do
          qmap <- use qualifierMap
          env <- use initEnv
          cands' <- lift . lift . lift $ refineCandidates [] qmap (instantiateConsAxioms env False Nothing) [c]
          concat <$> mapM solveCandidate cands'

-- | Filter out liquid assignments that are too strong for current consistency checks
checkTypeConsistency :: MonadHorn s => TCSolver s ()
checkTypeConsistency = do
  clauses <- use consistencyChecks
  cands <- use candidates
  env <- use initEnv
  cands' <- lift . lift . lift $ checkCandidates True clauses (instantiateConsAxioms env False Nothing) cands
  when (null cands') (throwError $ text "Found inconsistent refinements")
  candidates .= cands'

addRSubConstraint :: Monad s => Environment -> RType -> RType -> TCSolver s ()
addRSubConstraint env tl@(ScalarT _ rl pl) (ScalarT _ rr pr)
  | rl == ffalse = return ()
  | pr == fzero  = return () -- subsumed by well-formedness
  | otherwise    = simpleConstraints %= (RSubtype (addVariable valueVarName tl env) pl pr :)

-- | Simplify @c@ into a set of simple and shapeless constraints, possibly extended the current type assignment or predicate assignment
simplifyConstraint :: MonadHorn s => Constraint -> TCSolver s ()
simplifyConstraint c = do
  tass <- use typeAssignment
  pass <- use predAssignment
  simplifyConstraint' tass pass c

simplifyConstraint' _ _ c@WellFormedPotential{} = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@RSubtype{} = simpleConstraints %= (c :)
-- Any type: drop
simplifyConstraint' _ _ (Subtype _ _ AnyT _) = return ()
simplifyConstraint' _ _ (Subtype _ AnyT _ _) = return ()
simplifyConstraint' _ _ (WellFormed _ AnyT) = return ()
-- Any datatype: drop only if lhs is a datatype
simplifyConstraint' _ _ (Subtype _ (ScalarT (DatatypeT _ _ _) _ _) t _) | t == anyDatatype = return ()
-- Well-formedness of a known predicate drop
simplifyConstraint' _ pass c@(WellFormedPredicate _ _ _ p) | p `Map.member` pass = return () 

{-
simplifyConstraint' _ _ (Subtype env tl@(ScalarT bl@(TypeVarT _ a ml) rl pl) tr@(ScalarT br@(TypeVarT _ b mr) rr pr) False)
  | isBound env a && isBound env b -- && pr /= fzero
    = do 
        simpleConstraints %= (RSubtype (addVariable valueVarName tl env) ml mr :)
        addRSubConstraint env tl tr
        simplifyConstraint (Subtype env (ScalarT bl rl fzero) (ScalarT br rr fzero) False)
-}
-- Data types: if necessary, generate rsub constraint over top-level potentials before decomposing
simplifyConstraint' _ _ (Subtype env tl@(ScalarT bl@DatatypeT{} rl pl) tr@(ScalarT br@DatatypeT{} rr pr) False)
  | pr /= fzero
    = do
        addRSubConstraint env tl tr
        simplifyConstraint (Subtype env (ScalarT bl rl fzero) (ScalarT br rr fzero) False)
{-
-- Bools
simplifyConstraint' _ _ (Subtype env tl@(ScalarT BoolT rl pl) tr@(ScalarT BoolT rr pr) False)
  | pr /= fzero
    = do
        addRSubConstraint env tl tr
        simplifyConstraint (Subtype env (ScalarT BoolT rl fzero) (ScalarT BoolT rr fzero) False)
-- Ints
simplifyConstraint' _ _ (Subtype env tl@(ScalarT IntT rl pl) tr@(ScalarT IntT rr pr) False)
  | pr /= fzero
    = do
        addRSubConstraint env tl tr
        simplifyConstraint (Subtype env (ScalarT IntT rl fzero) (ScalarT IntT rr fzero) False)
-}
-- Type variable with known assignment: substitute
simplifyConstraint' tass _ (Subtype env tv@(ScalarT (TypeVarT _ a _) _ p) t variant)
  | a `Map.member` tass
  = simplifyConstraint (Subtype env (typeSubstitute tass tv) t variant)
simplifyConstraint' tass _ (Subtype env t tv@(ScalarT (TypeVarT _ a _) _ p) variant)
  | a `Map.member` tass
  = simplifyConstraint (Subtype env t (typeSubstitute tass tv) variant)
simplifyConstraint' tass _ (WellFormed env tv@(ScalarT (TypeVarT _ a _) _ _))
  | a `Map.member` tass
  = simplifyConstraint (WellFormed env (typeSubstitute tass tv))

-- Don't process yet, wait until type assignment is finalized
simplifyConstraint' tass _ c@SharedEnv{} =
  simpleConstraints %= (c :)
simplifyConstraint' tass _ c@ConstantRes{} =
  simpleConstraints %= (c :)
simplifyConstraint' tass _ c@Transfer{} =
  simpleConstraints %= (c :)

-- Two unknown free variables: nothing can be done for now
simplifyConstraint' _ _ c@(Subtype env (ScalarT (TypeVarT _ a _) _ _) (ScalarT (TypeVarT _ b _) _ _) _) | not (isBound env a) && not (isBound env b)
  = if a == b
      then error $ show $ text "simplifyConstraint: equal type variables on both sides"
      else ifM (use isFinal)
            (do -- This is a final pass: assign an arbitrary type to one of the variables
              addTypeAssignment a intAll
              simplifyConstraint c)
            (modify $ addTypingConstraint c)
simplifyConstraint' _ _ c@(WellFormed env (ScalarT (TypeVarT _ a _) _ _)) | not (isBound env a) =
  modify $ addTypingConstraint c
simplifyConstraint' _ _ c@WellFormedPredicate{} =
  modify $ addTypingConstraint c

-- Let types: extend environment (has to be done before trying to extend the type assignment)
simplifyConstraint' _ _ (Subtype env (LetT x tDef tBody) t variant)
  = do
      env' <- safeAddGhostVar x tDef env
      simplifyConstraint (Subtype env' tBody t variant) -- ToDo: make x unique?
simplifyConstraint' _ _ (Subtype env t (LetT x tDef tBody) variant)
  = do
      env' <- safeAddGhostVar x tDef env
      simplifyConstraint (Subtype env' t tBody variant) -- ToDo: make x unique?

-- Unknown free variable and a type: extend type assignment
simplifyConstraint' _ _ c@(Subtype env (ScalarT (TypeVarT _ a _) _ _) t _) | not (isBound env a)
  = unify env a t >> simplifyConstraint c
simplifyConstraint' _ _ c@(Subtype env t (ScalarT (TypeVarT _ a _) _ _) _) | not (isBound env a)
  = unify env a t >> simplifyConstraint c

-- Compound types: decompose
simplifyConstraint' _ _ (Subtype env (ScalarT (DatatypeT name (tArg:tArgs) pArgs) fml pot) (ScalarT (DatatypeT name' (tArg':tArgs') pArgs') fml' pot') consistency)
  = do
      simplifyConstraint (Subtype env tArg tArg' consistency)
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name tArgs pArgs) fml pot) (ScalarT (DatatypeT name' tArgs' pArgs') fml' pot') consistency)

simplifyConstraint' _ _ (Subtype env t@(ScalarT (DatatypeT name [] (pArg:pArgs)) fml pot) (ScalarT (DatatypeT name' [] (pArg':pArgs')) fml' pot') consistency)
  = do
      let variances = _predVariances ((env ^. datatypes) Map.! name)
      let isContra = variances !! (length variances - length pArgs - 1) -- Is pArg contravariant?
-- This is a bad condition! Need to get return val of actual pred
      if sortOf pArg == BoolS
      -- if (predSigResSort . head . _predParams $ (env ^. datatypes) Map.! name) == BoolS
        then if isContra
          then simplifyConstraint (Subtype env (int pArg') (int pArg) consistency)
          else simplifyConstraint (Subtype env (int pArg) (int pArg') consistency)
        else simpleConstraints %= (RSubtype env pArg pArg' :) 
          -- do
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name [] pArgs) fml pot) (ScalarT (DatatypeT name' [] pArgs') fml' pot') consistency)
simplifyConstraint' _ _ (Subtype env (FunctionT x tArg1 tRes1 _) (FunctionT y tArg2 tRes2 _) True)
  = if isScalarType tArg1
      then do
        env' <- safeAddGhostVar x tArg1 env
        simplifyConstraint (Subtype env' tRes1 tRes2 True)
      else simplifyConstraint (Subtype env tRes1 tRes2 True)
simplifyConstraint' _ _ (Subtype env (FunctionT x tArg1 tRes1 _) (FunctionT y tArg2 tRes2 _) consistency)
  = do
      -- simplifyConstraint (Subtype env (removePotential tArg2) (removePotential tArg1) consistency)
      simplifyConstraint (Subtype env tArg2 tArg1 consistency)
      if isScalarType tArg1
        then do
          env' <- safeAddGhostVar y tArg2 env
          -- simplifyConstraint (Subtype env' (renameVar (isBound env) x y tArg1 (removePotential tRes1)) (removePotential tRes2) consistency)
          simplifyConstraint (Subtype env' (renameVar (isBound env) x y tArg1 tRes1) tRes2 consistency)
        else simplifyConstraint (Subtype env tRes1 tRes2 consistency)
simplifyConstraint' _ _ c@(WellFormed env (ScalarT (DatatypeT name tArgs _) fml pot))
  = do
      mapM_ (simplifyConstraint . (\t -> WellFormed env t)) tArgs
      simpleConstraints %= (c :)
simplifyConstraint' _ _ (WellFormed env (FunctionT x tArg tRes _))
  = do
      simplifyConstraint (WellFormed env tArg)
      env' <- safeAddGhostVar x tArg env
      simplifyConstraint (WellFormed env' tRes)
simplifyConstraint' _ _ (WellFormed env (LetT x tDef tBody))
  = do
      env' <- safeAddGhostVar x tDef env
      simplifyConstraint (WellFormed env' tBody)

-- Simple constraint: return
simplifyConstraint' _ _ c@(Subtype env tl@(ScalarT bl@(TypeVarT s x m) _ _) tr@(ScalarT br@(TypeVarT s' x' m') _ _) _)
  | equalShape bl br = do
      addRSubConstraint env tl tr -- generate rsub constraint
      -- generate multiplicity constraint
      simpleConstraints %= (RSubtype env m m' :)
      simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(Subtype env tl@(ScalarT baseT _ _) tr@(ScalarT baseT' _ _) _)
  | equalShape baseT baseT' = do
      addRSubConstraint env tl tr -- generate rsub constraint
      simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormed _ (ScalarT baseT _ _)) = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormedCond _ _) = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormedMatchCond _ _) = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@SharedForm{} = simpleConstraints %= (c :)
-- Otherwise (shape mismatch): fail
simplifyConstraint' _ _ (Subtype _ t t' _) =
  throwError $ text  "Cannot match shape" <+> squotes (pretty $ shape t) $+$ text "with shape" <+> squotes (pretty $ shape t')


-- | Unify type variable @a@ with type @t@ or fail if @a@ occurs in @t@
unify env a t = if a `Set.member` typeVarsOf t
  then error $ show $ text "simplifyConstraint: type variable occurs in the other type"
  else do
    t' <- fresh env t
    writeLog 3 (text "UNIFY" <+> text a <+> text "WITH" <+> pretty t <+> text "PRODUCING" <+> pretty t')
    addTypeAssignment a t'

-- Predicate well-formedness: shapeless or simple depending on type variables
{-processPredicate c@(WellFormedPredicate env argSorts p) = do -- APs: split case into BoolS, IntS return types
  tass <- use typeAssignment
  let typeVars = Set.toList $ Set.unions $ map typeVarsOfSort argSorts
  if any (isFreeVariable tass) typeVars
    then do
      writeLog 3 $ text "WARNING: free vars in predicate" <+> pretty c
      modify $ addTypingConstraint c -- Still has type variables: cannot determine shape
    else do
      -- u <- freshId "U"
      let u = p
      addPredAssignment p (Unknown Map.empty u)
      let argSorts' = map (sortSubstitute $ asSortSubst tass) argSorts
      let args = zipWith Var argSorts' deBrujns
      let env' = typeSubstituteEnv tass env
      let vars = allScalars env'
      pq <- asks _predQualsGen
      addQuals u (pq (addAllVariables args env') args vars)
  where
    isFreeVariable tass a = not (isBound env a) && not (Map.member a tass)
-}
processPredicate c@(WellFormedPredicate env argSorts BoolS p) = do
  tass <- use typeAssignment
  let typeVars = Set.toList $ Set.unions $ map typeVarsOfSort argSorts
  if any (isFreeVariable tass) typeVars
    then do
      writeLog 3 $ text "WARNING: free vars in predicate" <+> pretty c
      modify $ addTypingConstraint c -- Still has type variables: cannot determine shape
    else do
      -- u <- freshId "U"
      let u = p
      addPredAssignment p (Unknown Map.empty u)
      let argSorts' = map (sortSubstitute $ asSortSubst tass) argSorts
      let args = zipWith Var argSorts' deBrujns
      let env' = typeSubstituteEnv tass env
      let vars = allScalars env'
      pq <- asks _predQualsGen
      addQuals u (pq (addAllVariables args env') args vars)
  where
    isFreeVariable tass a = not (isBound env a) && not (Map.member a tass)
processPredicate (WellFormedPredicate env _ IntS p) = do
  persistentState . resourceVars %= insertRVar (p, [])
  return ()
processPredicate c = modify $ addTypingConstraint c

-- | Eliminate type and predicate variables from simple constraints, create qualifier maps, split measure-based subtyping constraints
processConstraint :: MonadHorn s => Constraint -> TCSolver s ()
processConstraint (Subtype env (ScalarT baseTL l potl) (ScalarT baseTR r potr) True) | equalShape baseTL baseTR
  = do
      tass <- use typeAssignment
      pass <- use predAssignment
      let subst = sortSubstituteFml (asSortSubst tass) . substitutePredicate pass
      let l' = subst l
      let r' = subst r
      let potl' = subst potl
      let potr' = subst potr
      unless (l' == ftrue || r' == ftrue) $ simpleConstraints %= (Subtype env (ScalarT baseTL l' potl') (ScalarT baseTR r' potr') True :)

processConstraint c@(Subtype env (ScalarT baseTL l potl) (ScalarT baseTR r potr) consistency) | equalShape baseTL baseTR
  = if l == ffalse || r == ftrue
      then do
        -- Implication on refinements is trivially true, add constraint with trivial refinements for resource analysis
        --let c' = Subtype env (ScalarT baseTL ffalse potl) (ScalarT baseTR r potr) consistency
        --simpleConstraints %= (c': )
        return ()
      else do
        tass <- use typeAssignment
        pass <- use predAssignment
        let subst = sortSubstituteFml (asSortSubst tass) . substitutePredicate pass
        let l' = subst l
        let r' = subst r
        let potl' = subst potl
        let potr' = subst potr
        let c' = Subtype env (ScalarT baseTL l' potl') (ScalarT baseTR r' potr') consistency
        if Set.null $ (predsOf l' `Set.union` predsOf r') Set.\\ Map.keysSet (allPredicates env)
            then case baseTL of -- Subtyping of datatypes: try splitting into individual constraints between measures
                  DatatypeT dtName _ _ -> do
                    let measures = Map.keysSet $ allMeasuresOf dtName env
                    let isAbstract = null $ ((env ^. datatypes) Map.! dtName) ^. constructors
                    let vals = filter (\v -> varName v == valueVarName) . Set.toList . varsOf $ r'
                    let rConjuncts = conjunctsOf r'
                    doSplit <- asks _tcSolverSplitMeasures
                    if not doSplit || isAbstract || null vals || (not . Set.null . unknownsOf) (l' |&| r') -- TODO: unknowns can be split if we know their potential valuations
                      then simpleConstraints %= (c' :) -- Constraint has unknowns (or RHS doesn't contain _v)
                      else case splitByPredicate measures (head vals) (Set.toList rConjuncts) of
                            Nothing -> simpleConstraints %= (c' :) -- RHS cannot be split, add whole thing
                            Just mr -> if rConjuncts `Set.isSubsetOf` Set.unions (Map.elems mr)
                                        then do
                                          let lConjuncts = conjunctsOf $ instantiateCons (head vals) l'
                                          case splitByPredicate measures (head vals) (Set.toList lConjuncts) of -- Every conjunct of RHS is about some `m _v` (where m in measures)
                                              Nothing -> simpleConstraints %= (c' :) -- LHS cannot be split, add whole thing for now
                                              Just ml -> mapM_ (addSplitConstraint ml) (toDisjointGroups mr)
                                        else simpleConstraints %= (c' :) -- Some conjuncts of RHS are no covered (that is, do not contains _v), add whole thing
                  _ -> simpleConstraints %= (c' :)
          else modify $ addTypingConstraint c -- Constraint contains free predicate: add back and wait until more type variables get unified, so predicate variables can be instantiated
  where
    instantiateCons val fml@(Binary Eq v (Cons _ _ _)) | v == val = conjunction $ instantiateConsAxioms env False (Just val) fml
    instantiateCons _ fml = fml

    addSplitConstraint :: MonadHorn s => Map Id (Set Formula) -> (Set Id, Set Formula) -> TCSolver s ()
    addSplitConstraint ml (measures, rConjuncts) = do
      let rhs = conjunction rConjuncts
      let lhs = conjunction $ setConcatMap (\measure -> Map.findWithDefault Set.empty measure ml) measures
      let c' = Subtype env (ScalarT baseTL lhs potl) (ScalarT baseTR rhs potr) consistency
      simpleConstraints %= (c' :)


processConstraint c@(WellFormed env t@(ScalarT baseT fml pot))
  = do
      simpleConstraints %= (c :)
      case fml of
        Unknown _ u -> do
          qmap <- use qualifierMap
          tass <- use typeAssignment
          tq <- asks _typeQualsGen
          -- Only add qualifiers if it's a new variable; multiple well-formedness constraints could have been added for constructors
          let env' = typeSubstituteEnv tass env
          -- Should this be ghost? Probably... Doesn't really matter for well-formed constraints since we're only considering the potential of _v
          let env'' = addVariable valueVarName t env'
          unless (Map.member u qmap) $ addQuals u (tq env'' (Var (toSort baseT) valueVarName) (allScalars env'))
        _ -> return ()
processConstraint (WellFormedCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      cq <- asks _condQualsGen
      let env' = typeSubstituteEnv tass env
      addQuals u (cq env' (allScalars env'))
processConstraint (WellFormedMatchCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      mq <- asks _matchQualsGen
      let env' = typeSubstituteEnv tass env
      addQuals u (mq env' (allPotentialScrutinees env'))
processConstraint (RSubtype env pl pr)
  = do
      tass <- use typeAssignment
      pass <- use predAssignment
      let subst = sortSubstituteFml (asSortSubst tass) . substitutePredicate pass
      let pl' = subst pl
      let pr' = subst pr
      let env' = typeSubstituteEnv tass env
      let c' = RSubtype env' pl' pr'
      simpleConstraints %= (c' :)
processConstraint (SharedEnv env envl envr)
  = do
      tass <- use typeAssignment
      pass <- use predAssignment
      let substAndGetScalars = fmap toMonotype . nonGhostScalars . over symbols (scalarSubstituteEnv tass)
      let scalars = map (\(x, t) -> (Just x, t)) $ Map.assocs $ substAndGetScalars env
      let scalarsl = Map.elems $ substAndGetScalars envl
      let scalarsr = Map.elems $ substAndGetScalars envr
      cm <- view (resourceArgs . checkMultiplicities) 
      let cs = zipWith3 (partitionType cm env) scalars scalarsl scalarsr
      --let fpc = SharedForm env (_freePotential env) (_freePotential envl) (_freePotential envr)
      --let cfpc = SharedForm env (totalConditionalFP env) (totalConditionalFP envl) (totalConditionalFP envr)
      mapM_ processConstraint (concat cs)
      -- simpleConstraints %= (concat cs ++)
      --simpleConstraints %= (fpc :)
      --simpleConstraints %= (cfpc :)
processConstraint (ConstantRes env) = do
  tass <- use typeAssignment
  let env' = over symbols (scalarSubstituteEnv tass) env
  -- TODO: use  pred assignment to work w APs
  simpleConstraints %= (ConstantRes env' :)
-- processConstraint c@SharedForm{} = simpleConstraints %= (c :)
processConstraint c@(WellFormedPotential env p) = do
  pass <- use predAssignment
  simpleConstraints%= (WellFormedPotential env (substitutePredicate pass p) :)
processConstraint c@(SharedForm env f g h) = do
  pass <- use predAssignment
  -- traceM $ "Substituting in " ++ show (plain (pretty c))
  let f' = substitutePredicate pass f 
  let g' = substitutePredicate pass g 
  let h' = substitutePredicate pass h 
  simpleConstraints %= (SharedForm env f' g' h' :)
processConstraint (Transfer envIn envOut) = do
  tass <- use typeAssignment
  pass <- use predAssignment
  let envIn' = over symbols (scalarPredSubstituteEnv pass . scalarSubstituteEnv tass) envIn
  let envOut' = over symbols (scalarPredSubstituteEnv pass . scalarSubstituteEnv tass) envOut
  simpleConstraints %= (Transfer envIn' envOut' :)
processConstraint c = error $ show $ text "processConstraint: not a simple constraint" <+> pretty c

generateHornClauses :: (MonadHorn s, MonadSMT s) => Constraint -> TCSolver s ()
generateHornClauses (Subtype env (ScalarT baseTL l potl) (ScalarT baseTR r potr) True) | equalShape baseTL baseTR
  = do
      emb <- embedEnv env (l |&| r) False False
      let clause = conjunction (Set.insert l $ Set.insert r emb)
      consistencyChecks %= (clause :)
generateHornClauses c@(Subtype env (ScalarT baseTL l potl) (ScalarT baseTR r potr) _) | equalShape baseTL baseTR
  = do
      emb <- embedEnv env (l |&| r) True False
      clauses <- lift . lift . lift $ preprocessConstraint (conjunction (Set.insert l emb) |=>| r)
      hornClauses %= (clauses ++)
generateHornClauses WellFormed{}
  = return ()
generateHornClauses RSubtype{}
  = return ()
generateHornClauses SharedEnv{}
  = return ()
generateHornClauses SharedForm{}
  = return ()
generateHornClauses ConstantRes{}
  = return ()
generateHornClauses WellFormedPotential{}
  = return ()
generateHornClauses Transfer{}
  = return ()
generateHornClauses c = error $ show $ text "generateHornClauses: not a simple subtyping constraint" <+> pretty c

-- | 'allScalars' @env@ : logic terms for all scalar symbols in @env@
allScalars :: Environment -> [Formula]
allScalars env = mapMaybe toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (_, ForallT _ _) = Nothing
    toFormula (x, _) | x `Set.member` (env ^. letBound) = Nothing
    toFormula (x, Monotype t) = case t of
      ScalarT IntT  (Binary Eq _ (IntLit n)) _ -> Just $ IntLit n
      ScalarT BoolT (Var _ _) _ -> Just $ BoolLit True
      ScalarT BoolT (Unary Not (Var _ _)) _ -> Just $ BoolLit False
      ScalarT (DatatypeT dt [] []) (Binary Eq _ cons@(Cons _ name [])) _ | x == name -> Just cons
      ScalarT b _ _ -> Just $ Var (toSort b) x
      _ -> Nothing

-- | 'allPotentialScrutinees' @env@ : logic terms for all scalar symbols in @env@
allPotentialScrutinees :: Environment -> [Formula]
allPotentialScrutinees env = mapMaybe toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (x, Monotype t) = case t of
      ScalarT b@(DatatypeT _ _ _) _ _ ->
        if Set.member x (env ^. unfoldedVars) && notElem (Program (PSymbol x) t) (env ^. usedScrutinees)
          then Just $ Var (toSort b) x
          else Nothing
      _ -> Nothing
    toFormula _ = Nothing

hasPotentialScrutinees :: Monad s => Environment -> TCSolver s Bool
hasPotentialScrutinees env = do
  tass <- use typeAssignment
  return $ not $ null $ allPotentialScrutinees (typeSubstituteEnv tass env)

addTypeAssignment tv t = typeAssignment %= Map.insert tv t
addPredAssignment p fml = predAssignment %= Map.insert p fml

addQuals :: MonadHorn s => Id -> QSpace -> TCSolver s ()
addQuals name quals = do
  quals' <- lift . lift . lift $ pruneQualifiers quals
  qualifierMap %= Map.insert name quals'

-- | Add unknown @name@ with valuation @valuation@ to solutions of all candidates
addFixedUnknown :: MonadHorn s => Id -> Set Formula -> TCSolver s ()
addFixedUnknown name valuation = do
    addQuals name (toSpace Nothing (Set.toList valuation))
    candidates %= map update
  where
    update cand = cand { solution = Map.insert name valuation (solution cand) }

-- | 'fresh' @t@ : a type with the same shape as @t@ but fresh type variables, fresh predicate variables, and fresh unknowns as refinements
fresh :: MonadHorn s => Environment -> RType -> TCSolver s RType
fresh env (ScalarT b@(TypeVarT vSubst a m) _ p) | not (isBound env a) = do
  -- Free type variable: replace with fresh free type variable
  a' <- freshId "A"
  p' <- freshPotentials env (Just b) p
  return $ ScalarT (TypeVarT vSubst a' m) ftrue p'
fresh env (ScalarT baseT _ p) = do
  baseT' <- freshBase baseT
  -- Replace refinement with fresh predicate unknown:
  k <- freshId "U"
  p' <- freshPotentials env (Just baseT) p
  return $ ScalarT baseT' (Unknown Map.empty k) p'
  where
    freshBase (DatatypeT name tArgs _) = do
      -- Replace type arguments with fresh types:
      tArgs' <- mapM (fresh env) tArgs
      -- Replace predicate arguments with fresh predicate variables:
      let (DatatypeDef tParams pParams _ _ _ _) = (env ^. datatypes) Map.! name
      pArgs' <- mapM (\sig -> (freshPred env . map (noncaptureSortSubst tParams (map (toSort . baseTypeOf) tArgs')) $ predSigArgSorts sig) (predSigResSort sig)) pParams
      return $ DatatypeT name tArgs' pArgs'
    -- Ensure fresh base type has multiplicity 1 to avoid zeroing other formulas during unification
    freshBase baseT = return baseT
fresh env (FunctionT x tArg tFun c) =
  liftM2 (\t r -> FunctionT x t r c) (fresh env tArg) (fresh env tFun)
fresh env t = let (env', t') = embedContext env t in fresh env' t'

-- | Set valuation of unknown @name@ to @valuation@
-- and re-check all potentially affected constraints in all candidates
setUnknownRecheck :: MonadHorn s => Id -> Set Formula -> Set Id -> TCSolver s ()
setUnknownRecheck name valuation duals = do
  writeLog 3 $ text "Re-checking candidates after updating" <+> text name
  cands <- use candidates
  let cand = head cands
  let clauses = Set.filter (\fml -> name `Set.member` (Set.map unknownName (unknownsOf fml))) (validConstraints cand) -- First candidate cannot have invalid constraints
  let cands' = map (\c -> c { solution = Map.insert name valuation (solution c) }) cands
  env <- use initEnv
  cands'' <- lift . lift . lift $ checkCandidates False (Set.toList clauses) (instantiateConsAxioms env False Nothing) cands'

  if null cands''
    then throwError $ text "Re-checking candidates failed"
    else do
      let liveClauses = Set.filter (\fml -> duals `disjoint` (Set.map unknownName (unknownsOf fml))) (validConstraints cand)
      candidates .= map (\c -> c {
                                  validConstraints = Set.intersection liveClauses (validConstraints c),
                                  invalidConstraints = Set.intersection liveClauses (invalidConstraints c) }) cands'' -- Remove Horn clauses produced by now eliminated code

-- | 'matchConsType' @formal@ @actual@ : unify constructor return type @formal@ with @actual@
matchConsType env formal@(ScalarT (DatatypeT d vars pVars) _ _) actual@(ScalarT (DatatypeT d' args pArgs) _ p) | d == d'
  = do
      writeLog 3 $ text "Matching constructor type" $+$ pretty formal $+$ text "with scrutinee" $+$ pretty actual
      zipWithM_ (\(ScalarT (TypeVarT _ a _) ftrue _) t -> addTypeAssignment a t) vars args
      zipWithM_ (\(Pred _ p _) fml -> addPredAssignment p fml) pVars pArgs
matchConsType _ t t' = error $ show $ text "matchConsType: cannot match" <+> pretty t <+> text "against" <+> pretty t'

currentAssignment :: Monad s => RType -> TCSolver s RType
currentAssignment t = do
  tass <- use typeAssignment
  return $ typeSubstitute tass t

-- | Substitute type variables, predicate variables, and predicate unknowns in @t@
-- using current type assignment, predicate assignment, and liquid assignment
finalizeType :: Monad s => RType -> TCSolver s RType
finalizeType t = do
  tass <- use typeAssignment
  pass <- use predAssignment
  sol <- uses candidates (solution . head)
  return $ (typeApplySolution sol . typeSubstitutePred pass . typeSubstitute tass) t

-- | Substitute type variables, predicate variables, and predicate unknowns in @p@
-- using current type assignment, predicate assignment, and liquid assignment
finalizeProgram :: Monad s => RProgram -> TCSolver s (RProgram, TypingState)
finalizeProgram p = do
  tass <- use typeAssignment
  pass <- use predAssignment
  sol <- uses candidates (solution . head)
  tstate <- get
  let prog = typeApplySolution sol . typeSubstitutePred pass . typeSubstitute tass <$> p
  return (prog, tstate)


------------------------------------
------------------------------------
-- Utility functions
------------------------------------
------------------------------------

-- | Impose typing constraint @c@ on the programs
-- addTypingConstraint c = over typingConstraints (nub . (c :))


-- | Signal type error
throwError :: MonadHorn s => Doc -> TCSolver s ()
throwError msg = do
  (pos, ec) <- use errorContext
  lift $ lift $ throwE $ ErrorMessage TypeError pos (msg $+$ ec)

writeLog level msg = do
  maxLevel <- asks _tcSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return ()


-- | Check resource bounds: attempt to find satisfying expressions for multiplicity and potential annotations
checkResources :: (MonadHorn s, MonadSMT s, RMonad s)
               => [Constraint]
               -> TCSolver s ()
checkResources [] = return ()
checkResources constraints = do
  ps <- use persistentState
  let accConstraints = ps ^. resourceConstraints
  newC <- solveResourceConstraints accConstraints (filter isResourceConstraint constraints)
  case newC of
    Nothing -> throwError $ text "Insufficient resources"
    Just f  -> persistentState . resourceConstraints %= (++ f)
