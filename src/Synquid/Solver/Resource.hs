{-# LANGUAGE FlexibleContexts #-}

-- | Resource analysis
module Synquid.Solver.Resource (
  checkResources,
  simplifyRCs,
  allRMeasures,
  partitionType,
  getAnnotationStyle,
  getPolynomialDomain,
  replaceCons
) where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Solver.Monad
import Synquid.Pretty
import Synquid.Solver.CEGIS
import Synquid.Solver.Types
import Synquid.Solver.Util hiding (writeLog)

import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (tails, union, isPrefixOf)
import Data.Tuple.Extra (first)
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Monad.State
import Control.Lens
import Debug.Trace

-- | Check resource bounds: attempt to find satisfying expressions for multiplicity and potential annotations
checkResources :: (MonadHorn s, MonadSMT s, RMonad s)
               => [Constraint]
               -> TCSolver s ()
checkResources [] = return ()
checkResources constraints = do
  accConstraints <- use resourceConstraints
  newC <- solveResourceConstraints accConstraints (filter isResourceConstraint constraints)
  case newC of
    Nothing -> throwError $ text "Insufficient resources"
    Just f  -> resourceConstraints %= (++ f)

-- | Process, but do not solve, a set of resource constraints
simplifyRCs :: (MonadHorn s, MonadSMT s, RMonad s)
            => [Constraint]
            -> TCSolver s ()
simplifyRCs [] = return ()
simplifyRCs constraints = do
  rcs <- mapM generateFormula (filter isResourceConstraint constraints)
  resourceConstraints %= (++ rcs)

-- | 'solveResourceConstraints' @accConstraints constraints@ : Transform @constraints@ into logical constraints and attempt to solve the complete system by conjoining with @accConstraints@
solveResourceConstraints :: (MonadHorn s, RMonad s)
                         => [ProcessedRFormula]
                         -> [Constraint]
                         -> TCSolver s (Maybe [ProcessedRFormula])
solveResourceConstraints _ [] = return $ Just []
solveResourceConstraints accConstraints constraints = do
    writeLog 3 $ linebreak <> text "Generating resource constraints:"
    -- Check satisfiability
    constraintList <- mapM generateFormula constraints
    b <- satisfyResources (accConstraints ++ constraintList)
    let result = if b then "SAT" else "UNSAT"
    writeLog 5 $ nest 4 $ text "Accumulated resource constraints:"
      $+$ pretty (map bodyFml accConstraints)
    writeLog 3 $ nest 4 $ text "Solved resource constraint after conjoining formulas:"
      <+> text result $+$ prettyConjuncts (map bodyFml constraintList)
    return $ if b
      then Just constraintList -- $ Just $ if hasUniversals
      else Nothing

-- | 'generateFormula' @c@: convert constraint @c@ into a logical formula
--    If there are no universal quantifiers, we can cache the generated formulas
--    Otherwise, we must re-generate every time
generateFormula :: (MonadHorn s, RMonad s)
                => Constraint
                -> TCSolver s ProcessedRFormula
generateFormula c = do
  checkMults <- asks _checkMultiplicities
  generateFormula' checkMults c

generateFormula' :: (MonadHorn s, RMonad s)
                 => Bool
                 -> Constraint
                 -> TCSolver s ProcessedRFormula
generateFormula' checkMults c = do
  writeLog 4 $ indent 2 $ simplePrettyConstraint c <+> operator "~>"
  let mkRForm = RFormula Set.empty Set.empty Set.empty
  case c of
    Subtype{} -> error $ show $ text "generateFormula: subtype constraint present:" <+> pretty c
    WellFormed{} -> error $ show $ text "generateFormula: well-formed constraint present:" <+> pretty c
    RSubtype env pl pr -> do
      op <- subtypeOp
      substs <- generateFreshUniversals env
      let fml = mkRForm substs Map.empty $ pl `op` pr
      embedAndProcessConstraint env Nothing fml
    SharedForm env f fl fr -> do
      let sharingFml = f |=| (fl |+| fr)
      let wf = conjunction [f |>=| fzero, fl |>=| fzero, fr |>=| fzero]
      substs <- generateFreshUniversals env
      let fml = mkRForm substs Map.empty (wf |&| sharingFml)
      embedAndProcessConstraint env Nothing fml
    ConstantRes env -> do
      substs <- generateFreshUniversals env
      (pending, f) <- assertZeroPotential env
      let fml = mkRForm substs pending f
      embedAndProcessConstraint env Nothing fml
    Transfer env env' -> do
      substs <- generateFreshUniversals env
      (pending, fmls) <- redistribute env env'
      let fml = mkRForm substs pending $ conjunction fmls
      embedAndProcessConstraint env Nothing fml
    _ -> error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c


-- Constraint pre-processing pipeline
embedAndProcessConstraint :: (MonadHorn s, RMonad s)
                          => Environment
                          -> Maybe Formula
                          -> RawRFormula
                          -> TCSolver s ProcessedRFormula
embedAndProcessConstraint env extra rfml = do
  hasUnivs <- isJust <$> asks _cegisDomain
  let go = insertAssumption extra
       >=> embedConstraint env
       >=> instantiateUnknowns
       >=> instantiateAxioms env
       >=> elaborateAssumptions
       >=> updateVars
       >=> formatVariables
       >=> applyAssumptions
  if hasUnivs
    then go rfml
    else translateAndFinalize rfml
    {- else return $ rfml {
      _knownAssumptions = (),
      _unknownAssumptions = ()
    } -}

translateAndFinalize :: RMonad s => RawRFormula -> TCSolver s ProcessedRFormula 
translateAndFinalize rfml = do 
  writeLog 3 $ indent 4 $ pretty (bodyFml rfml)
  z3lit <- lift . lift . lift $ translate $ bodyFml rfml
  return $ rfml {
    _knownAssumptions = ftrue,
    _unknownAssumptions = (),
    _rconstraints = z3lit
  }

-- Insert extra assumption, if necessary
insertAssumption :: Monad s => Maybe Formula -> RawRFormula -> TCSolver s RawRFormula
insertAssumption Nothing f = return f
insertAssumption (Just extra) rfml = return $ 
  case extra of
    u@Unknown{} -> over unknownAssumptions (Set.insert u) rfml 
    f           -> over knownAssumptions (Set.insert f) rfml 

-- Embed context and generate constructor axioms
embedConstraint :: (MonadHorn s, RMonad s)
                => Environment
                -> RawRFormula
                -> TCSolver s RawRFormula
embedConstraint env rfml = do 
  useMeasures <- maybe False shouldUseMeasures <$> asks _cegisDomain
  -- Get assumptions related to all non-ghost scalar variables in context
  vars <- use universalVars
  -- THIS IS A HACK -- need to ensure we grab the assumptions related to _v
  -- Note that sorts DO NOT matter here -- the embedder will ignore them.
  let vars' = Set.insert (Var AnyS valueVarName) $ Set.map (Var AnyS) vars
  ass <- embedSynthesisEnv env (conjunction vars') True useMeasures
  --emb <- Set.filter (\f -> not (isUnknownForm f) && isNumeric f) <$> embedSynthesisEnv env (conjunction vars') True useMeasures
  --unk <- Set.filter isUnknownForm ass
  let emb = Set.filter (not . isUnknownForm) ass
  let unk = Set.filter isUnknownForm ass
  return $ over knownAssumptions (Set.union emb) 
         $ over unknownAssumptions (Set.union unk) rfml


instantiateUnknowns :: MonadHorn s => RawRFormula -> TCSolver s RawRFormula
instantiateUnknowns rfml = do 
  unknown' <- assignUnknowns (_unknownAssumptions rfml)
  return $ set unknownAssumptions Set.empty
         $ over knownAssumptions (Set.union unknown') rfml


instantiateAxioms :: MonadHorn s => Environment -> RawRFormula -> TCSolver s RawRFormula
instantiateAxioms env rfml = do 
  let known = _knownAssumptions rfml
  useMeasures <- maybe False shouldUseMeasures <$> asks _cegisDomain
  let axioms = if useMeasures
        then instantiateConsAxioms (env { _measureDefs = allRMeasures env } ) True Nothing (conjunction known)
        else Set.empty
  return $ over knownAssumptions (Set.union axioms) rfml


replaceCons f@Cons{} = mkFuncVar f
replaceCons f = f

replacePred f@Pred{} = mkFuncVar f
replacePred f = f

-- Instantiate universally quantified expressions
-- Generate congruence axioms
elaborateAssumptions :: MonadHorn s => RawRFormula -> TCSolver s (RawRFormula, Set Formula)
elaborateAssumptions rfml = do 
  -- Instantiate universals
  res <- mapM instantiateForall $ Set.toList (_knownAssumptions rfml)
  let instantiatedEmb = map fst res
  -- Generate variables for predicate applications
  let bodyPreds = gatherPreds (_rconstraints rfml)
  -- Generate congruence axioms
  let allPreds = Set.unions $ bodyPreds : map snd res
  let congruenceAxioms = generateCongAxioms allPreds
  let completeEmb = Set.fromList $ congruenceAxioms ++ concat instantiatedEmb
  return (set knownAssumptions completeEmb rfml, allPreds)

updateVars :: MonadHorn s => (RawRFormula, Set Formula) -> TCSolver s RawRFormula
updateVars (rfml, allPreds) = do
  -- substitute all universally quantified expressions in body, known, and allPreds  
  let substs = _varSubsts rfml
  cons <- use matchCases
  let format = Set.map (transformFml mkFuncVar . substitute substs)
  universalMeasures %= Set.union (Set.map (transformFml mkFuncVar) (Set.map (substitute substs) allPreds))
  return $ set renamedPreds (format (cons `Set.union` allPreds))
         $ over knownAssumptions (Set.map (substitute substs)) 
         $ over rconstraints (substitute substs) rfml


formatVariables :: MonadHorn s => RawRFormula -> TCSolver s RawRFormula
formatVariables rfml = do 
  let update = Set.map (transformFml mkFuncVar)
  return $ over unknownAssumptions update 
         $ over knownAssumptions update 
         $ over rconstraints (transformFml mkFuncVar) rfml

applyAssumptions :: MonadHorn s
                 => RawRFormula
                 -> TCSolver s ProcessedRFormula
applyAssumptions (RFormula known unknown preds substs pending fml) = do
  aDomain <- asks _cegisDomain
  let ass = conjunction $ Set.union known unknown
  writeLog 3 $ indent 4 $ pretty (ass |=>| fml) -- conjunction (map lcToFml lcs))
  return $ RFormula ass () preds substs pending fml 


-- | Check the satisfiability of the generated resource constraints, instantiating universally
--     quantified expressions as necessary.
satisfyResources :: RMonad s
                 => [ProcessedRFormula]
                 -> TCSolver s Bool
satisfyResources rfmls = do
  let runInSolver = lift . lift . lift
  noUnivs <- isNothing <$> asks _cegisDomain
  if noUnivs
    then do
      let fml = conjunction $ map bodyFml rfmls
      model <- runInSolver $ solveAndGetModel fml
      case model of
        Nothing -> return False
        Just m' -> do
          writeLog 6 $ nest 2 (text "Solved with model") </> nest 6 (text (snd m'))
          return True
    else do
      ufmls <- map (Var IntS) . Set.toList <$> use universalVars
      --traceM $ "vars: " ++ show (plain (pretty ufmls))
      universals <- collectUniversals' rfmls ufmls
      cMax <- asks _cegisMax
      cstate <- updateCEGISState

      writeLog 3 $ text "Solving resource constraint with CEGIS:"
      writeLog 5 $ pretty $ conjunction $ map completeFml rfmls
      logUniversals  
      
      let go = solveWithCEGIS cMax rfmls universals
      (sat, cstate') <- runInSolver $ runCEGIS go cstate
      storeCEGISState cstate'
      return sat

storeCEGISState :: Monad s => CEGISState -> TCSolver s ()
storeCEGISState st = do 
  cegisState .= st
  incremental <- asks _incrementalCEGIS
  -- For non-incremental solving, don't reset resourceVars
  when incremental $
    resourceVars .= Map.empty

-- Given a list of resource constraints, assemble the relevant universally quantified 
--   expressions for the CEGIS solver: renamed variables, constructor and measure applications
collectUniversals :: Monad s => [ProcessedRFormula] -> TCSolver s Universals
collectUniversals rfmls = do 
  let preds = map (\(Var s x) -> (x, Var s x)) (collectUFs rfmls) 
  return $ Universals (formatUniversals (collectVars rfmls)) preds

collectUniversals' :: Monad s => [ProcessedRFormula] -> [Formula] -> TCSolver s Universals
collectUniversals' rfmls extra = do 
  let preds = map (\(Var s x) -> (x, Var s x)) (collectUFs rfmls) 
  return $ Universals (formatUniversals (extra ++ collectVars rfmls)) preds

collectVars :: [ProcessedRFormula] -> [Formula]
collectVars = concatMap (Map.elems . _varSubsts)

collectUFs :: [ProcessedRFormula] -> [Formula]
collectUFs = concatMap (Set.toList . _renamedPreds)

shouldUseMeasures :: AnnotationDomain -> Bool
shouldUseMeasures ad = case ad of
    Variable -> False
    _ -> True

-- Nondeterministically redistribute top-level potentials between variables in context
redistribute :: Monad s
             => Environment
             -> Environment
             -> TCSolver s (PendingRSubst, [Formula])
redistribute envIn envOut = do
  let fpIn  = envIn ^. freePotential
  let fpOut = envOut ^. freePotential
  let cfpIn  = totalConditionalFP envIn
  let cfpOut = totalConditionalFP envOut
  let wellFormedFP = fmap (|>=| fzero) [fpIn, fpOut, cfpIn, cfpOut]
  -- Sum of top-level potential annotations
  let envSum = sumFormulas . allPotentials
  -- Assert that all potentials are well-formed
  let wellFormed env = map (|>=| fzero) (Map.elems (allPotentials env))
  -- Assert (fresh) potentials in output context are well-formed
  let wellFormedAssertions = wellFormedFP ++ wellFormed envOut
  --Assert that top-level potentials are re-partitioned
  let transferAssertions = (envSum envIn |+| fpIn |+| cfpIn) |=| (envSum envOut |+| fpOut |+| cfpOut)
  -- No pending substitutions for now
  let substitutions e = Map.foldlWithKey generateSubstFromType Map.empty (toMonotype <$> nonGhostScalars e) 
  return (Map.union (substitutions envIn) (substitutions envOut), transferAssertions : wellFormedAssertions)

-- Assert that a context contains zero "free" potential
assertZeroPotential :: Monad s
                    => Environment
                    -> TCSolver s (PendingRSubst, Formula)
assertZeroPotential env = do
  let substitutions = Map.foldlWithKey generateSubstFromType Map.empty (toMonotype <$> nonGhostScalars env)
  let envSum = sumFormulas . allPotentials 
  let fml = ((env ^. freePotential) |+| envSum env) |=| fzero
  return (substitutions, fml)

allPotentials :: Environment -> Map String Formula 
allPotentials env = Map.mapMaybeWithKey substTopPotential $ toMonotype <$> nonGhostScalars env
  where 
    substTopPotential x t = 
      substitute (Map.singleton valueVarName (Var (toSort (baseTypeOf t)) x)) <$> topPotentialOf t

generateFreshUniversals :: Monad s => Environment -> TCSolver s Substitution
generateFreshUniversals env = do 
  relevant <- use universalVars
  --let univs = Map.filterWithKey (\x _ -> x `Set.member` relevant) $ symbolsOfArity 0 env
  let univs = Map.filterWithKey (\x _ -> x == valueVarName) $ symbolsOfArity 0 env
  Map.traverseWithKey freshen univs
  where 
    sortFrom = toSort . baseTypeOf . toMonotype
    freshen x sch = do 
      x' <- freshVersion x 
      return $ Var (sortFrom sch) x'

-- Substitute for _v in potential annotation
generateSubstFromType :: PendingRSubst -> String -> RType -> PendingRSubst
generateSubstFromType subs x t =
  case topPotentialOf t of
    Nothing -> subs
    Just (Ite g p q) ->
      let value' = Var (toSort (baseTypeOf t)) x
          sub = Map.singleton valueVarName value'
      in Map.insert p sub $ Map.insert q sub subs
    Just p ->
      let value' = Var (toSort (baseTypeOf t)) x
      in Map.insert p (Map.singleton valueVarName value') subs


-- Generate sharing constraints, given a type and the two types
--   into which it is shared
partitionType :: Bool
              -> Environment
              -> (String, RType)
              -> RType
              -> RType
              -> [Constraint]
partitionType cm env (x, t@(ScalarT b _ f)) (ScalarT bl _ _) (ScalarT br _ _) 
  | f == fzero = partitionBase cm env (x, b) bl br
partitionType cm env (x, t@(ScalarT b _ f)) (ScalarT bl _ fl) (ScalarT br _ fr)
  = let vvtype = addRefinement t (varRefinement x (toSort b))
        env'   = addVariable valueVarName vvtype env 
    in SharedForm env' f fl fr : partitionBase cm env (x, b) bl br

partitionBase cm env (x, DatatypeT _ ts _) (DatatypeT _ tsl _) (DatatypeT _ tsr _)
  = concat $ zipWith3 (partitionType cm env) (zip (repeat x) ts) tsl tsr
partitionBase cm env (x, b@(TypeVarT _ a m)) (TypeVarT _ _ ml) (TypeVarT _ _ mr)
  = [SharedForm env m ml mr | cm]
partitionBase _ _ _ _ _ = []


-- Is given constraint relevant for resource analysis
isResourceConstraint :: Constraint -> Bool
isResourceConstraint (Subtype _ ScalarT{} ScalarT{} _) = False
isResourceConstraint RSubtype{}    = True
isResourceConstraint WellFormed{}  = False
isResourceConstraint SharedEnv{}   = False -- should never be present by now
isResourceConstraint SharedForm{}  = True
isResourceConstraint ConstantRes{} = True
isResourceConstraint Transfer{}    = True
isResourceConstraint _             = False

-- Return refinement of scalar type
refinementOf :: RType -> Formula
refinementOf (ScalarT _ fml _) = fml
refinementOf _                 = error "error: Encountered non-scalar type when generating resource constraints"

-- Instantiate universally quantified expression with all possible arguments in the
--   quantified position. Also generate congruence axioms.
-- POSSIBLE PROBLEM: this doesn't really recurse looking for arbitrary foralls
--   It will find them if top-level or nested below a single operation. This SHOULD
--   be ok for our current scenario...
-- The function returns a pair, the first element of which is a list of all formulas,
--   including new predicate applications, the second is a set of just the instantiated apps
instantiateForall :: Monad s => Formula -> TCSolver s ([Formula], Set Formula)
instantiateForall f@All{} = instantiateForall' f
instantiateForall f       = return ([f], gatherPreds f)

instantiateForall' (All f g) = instantiateForall' g
instantiateForall' f         = instantiatePred f

instantiatePred :: Monad s => Formula -> TCSolver s ([Formula], Set Formula)
instantiatePred fml@(Binary op p@(Pred s x args) axiom) = do
  env <- use initEnv
  case Map.lookup x (allRMeasures env) of
    Nothing -> error $ show $ text "instantiatePred: measure definition not found" <+> pretty p
    Just mdef -> do
      let substs = allValidCArgs env mdef p
      let allPreds = map (`substitute` p) substs
      let allFmls = map (`substitute` fml) substs
      return (allFmls, Set.fromList allPreds)

-- Replace predicate applications in formula f with appropriate variables,
--   collecting all such predicate applications present in f
gatherPreds :: Formula -> Set Formula
gatherPreds (Unary op f)    = gatherPreds f
gatherPreds (Binary op f g) = gatherPreds f `Set.union` gatherPreds g
gatherPreds (Ite g t f)     = Set.unions [gatherPreds g, gatherPreds t, gatherPreds f]
gatherPreds (All f g)       = gatherPreds g -- maybe should handle quantified fmls...
gatherPreds (SetLit s fs)   = Set.unions $ map gatherPreds fs
gatherPreds f@Pred{}        = Set.singleton f
gatherPreds f               = Set.empty

-- Generate all congruence axioms, given all instantiations of universally quantified
--   measure applications
generateCongAxioms :: Set Formula -> [Formula]
generateCongAxioms preds = concatMap assertCongruence $ Map.elems (groupPreds preds)
  where
    groupPreds = foldl (\pmap p@(Pred _ x _) -> Map.insertWith (++) x [p] pmap) Map.empty

-- Generate all congruence relations given a list of possible applications of
--   some measure
assertCongruence :: [Formula] -> [Formula]
assertCongruence allApps = map assertCongruence' (pairs allApps)
  where
    -- All pairs from a list
    pairs xs = [(x, y) | (x:ys) <- tails xs, y <- ys]

assertCongruence' (pl@(Pred _ ml largs), pr@(Pred _ mr rargs)) =
  --conjunction (zipWith (|=|) largs rargs) |=>| (mkvar pl |=| mkvar pr)
  conjunction (zipWith (|=|) largs rargs) |=>| (pl |=| pr)
  where
    mkvar = transformFml mkFuncVar
assertCongruence' ms = error $ show $ text "assertCongruence: called with non-measure formulas:"
  <+> pretty ms

-- | 'getValueVarSubst' @env fml@ : Given a context and formula, find the valuation of _v
--    by inspecting its refinement of the form _v :: { B | _v == x }
--    and return this substitution [x / _v]
getValueVarSubst :: Environment -> Substitution
getValueVarSubst env =
  case Map.lookup valueVarName (symbolsOfArity 0 env) of
    Nothing -> Map.empty
    Just sc -> Map.singleton valueVarName $ getVVFromType (toMonotype sc)

getVVFromType (ScalarT _ ref _) = findVV ref
  where findVV (Binary Eq (Var _ "_v") right) = right
        findVV _ = error $ show $ text "getVVFromType: ill-formed refinement:" <+> pretty ref
getVVFromType t = error $ show $ text "getVVFromType: non-scalar type:" <+> pretty t

getAnnotationStyle = getAnnotationStyle' . toMonotype

getAnnotationStyle' t =
  let rforms = conjunction $ allRFormulas True t
  in case (hasVar rforms, hasPred rforms) of
      (True, True)  -> Just Both
      (False, True) -> Just Measure
      (True, _)     -> Just Variable
      _             -> Nothing

getPolynomialDomain = getPolynomialDomain' . toMonotype

getPolynomialDomain' t = 
  let rforms = conjunction $ allRFormulas True t 
  in case (hasVarITE rforms, hasPredITE rforms) of 
      (True, True)  -> Just Both
      (False, True) -> Just Measure
      (True, _)     -> Just Variable
      _             -> Nothing


subtypeOp :: Monad s => TCSolver s (Formula -> Formula -> Formula)
subtypeOp = do
  ct <- asks _constantRes
  return $ if ct then (|=|) else (|>=|)

logUniversals :: Monad s => TCSolver s ()
logUniversals = do 
  uvars <- Set.toList <$> use universalVars
  ufuns <- Set.toList <$> use universalMeasures
  capps <- Set.toList <$> use matchCases
  writeLog 3 $ indent 2 $ text "Over universally quantified variables:"
    <+> hsep (map pretty uvars) <+> text "and functions:"
    <+> hsep (map pretty (ufuns ++ capps))

writeLog level msg = do
  maxLevel <- asks _tcSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return ()