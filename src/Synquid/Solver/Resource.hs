{-# LANGUAGE FlexibleContexts #-}

-- | Resource analysis
module Synquid.Solver.Resource (
  checkResources,
  processResources,
  allUniversals,
  allRFormulas,
  allRMeasures,
  partitionType,
  getAnnotationStyle
) where

import Synquid.Logic 
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Solver.Monad
import Synquid.Pretty
import Synquid.Solver.Util hiding (writeLog)
import Synquid.Solver.CEGIS 

import Data.List (union)
import Data.Maybe
import qualified Data.Set as Set 
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Lens
import Debug.Trace

{- Implementation -}

-- | Check resource bounds: attempt to find satisfying expressions for multiplicity and potential annotations 
checkResources :: (MonadHorn s, MonadSMT s, RMonad s) 
               => [Constraint] 
               -> TCSolver s ()
checkResources [] = return () 
checkResources constraints = do 
  oldConstraints <- use resourceConstraints 
  newC <- solveResourceConstraints oldConstraints (filter isResourceConstraint constraints)
  case newC of 
    Nothing -> throwError $ text "Insufficient resources"
    Just f  -> resourceConstraints %= (++ f) 

processResources :: (MonadHorn s, MonadSMT s, RMonad s)
                 => [Constraint]
                 -> TCSolver s ()
processResources [] = return ()
processResources constraints = do 
  rcs <- mapM (generateFormula True . Right) constraints 
  resourceConstraints %= (++ map Left rcs)
  
-- | 'solveResourceConstraints' @oldConstraints constraints@ : Transform @constraints@ into logical constraints and attempt to solve the complete system by conjoining with @oldConstraints@
solveResourceConstraints :: (MonadHorn s, RMonad s) => [RConstraint] -> [Constraint] -> TCSolver s (Maybe [RConstraint]) 
solveResourceConstraints _ [] = return $ Just [] 
solveResourceConstraints oldConstraints constraints = do
    writeLog 3 $ linebreak <+> text "Generating resource constraints:"
    -- Need environment to determine which annotation formulas are universally quantified
    let tempEnv = envFrom $ head constraints
    -- Generate numerical resource-usage formulas from typing constraints:
    constraintList <- mapM (generateFormula True . Right) constraints
    accFmls <- mapM (generateFormula False) oldConstraints
    query <- assembleQuery accFmls constraintList 
    -- Check satisfiability
    universals <- use universalFmls
    b <- satisfyResources tempEnv (Set.toList universals) query
    let result = if b then "SAT" else "UNSAT"
    writeLog 5 $ nest 4 $ text "Accumulated resource constraints:" 
      $+$ prettyConjuncts (filter (isInteresting . rformula . constraint) accFmls)
    writeLog 3 $ nest 4 $ text "Solved resource constraint after conjoining formulas:" 
      <+> text result $+$ prettyConjuncts (filter (isInteresting . rformula . constraint) constraintList)
    return $ if b 
      then Just $ map Left $ filter (not . isTrivialTC) constraintList -- $ Just $ if hasUniversals
      else Nothing


-- | Given lists of constraints (newly-generated and accumulated), construct the corresponding solver query
assembleQuery :: MonadHorn s 
              => [TaggedConstraint] 
              -> [TaggedConstraint] 
              -> TCSolver s [RFormula]
assembleQuery accConstraints constraints = do
  let fmlList    = map constraint (filter (not . isTrivialTC) constraints)
  let accFmlList = map constraint accConstraints
  let allRFmls = accFmlList ++ fmlList 
  mapM applyAssumptions allRFmls

applyAssumptions :: MonadHorn s 
                 => RFormula 
                 -> TCSolver s RFormula
applyAssumptions (RFormula known unknown substs fml) = do 
  emb <- assignUnknowns unknown
  univs <- use universalFmls
  aDomain <- asks _cegisDomain
  rms <- Map.keys <$> use resourceMeasures
  let useMeasures = maybe False shouldUseMeasures aDomain 
  let emb' = Set.filter (isRelevantAssumption useMeasures rms univs) emb
  let known' = Set.filter (isRelevantAssumption useMeasures rms univs) known
  let finalFml = if isNothing aDomain 
      then fml
      else (conjunction known' |&| conjunction emb') |=>| fml
  writeLog 3 $ text "Assembled formula:" <+> pretty finalFml
  return $ RFormula Set.empty Set.empty substs finalFml 

isTrivialTC (TaggedConstraint _ f) = isTrivial . rformula $ f

-- | 'generateFormula' @c@: convert constraint @c@ into a logical formula
--    If there are no universal quantifiers, we can cache the generated formulas (the Left case)
--    Otherwise, we must re-generate every time
generateFormula :: (MonadHorn s, RMonad s) => Bool -> RConstraint -> TCSolver s TaggedConstraint
generateFormula _ (Left tc) = return tc
generateFormula shouldLog (Right c) = do 
  checkMults <- asks _checkMultiplicities
  generateFormula' shouldLog checkMults c

generateFormula' :: (MonadHorn s, RMonad s)
                 => Bool 
                 -> Bool 
                 -> Constraint 
                 -> TCSolver s TaggedConstraint 
generateFormula' shouldLog checkMults c = 
  let assemble fs = conjunction (filter (not . isTrivial) fs) 
      -- Start without assumptions, known or unknown
      mkRForm = RFormula Set.empty Set.empty in
  case c of 
    Subtype env tl tr variant label -> do
      op <- subtypeOp
      let fmls = mkRForm Map.empty $ assemble (directSubtypes checkMults op tl tr)
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls Nothing
    RSubtype env pl pr label -> do 
      op <- subtypeOp 
      let fml = mkRForm Map.empty $ pl `op` pr
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fml Nothing
    WellFormed env t label -> do
      let fmls = mkRForm Map.empty $ assemble $ map (|>=| fzero) $ allRFormulas checkMults t
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls (Just (refinementOf t))
    SharedForm env f fl fr label -> do 
      let sharingFml = f |=| (fl |+| fr)  
      let wf = conjunction [f |>=| fzero, fl |>=| fzero, fr |>=| fzero]
      let fmls = mkRForm Map.empty (wf |&| sharingFml)
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls Nothing
    ConstantRes env label -> do 
      (substs, f) <- assertZeroPotential env
      let fmls = mkRForm substs f 
      TaggedConstraint ("CT: " ++ label) <$> embedAndProcessConstraint shouldLog env c fmls Nothing
    Transfer env env' label -> do 
      (fmls, substs) <- redistribute env env' 
      let rfml = mkRForm substs $ assemble fmls
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c rfml Nothing 
    _ -> error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c

-- | Embed the environment assumptions and preproess the constraint for solving 
embedAndProcessConstraint :: (MonadHorn s, RMonad s)
                          => Bool 
                          -> Environment 
                          -> Constraint 
                          -> RFormula
                          -> Maybe Formula
                          -> TCSolver s RFormula
embedAndProcessConstraint shouldLog env c rfml extra = do 
  let fml = rformula rfml
  let substs = pendingSubsts rfml
  aDomain <- asks _cegisDomain
  -- If the top-level annotations do not contain measures,
  --   do not consider any assumptions over measures or any post conditions
  let useMeasures = maybe False shouldUseMeasures aDomain 
  univs <- use universalFmls
  let possibleVars = varsOf fml
  --traceM $ "POSSIBLE: " ++ show possibleVars
  emb <- Set.filter (not . isUnknownForm) <$> embedSynthesisEnv env (conjunction possibleVars) True useMeasures
  let axioms = if useMeasures
      then instantiateConsAxioms env True Nothing (conjunction emb)
      else Set.empty
  noUnivs <- isNothing <$> asks _cegisDomain
  let (finalEmb, unknownEmb) = 
        if noUnivs 
          then (Set.empty, Set.empty)
          else (Set.union emb axioms, allUnknowns env)
  let (finalEmb', unknownEmb') = case extra of 
        Nothing -> (finalEmb, unknownEmb)
        Just u@Unknown{} -> (finalEmb, Set.insert u unknownEmb)
        Just f -> (Set.insert f finalEmb, unknownEmb)
  -- Only for logging:
  let printFml = conjunction finalEmb |=>| fml
  --when shouldLog $ writeLog 3 (nest 4 $ pretty c $+$ text "Gives numerical constraint" <+> pretty printFml)
  return $ RFormula finalEmb' unknownEmb' substs fml

-- Filter out irrelevant assumptions -- might be measures, and 
--   any operation over a non-integer variable
isRelevantAssumption :: Bool -> [String] -> Set Formula -> Formula -> Bool 
isRelevantAssumption _ _ rvs v@Var{} = True --Set.member v rvs
isRelevantAssumption useM rms _ (Pred _ x _) = useM && x `elem` rms
isRelevantAssumption _ _ _ Unknown{} = False -- TODO: fix once i start assuming unknowns
isRelevantAssumption useM rms rvs (Unary _ f) = isRelevantAssumption useM rms rvs f
isRelevantAssumption useM rms rvs (Binary _ f g) = isRelevantAssumption useM rms rvs f && isRelevantAssumption useM rms rvs g
isRelevantAssumption useM rms rvs (Ite f g h) = isRelevantAssumption useM rms rvs f && isRelevantAssumption useM rms rvs g && isRelevantAssumption useM rms rvs h
isRelevantAssumption useM _ _ Cons{} = useM
isRelevantAssumption useM rms rvs (All f g) = isRelevantAssumption useM rms rvs g -- trace "Warning: universally quantified assumption" True
isRelevantAssumption _ _ _ _ = True


-- | Check the satisfiability of the generated resource constraints, instantiating universally 
--     quantified expressions as necessary.
satisfyResources :: RMonad s 
                 => Environment 
                 -> [Formula] 
                 -> [RFormula]
                 -> TCSolver s Bool
satisfyResources env universals rfmls = do 
  shouldInstantiate <- asks _instantiateUnivs
  noUnivs <- isNothing <$> asks _cegisDomain
  if noUnivs || not shouldInstantiate
    then do 
      let fml = conjunction $ map rformula rfmls
      model <- lift . lift . lift $ solveAndGetModel fml
      case model of
        Nothing -> return False
        Just m' -> do 
          writeLog 6 $ nest 2 (text "Solved with model") </> nest 6 (text (snd m'))
          return True 
    else do
      cMax <- asks _cegisMax
      -- Unsafe, but should be OK since we already checked that universals are non-null
      aDomain <- fromJust <$> asks _cegisDomain
      rVars <- use resourceVars
      -- Construct list of universally quantified expressions, storing the formula with a string representation
      let universalsWithVars = formatUniversals universals 
      uMeasures <- Map.assocs <$> use resourceMeasures
      -- Initialize polynomials for each resource variable
      let init name info = initializePolynomial env aDomain uMeasures (name, info) 
      let allPolynomials = Map.mapWithKey init rVars
      -- List of all coefficients in the list of all polynomials
      let allCoefficients = concat $ Map.elems $ fmap coefficientsOf allPolynomials
      -- Initialize all coefficient values -- the starting value should not matter
      let initialProgram = Map.fromList $ zip allCoefficients initialCoefficients 
      -- Assume that all measure applications are well-formed:
      let useMeasures = shouldUseMeasures aDomain 
      let ass = if useMeasures
          then conjunction $ map (|>=| fzero) (possibleMeasureApps env universals uMeasures)
          else ftrue
      let allUniversals = Universals universalsWithVars uMeasures 
      writeLog 3 $ text "Solving resource constraint with CEGIS:" 
      writeLog 5 $ pretty $ conjunction $ map rformula rfmls
      writeLog 3 $ text "Over universally quantified expressions:" <+> hsep (map (pretty . snd) universalsWithVars)
      solveWithCEGIS cMax rfmls ass allUniversals [] allPolynomials initialProgram 

shouldUseMeasures  ad = case ad of 
    Variable -> False 
    _ -> True 

adjustSorts (BoolLit b) = BoolLit b
adjustSorts (IntLit b) = IntLit b
adjustSorts (Var _ x) = Var IntS x
adjustSorts (Binary op f g) = Binary op (adjustSorts f) (adjustSorts g)
adjustSorts (Unary op f) = Unary op (adjustSorts f)

allRMeasures sch = allRMeasures' (typeFromSchema sch) 

allRMeasures' :: RType -> Map String MeasureDef -> Map String MeasureDef
allRMeasures' typ measures = 
  let rforms = allRFormulas True typ
      allPreds = Set.unions $ map getAllPreds rforms
  in  Map.filterWithKey (\x _ -> x `Set.member` allPreds) measures

-- Nondeterministically redistribute top-level potentials between variables in context
redistribute :: Monad s 
             => Environment 
             -> Environment 
             -> TCSolver s ([Formula], Map Formula Substitution)
redistribute envIn envOut = do
  let fpIn  = _freePotential envIn 
  let fpOut = _freePotential envOut 
  -- All (non-ghost) scalar types 
  let scalarsOf env = typeFromSchema <$> nonGhostScalars env
  -- All top-level potential annotations of a map of scalar types
  let topPotentials = Map.mapMaybe topPotentialOf
  -- Generate pending substitutions 
  -- TODO: generalize this to potentials that aren't just free variables!
  let substitutions e = Map.foldlWithKey generateSubst Map.empty (scalarsOf e)
  -- Sum of all top-level potentials of scalar types in context
  let envSum env = sumFormulas $ topPotentials $ Map.mapWithKey applySubst $ scalarsOf env
  -- Assert that all potentials are well-formed
  let wellFormed smap = map (|>=| fzero) ((Map.elems . topPotentials) smap) 
  -- Assert (fresh) potentials in output context are well-formed
  let wellFormedAssertions = (fpIn |>=| fzero) : (fpOut |>=| fzero) : wellFormed (scalarsOf envOut) 
  --Assert that top-level potentials are re-partitioned
  let transferAssertions = (envSum envIn |+| fpIn) |=| (envSum envOut |+| fpOut)
  return (transferAssertions : wellFormedAssertions, Map.union (substitutions envIn) (substitutions envOut))

-- Substitute for _v in potential annotation
generateSubst subs x t = 
  case topPotentialOf t of 
    Nothing -> subs 
    Just (Ite g p q) -> 
      let value' = Var (toSort (baseTypeOf t)) x
          subs' = Map.insert p (Map.singleton valueVarName value') subs
      in Map.insert q (Map.singleton valueVarName value') subs
    Just p ->
      let value' = Var (toSort (baseTypeOf t)) x 
      in Map.insert p (Map.singleton valueVarName value') subs

applySubst x (ScalarT b r p) = 
  let value' = Var (toSort b) x 
  in ScalarT b r $ substitute (Map.singleton valueVarName value') p

partitionType :: Bool 
              -> String 
              -> Environment 
              -> (String, RType)
              -> RType
              -> RType
              -> [Constraint]
partitionType cm l env (x, t@(ScalarT b _ f)) (ScalarT bl _ fl) (ScalarT br _ fr)
  = let env' = addAssumption (Var (toSort b) valueVarName |=| Var (toSort b) x) $ addVariable valueVarName t env
    in trace ("adding " ++ x ++ " :: " ++ show (plain (pretty t))) $ SharedForm env' f fl fr (x ++ " : " ++ l) : partitionBase cm l env (x, b) bl br

partitionBase cm l env (x, DatatypeT _ ts _) (DatatypeT _ tsl _) (DatatypeT _ tsr _)
  = concat $ zipWith3 (partitionType cm l env) (zip (repeat x) ts) tsl tsr
partitionBase cm l env (x, b@(TypeVarT _ _ m)) (TypeVarT _ _ ml) (TypeVarT _ _ mr) 
  = [SharedForm env m ml mr (x ++ " : " ++ l) | cm]
partitionBase _ _ _ _ _ _ = []


assertZeroPotential :: Monad s 
                    => Environment 
                    -> TCSolver s (PendingRSubst, Formula) 
assertZeroPotential env = do 
  let scalars = typeFromSchema <$> nonGhostScalars env 
  let topPotentials = Map.mapMaybe topPotentialOf
  let substitutions = Map.foldlWithKey generateSubst Map.empty scalars
  let fml = ((env ^. freePotential) |+| sumFormulas (topPotentials scalars)) |=| fzero
  return (substitutions, fml)

-- | 'directSubtypes' @env tl tr@ : Generate the set of all formulas in types @tl@ and @tr@, zipped by a binary operation @op@ on formulas 
directSubtypes :: Bool 
               -> (Formula -> Formula -> Formula) 
               -> RType 
               -> RType 
               -> [Formula]
directSubtypes cm op (ScalarT bl _ fl) (ScalarT br _ fr) = 
  {-(fl `op` fr) :-} directSubtypesBase cm op bl br
directSubtypes _ _ _ _ = [] 

directSubtypesBase :: Bool 
                  -> (Formula -> Formula -> Formula) 
                  -> BaseType Formula 
                  -> BaseType Formula 
                  -> [Formula]
directSubtypesBase cm op (DatatypeT _ tsl _) (DatatypeT _ tsr _) 
  = concat $ zipWith (directSubtypes cm op) tsl tsr
directSubtypesBase cm op (TypeVarT _ _ ml) (TypeVarT _ _ mr)     
  = [fml | cm && not (isTrivial fml)] 
    where fml = ml `op` mr
directSubtypesBase _ _ _ _ = []

totalTopLevelPotential :: RType -> Formula
totalTopLevelPotential (ScalarT base _ p) = p 
totalTopLevelPotential _                  = fzero

-- Is given constraint relevant for resource analysis
isResourceConstraint :: Constraint -> Bool
isResourceConstraint (Subtype _ ScalarT{} ScalarT{} _ _) = False-- True
isResourceConstraint RSubtype{}    = True
isResourceConstraint WellFormed{}  = True
isResourceConstraint SharedEnv{}   = False -- should never be present by now
isResourceConstraint SharedForm{}  = True
isResourceConstraint ConstantRes{} = True
isResourceConstraint Transfer{}    = True
isResourceConstraint _             = False

-- Return refinement of scalar type
refinementOf :: RType -> Formula 
refinementOf (ScalarT _ fml _) = fml
refinementOf _                 = error "error: Encountered non-scalar type when generating resource constraints"

-- | 'allUniversals' @env sch@ : set of all universally quantified resource formulas in the potential
--    annotations of the type @sch@
allUniversals :: Environment -> RSchema -> Set Formula
allUniversals env sch = getUniversals univSyms $ conjunction $ allRFormulas True $ typeFromSchema sch 
  where
    -- Include function argument variable names in set of possible universally quantified expressions
    univSyms = varsOfType (typeFromSchema sch) `Set.union` universalSyms env
    varsOfType ScalarT{}                 = Set.empty
    varsOfType (FunctionT x argT resT _) = Set.insert x (varsOfType argT `Set.union` varsOfType resT)

-- | 'getUniversals' @env f@ : return the set of universally quantified terms in formula @f@ given set of universally quantified symbols @syms@ 
getUniversals :: Set String -> Formula -> Set Formula
getUniversals syms (SetLit s fs)  = Set.unions $ map (getUniversals syms) fs
getUniversals syms v@(Var s x)    = Set.fromList [v | Set.member x syms || isValueVar x] 
  where 
    isValueVar ('_':'v':_) = True
    isValueVar _           = False
getUniversals syms (Unary _ f)    = getUniversals syms f
getUniversals syms (Binary _ f g) = getUniversals syms f `Set.union` getUniversals syms g
getUniversals syms (Ite f g h)    = getUniversals syms f `Set.union` getUniversals syms g `Set.union` getUniversals syms h
getUniversals syms (Pred _ _ fs)  = Set.unions $ map (getUniversals syms) fs 
getUniversals syms (Cons _ _ fs)  = Set.unions $ map (getUniversals syms) fs
getUniversals syms (All f g)      = getUniversals syms g
getUniversals _ _                 = Set.empty 

-- Filter away "uninteresting" constraints for logging. Specifically, well-formednes
-- Definitely not complete, just "pretty good"
isInteresting :: Formula -> Bool
isInteresting (Binary Ge (IntLit _) (IntLit 0)) = False
isInteresting (Binary Ge (Var _ _) (IntLit 0))  = False
isInteresting (Binary Implies _ f)     = isInteresting f 
isInteresting (BoolLit True)           = False
isInteresting (Binary And f g)         = isInteresting f || isInteresting g 
isInteresting _                        = True

getAnnotationStyle sch = getAnnotationStyle' $ typeFromSchema sch

getAnnotationStyle' t = 
  let rforms = conjunction $ allRFormulas True t
  in 
    case (varsOnly rforms, predsOnly rforms) of 
      (True, True)  -> Just Both 
      (False, True) -> Just Measure
      (True, _)     -> Just Variable
      _             -> Nothing

subtypeOp :: Monad s => TCSolver s (Formula -> Formula -> Formula)
subtypeOp = do 
  ct <- asks _constantRes 
  return $ if ct then (|=|) else (|>=|)

writeLog level msg = do 
  maxLevel <- asks _tcSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return ()