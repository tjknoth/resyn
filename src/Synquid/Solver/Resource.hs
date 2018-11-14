{-# LANGUAGE FlexibleContexts #-}

-- | Resource analysis
module Synquid.Solver.Resource (
  checkResources,
  allUniversals,
  allRFormulas,
  allRMeasures,
  --testCEGIS,
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
               => RType 
               -> [Constraint] 
               -> TCSolver s ()
checkResources _ [] = return ()
checkResources typ constraints = do 
  oldConstraints <- use resourceConstraints 
  tparams <- ask 
  let solve = solveResourceConstraints oldConstraints (filter isResourceConstraint constraints)
  newC <- solve 
  case newC of 
    Nothing -> throwError $ text "Insufficient resources"
    Just f  -> resourceConstraints %= (++ f) 

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
    let query = assembleQuery accFmls constraintList 
    -- Check satisfiability
    universals <- use universalFmls
    hasUniversals <- isJust <$> asks _cegisDomain
    b <- satisfyResources tempEnv (Set.toList universals) query
    let result = if b then "SAT" else "UNSAT"
    writeLog 5 $ nest 4 $ text "Accumulated resource constraints:" 
      $+$ prettyConjuncts (filter (isInteresting . rformula . constraint) accFmls)
    writeLog 3 $ nest 4 $ text "Solved resource constraint after conjoining formulas:" 
      <+> text result $+$ prettyConjuncts (filter (isInteresting . rformula . constraint) constraintList)
    if b 
      then 
        return $ Just $ map Left $ filter (not . isTrivialTC) constraintList -- $ Just $ if hasUniversals
          -- Store raw constraints
          -- then map Right constraints
          -- Otherwise, store TaggedConstraints with the appropriate formulas
          -- else map Left $ filter (not . isTrivialTC) constraintList
      else return Nothing


-- | Given lists of constraints (newly-generated and accumulated), construct the corresponding solver query
assembleQuery :: [TaggedConstraint] -> [TaggedConstraint] -> [RFormula]
assembleQuery accConstraints constraints = 
  let fmlList    = map constraint (filter (not . isTrivialTC) constraints)
      accFmlList = map constraint accConstraints
  in accFmlList ++ fmlList 

-- worth having a "constraint" typeclass?
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
  let assemble fs = conjunction (filter (not . isTrivial) fs) in
  case c of 
    Subtype env tl tr variant label -> do
      op <- subtypeOp
      let fmls = RFormula Map.empty $ assemble (directSubtypes checkMults op tl tr)
      -- When decomposing datatypes into subtyping constraints we already added _v to the context. Not true
      --   for other types. TODO: make this less janky (add a new class of constraint for doing the >= comparison)
      env' <- if isNothing (Map.lookup valueVarName (symbolsOfArity 0 env)) && not (isDataType (baseTypeOf tl))
                then safeAddGhostVar valueVarName tl env 
                else return env
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env' c fmls (Set.insert (refinementOf tl))
    WellFormed env t label -> do
      let fmls = RFormula Map.empty $ assemble $ map (|>=| fzero) $ allRFormulas checkMults t
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls (Set.insert (refinementOf t))
    SharedForm env f fl fr label -> do 
      let sharingFml = f |=| (fl |+| fr)  
      let wf = conjunction [f |>=| fzero, fl |>=| fzero, fr |>=| fzero]
      let fmls = RFormula Map.empty (wf |&| sharingFml)
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls id
    ConstantRes env label -> do 
      fml <- assertZeroPotential env
      TaggedConstraint ("CT: " ++ label) <$> embedAndProcessConstraint shouldLog env c fml id 
    Transfer env env' label -> do 
      (fmls, substs) <- redistribute env env' 
      let rfml = RFormula substs $ assemble fmls
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c rfml id
    _ -> error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c

-- | Embed the environment assumptions and preproess the constraint for solving 
embedAndProcessConstraint :: (MonadHorn s, RMonad s)
                          => Bool 
                          -> Environment 
                          -> Constraint 
                          -> RFormula
                          -> (Set Formula -> Set Formula) 
                          -> TCSolver s RFormula
embedAndProcessConstraint shouldLog env c rfml addTo = do 
  let fml = rformula rfml
  let substs = pendingSubsts rfml
  aDomain <- asks _cegisDomain
  -- If the top-level annotations do not contain measures,
  --   do not consider any assumptions over measures or any post conditions
  let useMeasures = maybe False shouldUseMeasures aDomain 
  univs <- use universalFmls
  let possibleVars = varsOf fml
  emb <- embedSynthesisEnv env (conjunction (Set.union univs possibleVars)) True useMeasures
  -- Check if embedding is singleton { false }
  let isFSingleton s = (Set.size s == 1) && (Set.findMin s == ffalse)
  if isFSingleton emb  
    then return $ RFormula Map.empty ftrue
    else do 
      let emb' = conjunction $ preprocessAssumptions $ Set.filter (isRelevantAssumption useMeasures univs) (addTo emb)
      let axioms = if useMeasures
          then conjunction $ instantiateConsAxioms env True Nothing emb'
          else ftrue
      let emb'' = emb' |&| axioms 
      --let instantiated = instantiateConsAxioms env True Nothing emb'
      noUnivs <- isNothing <$> asks _cegisDomain
      -- Only include implication if its nontrivial and there are no universally quantified expressions
      let finalFml = if (emb'' == ftrue) || noUnivs then fml else emb'' |=>| fml
      when shouldLog $ writeLog 3 (nest 4 $ pretty c $+$ text "Gives numerical constraint" <+> pretty finalFml)
      return $ RFormula substs finalFml

-- Filter out irrelevant assumptions -- might be measures, and 
--   any operation over a non-integer variable
isRelevantAssumption :: Bool -> Set Formula -> Formula -> Bool 
isRelevantAssumption _ rvs v@Var{} = Set.member v rvs
isRelevantAssumption useM _ Pred{} = useM 
isRelevantAssumption _ _ Unknown{} = trace "Warning: unknown assumption" False -- TODO: fix once i start assuming unknowns
isRelevantAssumption useM rvs (Unary _ f) = isRelevantAssumption useM rvs f
isRelevantAssumption useM rvs (Binary _ f g) = isRelevantAssumption useM rvs f && isRelevantAssumption useM rvs g
isRelevantAssumption useM rvs (Ite f g h) = isRelevantAssumption useM rvs f && isRelevantAssumption useM rvs g && isRelevantAssumption useM rvs h
isRelevantAssumption useM _ Cons{} = useM
isRelevantAssumption useM _ All{} = trace "Warning: universally quantified assumption" True
isRelevantAssumption _ _ _ = True


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
      -- Gather data types and their constructors
      let dts = filter (`notElem` setConstructors) $ concatMap _constructors 
              $ Map.elems $ env^.datatypes
      -- This is ugly currently: need to zip the names twice because of how the UF instances are designed
      let cons = zip dts $ zip (repeat env) dts
      let allUniversals = Universals universalsWithVars uMeasures cons
      writeLog 3 $ text "Solving resource constraint with CEGIS:" 
      writeLog 5 $ pretty $ conjunction $ map rformula rfmls
      writeLog 3 $ text "Over universally quantified expressions:" <+> hsep (map (pretty . snd) universalsWithVars)
      solveWithCEGIS cMax rfmls ass allUniversals [] allPolynomials initialProgram 

shouldUseMeasures  ad = case ad of 
    Variable -> False 
    _ -> True 
-- CEGIS test harness
-- If this is going to work with measures, need a way to parse measures, etc
--   or just manually instantiate cons axioms
{-
testCEGIS :: RMonad s => Formula -> RSolver s Bool
testCEGIS fml = do 
  let fml' = adjustSorts fml
  let universals = map (Var IntS) ["n", "x11"]
  let rVars = ["p0", "p1"]
  let aDomain = Variable
  let uMeasures = []
  let env = emptyEnv
  -- max number of iterations through the CEGIS loop
  let maxIterations = length universals + 10
  let init rv = initializePolynomial env aDomain universals uMeasures
  let allPolynomials = zip rVars $ map init rVars
  let allCoefficients = concatMap (coefficientsOf . snd) allPolynomials
  let initialProgram = Map.fromList $ zip allCoefficients initialCoefficients 
  let universalsWithVars = formatUniversals universals 
  let ctors = []
  let measures = []
  let allUniversals = Universals universalsWithVars measures ctors
  let ass = conjunction $ map (|>=| fzero) (possibleMeasureApps env universals uMeasures)
  writeLog 3 $ linebreak </> text "Solving resource constraint with CEGIS:" <+> pretty fml' 
    <+> text "Over universally quantified expressions:" <+> pretty (map snd universalsWithVars)
  lift $ solveWithCEGIS maxIterations fml' ass allUniversals [] (Map.fromList allPolynomials) initialProgram
-}

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
  let substitutions e = Map.foldlWithKey generateSubst Map.empty (scalarsOf e)
  -- Sum of all top-level potentials of scalar types in context
  let envSum env = sumFormulas $ topPotentials $ scalarsOf env
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
      Just p -> 
        case toSort (baseTypeOf t) of 
          IntS -> let value' = Var (toSort (baseTypeOf t)) x 
                  in Map.insert p (Map.singleton valueVarName value') subs
          _ -> subs

partitionType :: Bool 
              -> String 
              -> Environment 
              -> RType 
              -> RType 
              -> RType 
              -> [Constraint]
partitionType cm l env t@(ScalarT b _ f) (ScalarT bl _ fl) (ScalarT br _ fr) 
  = let env' = addVariable valueVarName t env
    in SharedForm env' f fl fr l : partitionBase cm l env b bl br

partitionBase cm l env (DatatypeT _ ts _) (DatatypeT _ tsl _) (DatatypeT _ tsr _)
  = concat $ zipWith3 (partitionType cm l env) ts tsl tsr
partitionBase cm l env b@(TypeVarT _ _ m) (TypeVarT _ _ ml) (TypeVarT _ _ mr) 
  = [SharedForm env m ml mr l | cm]
partitionBase _ _ _ _ _ _ = []


assertZeroPotential :: Monad s 
                    => Environment 
                    -> TCSolver s RFormula
assertZeroPotential env = do 
  let scalars = typeFromSchema <$> nonGhostScalars env 
  let topPotentials = Map.mapMaybe topPotentialOf
  let substitutions = Map.foldlWithKey generateSubst Map.empty scalars
  let fml = ((env ^. freePotential) |+| sumFormulas (topPotentials scalars)) |=| fzero
  return $ RFormula substitutions fml 

-- | 'directSubtypes' @env tl tr@ : Generate the set of all formulas in types @tl@ and @tr@, zipped by a binary operation @op@ on formulas 
directSubtypes :: Bool 
               -> (Formula -> Formula -> Formula) 
               -> RType 
               -> RType 
               -> [Formula]
directSubtypes cm op (ScalarT bl _ fl) (ScalarT br _ fr) = 
  (fl `op` fr) : directSubtypesBase cm op bl br
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
isResourceConstraint (Subtype _ _ _ True _) = False -- don't care about consistency checks
isResourceConstraint (Subtype _ ScalarT{} ScalarT{} _ _) = True
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

-- | 'preprocessAssumptions' @fmls@ : eliminate assumptions that contain unknown predicates 
--    temporary only -- this is incomplete
preprocessAssumptions :: Set Formula -> Set Formula 
preprocessAssumptions = Set.filter (not . isUnknownForm)

assumeUnknowns :: Formula -> Formula
assumeUnknowns u@(Unknown s id)  = BoolLit True
assumeUnknowns (SetLit s fs)     = SetLit s (map assumeUnknowns fs)
assumeUnknowns (Unary op f)      = Unary op (assumeUnknowns f)
assumeUnknowns (Binary op fl fr) = Binary op (assumeUnknowns fl) (assumeUnknowns fr)
assumeUnknowns (Ite g t f)       = Ite (assumeUnknowns g) (assumeUnknowns t) (assumeUnknowns f)
assumeUnknowns (Pred s x fs)     = Pred s x (map assumeUnknowns fs)
assumeUnknowns (Cons s x fs)     = Cons s x (map assumeUnknowns fs)
assumeUnknowns (All f g)         = All (assumeUnknowns f) (assumeUnknowns g)
assumeUnknowns f                 = f

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

-- Substitute variable for a formula (predicate application or variable) in given formula @fml@
substituteForFml :: Formula -> Formula -> Formula -> Formula
substituteForFml new old v@Var{} = if v == old then new else v
substituteForFml new old (Unary op f) = Unary op (substituteForFml new old f)
substituteForFml new old (Binary op f g) = Binary op (substituteForFml new old f) (substituteForFml new old g)
substituteForFml new old (Ite f g h) = Ite (substituteForFml new old f) (substituteForFml new old g) (substituteForFml new old h)
substituteForFml new old p@(Pred s x fs) = 
  if p == old 
    then new
    else Pred s x $ map (substituteForFml new old) fs
substituteForFml new old (Cons s x fs) = Cons s x $ map (substituteForFml new old) fs
substituteForFml new old (All f g) = All f (substituteForFml new old g)
substituteForFml _ _ f = f

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