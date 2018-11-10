{-# LANGUAGE FlexibleContexts #-}

-- | Resource analysis
module Synquid.Solver.Resource (
  checkResources,
  allUniversals,
  allRFormulas,
  allRMeasures,
  testCEGIS,
  shareEnv,
  getAnnotationStyle
) where

import Synquid.Logic 
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Solver.Monad
import Synquid.Pretty
import Synquid.Solver.Util hiding (writeLog)
import Synquid.Solver.CEGIS 

import Data.Maybe
import qualified Data.Set as Set 
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Lens
import Debug.Trace

-- Read current type under consideration
type RSolver s = ReaderT RType (TCSolver s) 

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
  newC <- runReaderT solve typ
  case newC of 
    Nothing -> throwError $ text "Insufficient resources"
    Just f  -> resourceConstraints %= (++ f) 

-- | 'solveResourceConstraints' @oldConstraints constraints@ : Transform @constraints@ into logical constraints and attempt to solve the complete system by conjoining with @oldConstraints@
solveResourceConstraints :: RMonad s => [RConstraint] -> [Constraint] -> RSolver s (Maybe [RConstraint]) 
solveResourceConstraints _ [] = return $ Just [] 
solveResourceConstraints oldConstraints constraints = do
    writeLog 3 $ linebreak <+> text "Generating resource constraints:"
    checkMults <- lift $ asks _checkMultiplicities
    -- Need environment to determine which annotation formulas are universally quantified
    let tempEnv = envFrom $ head constraints
    -- Need initial environment to get possible constant arguments for measures
    --  For some reason, we can't use tempEnv here, often the measureConstArgs will not be initialized
    iEnv <- lift $ use initEnv
    -- Check for new universally quantified expressions
    universals <- fromMaybe Set.empty <$> use universalFmls
    -- Generate numerical resource-usage formulas from typing constraints:
    constraintList <- mapM (generateFormula True universals . Right) constraints
    accFmls <- mapM (generateFormula False universals) oldConstraints
    universals' <- updateUniversals tempEnv $ conjunction (map constraint constraintList) 
    let query = assembleQuery accFmls constraintList 
    -- Check satisfiability
    b <- satisfyResources iEnv (Set.toList universals') query
    let result = if b then "SAT" else "UNSAT"
    writeLog 5 $ nest 4 $ text "Accumulated resource constraints:" 
      $+$ prettyConjuncts (filter (isInteresting . constraint) accFmls)
    writeLog 3 $ nest 4 $ text "Solved resource constraint after conjoining formulas:" 
      <+> text result $+$ prettyConjuncts (filter (isInteresting . constraint) constraintList)
    if b 
      then 
        return $ Just $ if null universals
          -- Store raw constraints
          then map Right constraints
          -- Otherwise, store TaggedConstraints with the appropriate formulas
          else map Left $ filter (not . isTrivialTC) constraintList
      else return Nothing


-- | Given lists of constraints (newly-generated and accumulated), construct the corresponding solver query
assembleQuery :: [TaggedConstraint] -> [TaggedConstraint] -> Formula 
assembleQuery accConstraints constraints = 
  let fmlList    = map constraint (filter (not . isTrivialTC) constraints)
      accFmlList = map constraint accConstraints
  in conjunction $ accFmlList ++ fmlList 

-- worth having a "constraint" typeclass?
isTrivialTC (TaggedConstraint _ f) = isTrivial f

-- | 'generateFormula' @c@: convert constraint @c@ into a logical formula
--    If there are no universal quantifiers, we can cache the generated formulas (the Left case)
--    Otherwise, we must re-generate every time
generateFormula :: RMonad s => Bool -> Set Formula -> RConstraint -> RSolver s TaggedConstraint
generateFormula _ _ (Left tc) = return tc
generateFormula shouldLog univs (Right c) = do 
  currentType <- ask
  checkMults <- lift $ asks _checkMultiplicities
  if isScalarType currentType
    -- Scalar type: potential name clashes with _v, rename instances
    then do 
      let valueVarSort = toSort $ baseTypeOf currentType
      (TaggedConstraint x fml) <- generateFormula' shouldLog checkMults univs c
      TaggedConstraint x <$> lift (freshValueVars fml valueVarSort)
    -- Function type: proceed as usual
    else generateFormula' shouldLog checkMults univs c

generateFormula' :: RMonad s 
                 => Bool 
                 -> Bool 
                 -> Set Formula 
                 -> Constraint 
                 -> RSolver s TaggedConstraint 
generateFormula' shouldLog checkMults univs c = 
  let assemble fs = conjunction $ filter (not . isTrivial) fs in
  case c of 
    Subtype env tl tr variant label -> do
      op <- subtypeOp
      let fmls = assemble $ directSubtypes checkMults op tl tr
      let relevantFml = conjunction $ univs `Set.union` allFormulasOf checkMults tl 
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls relevantFml (Set.insert (refinementOf tl))
    WellFormed env t label -> do
      let fmls = assemble $ map (|>=| fzero) $ allRFormulas checkMults t
      let relevantFml = conjunction $ univs `Set.union` allFormulasOf checkMults t
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls relevantFml (Set.insert (refinementOf t))
    SharedEnv env envl envr label -> do 
      let fmls = assemble $ shareEnv checkMults env envl envr
      let relevantFml = conjunction univs -- TODO: need more stuff here?
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls relevantFml id
    ConstantRes env label -> do 
      let fml = assertZeroPotential env
      let relevantFml = conjunction univs 
      TaggedConstraint ("CT: " ++ label) <$> embedAndProcessConstraint shouldLog env c fml relevantFml id 
    Transfer env env' label -> do 
      let fml = assemble $ redistribute env env' 
      let relevantFml = conjunction univs 
      TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fml relevantFml id
    _ -> error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c

-- | Embed the environment assumptions and preproess the constraint for solving 
embedAndProcessConstraint :: RMonad s
                          => Bool 
                          -> Environment 
                          -> Constraint 
                          -> Formula 
                          -> Formula 
                          -> (Set Formula -> Set Formula) 
                          -> RSolver s Formula
embedAndProcessConstraint shouldLog env c fmls relevantFml addTo = do 
  emb <- lift $ embedSynthesisEnv env relevantFml True
  --writeLog 3 $ text "EMBEDDING" <+> pretty emb
  -- Check if embedding is singleton { false }
  let isFSingleton s = (Set.size s == 1) && (Set.findMin s == ffalse)
  if isFSingleton emb  
    then return ftrue
    else do 
      let emb' = conjunction $ preprocessAssumptions $ addTo emb
      let axioms = conjunction $ instantiateConsAxioms env True Nothing emb'
      let emb'' = emb' |&| axioms 
      --let instantiated = instantiateConsAxioms env True Nothing emb'
      needsEmb <- isJust <$> use universalFmls
      -- Only include implication if its nontrivial and there are no universally quantified expressions
      let finalFml = if (emb'' == ftrue) || not needsEmb then fmls else emb'' |=>| fmls
      when shouldLog $ writeLog 3 (nest 4 $ pretty c $+$ text "Gives numerical constraint" <+> pretty finalFml)
      return finalFml

-- | Check the satisfiability of the generated resource constraints, instantiating universally 
--     quantified expressions as necessary.
satisfyResources :: RMonad s 
                 => Environment 
                 -> [Formula] 
                 -> Formula 
                 -> RSolver s Bool
satisfyResources env universals fml = do 
  shouldInstantiate <- lift $ asks _instantiateUnivs
  if null universals || not shouldInstantiate
    then do 
      model <- lift . lift . lift . lift $ solveAndGetModel fml
      case model of 
        Nothing -> return False
        Just m' -> do 
          writeLog 6 $ nest 2 (text "Solved with model") </> nest 6 (text (snd m'))
          return True 
    else do
      cParams <- lift $ asks _cegisParams
      -- Unsafe, but should be OK since we already checked that universals are non-null
      let aDomain = fromJust $ annotationDomain cParams
      rVars <- Set.toList <$> use resourceVars
      -- Construct list of universally quantified expressions, storing the formula with a string representation
      let universalsWithVars = formatUniversals universals 
      uMeasures <- Map.assocs <$> use resourceMeasures
      -- Initialize polynomials for each resource variablea
      let init = initializePolynomial env aDomain universals uMeasures
      let allPolynomials = zip rVars $ map init rVars
      -- List of all coefficients in the list of all polynomials
      let allCoefficients = concatMap (coefficientsOf . snd) allPolynomials
      -- Initialize all coefficient values -- the starting value should not matter
      let initialProgram = Map.fromList $ zip allCoefficients initialCoefficients 
      -- Assume that all measure applications are well-formed:
      let ass = conjunction $ map (|>=| fzero) (possibleMeasureApps env universals uMeasures)
      writeLog 3 $ text "Solving resource constraint with CEGIS:" 
      writeLog 5 $ pretty fml
      writeLog 3 $ text "Over universally quantified expressions:" <+> pretty (map universalFml universalsWithVars)
      lift $ solveWithCEGIS (numIterations cParams) fml ass universalsWithVars uMeasures [] (Map.fromList allPolynomials) initialProgram 

-- CEGIS test harness
-- If this is going to work with measures, need a way to parse measures, etc
--   or just manually instantiate cons axioms
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
  let init = initializePolynomial env aDomain universals uMeasures
  let allPolynomials = zip rVars $ map init rVars
  let allCoefficients = concatMap (coefficientsOf . snd) allPolynomials
  let initialProgram = Map.fromList $ zip allCoefficients initialCoefficients 
  let universalsWithVars = formatUniversals universals 
  let ass = conjunction $ map (|>=| fzero) (possibleMeasureApps env universals uMeasures)
  writeLog 3 $ linebreak </> text "Solving resource constraint with CEGIS:" <+> pretty fml' 
    <+> text "Over universally quantified expressions:" <+> pretty (map universalFml universalsWithVars)
  lift $ solveWithCEGIS maxIterations fml' ass universalsWithVars [] [] (Map.fromList allPolynomials) initialProgram


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
redistribute :: Environment -> Environment -> [Formula]
redistribute envIn envOut = 
  let fpIn  = _freePotential envIn 
      fpOut = _freePotential envOut 
      -- All (non-ghost) scalar types 
      scalarsOf env = typeFromSchema <$> nonGhostScalars env
      -- All top-level potential annotations of a map of scalar types
      topPotentials = Map.mapMaybe topPotentialOf
      -- Sum of all top-level potentials of scalar types in context
      envSum env = sumFormulas $ topPotentials $ scalarsOf env
      -- Assert that all potentials are well-formed
      wellFormed smap = map (|>=| fzero) ((Map.elems . topPotentials) smap) 
      -- Assert (fresh) potentials in output context are well-formed
      wellFormedAssertions = (fpIn |>=| fzero) : (fpOut |>=| fzero) : wellFormed (scalarsOf envOut) 
      --Assert that top-level potentials are re-partitioned
      transferAssertions = (envSum envIn |+| fpIn) |=| (envSum envOut |+| fpOut)
  in transferAssertions : wellFormedAssertions


-- Generate sharing constraints between a 3-tuple of contexts
shareEnv :: Bool -> Environment -> Environment -> Environment -> [Formula]
shareEnv checkMults env envl envr = 
  (fpPartition : concat allPartitions) ++ wf
  where
    fpl = _freePotential envl
    fpr = _freePotential envr
    fpPartition = _freePotential env |=| (fpl |+| fpr)
    scalars = map typeFromSchema $ Map.elems $ nonGhostScalars env 
    scalarsl = map typeFromSchema $ Map.elems $ nonGhostScalars envl
    scalarsr = map typeFromSchema $ Map.elems $ nonGhostScalars envr
    allPartitions = zipWith3 (partition checkMults) scalars scalarsl scalarsr 
    allRFormsL = concatMap (allRFormulas True) scalarsl 
    allRFormsR = concatMap (allRFormulas True) scalarsr
    wf = map (|>=| fzero) (fpl : fpr : allRFormsL ++ allRFormsR)

-- | 'partition' @t tl tr@ : Generate numerical constraints referring to a partition of the resources associated with @t@ into types @tl@ and @tr@ 
partition :: Bool -> RType -> RType -> RType -> [Formula]
partition cm t@(ScalarT b _ f) (ScalarT bl _ fl) (ScalarT br _ fr)
  = (f |=| (fl |+| fr)) : partitionBase cm b bl br
partition _ _ _ _ = []

partitionBase :: Bool -> BaseType Formula -> BaseType Formula -> BaseType Formula -> [Formula]
partitionBase cm (DatatypeT _ ts _) (DatatypeT _ tsl _) (DatatypeT _ tsr _) 
  = concat $ zipWith3 (partition cm) ts tsl tsr
partitionBase cm (TypeVarT _ _ m) (TypeVarT _ _ ml) (TypeVarT _ _ mr) 
  = [m |=| (ml |+| mr) | cm] 
partitionBase _ _ _ _ = [] 

assertZeroPotential :: Environment -> Formula
assertZeroPotential env = ((env ^. freePotential) |+| sumFormulas (fmap totalTopLevelPotential scalars)) |=| fzero
  where 
    scalars = typeFromSchema <$> nonGhostScalars env 

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
isResourceConstraint SharedEnv{}   = True
isResourceConstraint ConstantRes{} = True
isResourceConstraint Transfer{}    = True
isResourceConstraint _             = False

-- Return refinement of scalar type
refinementOf :: RType -> Formula 
refinementOf (ScalarT _ fml _) = fml
refinementOf _                 = error "error: Encountered non-scalar type when generating resource constraints"

-- | 'preprocessAssumptions' @fmls@ : eliminate assumptions that contain unknown predicates
preprocessAssumptions :: Set Formula -> Set Formula 
preprocessAssumptions fs = Set.map assumeUnknowns $ Set.filter (not . isUnknownForm) fs

-- Remove any clauses containing a data type or measure application (temporarily, to implement CEGIS over numeric variables)
removeDTs ms = Set.filter (not . containsDT ms)

-- Assume that unknown predicates in a formula evaluate to True
-- TODO: probably don't need as many cases
assumeUnknowns :: Formula -> Formula
assumeUnknowns (Unknown s id)    = BoolLit True
assumeUnknowns (SetLit s fs)     = SetLit s (map assumeUnknowns fs)
assumeUnknowns (Unary op f)      = Unary op (assumeUnknowns f)
assumeUnknowns (Binary op fl fr) = Binary op (assumeUnknowns fl) (assumeUnknowns fr)
assumeUnknowns (Ite g t f)       = Ite (assumeUnknowns g) (assumeUnknowns t) (assumeUnknowns f)
assumeUnknowns (Pred s x fs)     = Pred s x (map assumeUnknowns fs)
assumeUnknowns (Cons s x fs)     = Cons s x (map assumeUnknowns fs)
assumeUnknowns (All f g)         = All (assumeUnknowns f) (assumeUnknowns g)
assumeUnknowns f                 = f

-- | Check for new universally quantified expressions, persisting the update
updateUniversals :: Monad s => Environment -> Formula -> RSolver s (Set Formula)
updateUniversals env fml = do 
  accUnivs <- use universalFmls
  case accUnivs of 
    Nothing -> return Set.empty
    Just us -> do 
      let newUniversals = getUniversals (universalSyms env) fml
      let universals' = us `Set.union` newUniversals
      universalFmls .= Just universals'
      return universals'

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

-- | containsDT @ms f@ : return whether or not formula @f@ includes a measure (or a data type in general), the names of which are in @ms@
containsDT :: [String] -> Formula -> Bool
containsDT _  (Var _ x)          = x == valueVarName
containsDT ms (Pred _ name args) = (name `elem` ms) || any (containsDT ms) args
containsDT _  Cons{}             = True 
containsDT ms (Unary _ f)        = containsDT ms f
containsDT ms (Binary _ f g)     = containsDT ms f || containsDT ms g
containsDT ms (Ite f g h)        = containsDT ms f || containsDT ms g || containsDT ms h
containsDT ms (All f g)          = containsDT ms f || containsDT ms g
containsDT ms (SetLit _ fs)      = any (containsDT ms) fs
containsDT _ _                   = False
        
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

subtypeOp :: Monad s => RSolver s (Formula -> Formula -> Formula)
subtypeOp = do 
  ct <- lift $ asks _constantRes 
  return $ if ct then (|=|) else (|>=|)

writeLog level msg = do 
  maxLevel <- lift $ asks _tcSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return ()