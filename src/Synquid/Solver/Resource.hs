{-# LANGUAGE FlexibleContexts #-}

-- | Resource analysis
module Synquid.Solver.Resource (
  checkResources,
  allUniversals,
  testCEGIS
) where

import Synquid.Logic 
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Solver.Monad
import Synquid.Pretty
import Synquid.Error
import Synquid.Solver.Util hiding (writeLog)
import Synquid.Solver.CEGIS 

import Data.Maybe
import Data.List hiding (partition)
import qualified Data.Set as Set 
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Reader
import Control.Lens
import Debug.Trace

-- Read current type under consideration
type RSolver s = ReaderT RType (TCSolver s) 

{- Implementation -}

-- | Check resource bounds: attempt to find satisfying expressions for multiplicity and potential annotations 
checkResources :: (MonadHorn s, MonadSMT s) => RType -> [Constraint] -> TCSolver s ()
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
solveResourceConstraints :: MonadSMT s => [RConstraint] -> [Constraint] -> RSolver s (Maybe [RConstraint]) 
solveResourceConstraints oldConstraints constraints = do
    writeLog 3 $ linebreak <+> text "Generating resource constraints:"
    checkMults <- lift $ asks _checkMultiplicities
    containsUnivs <- isNothing <$> use universalFmls 
    -- Need environment to determine which annotation formulas are universally quantified
    let tempEnv = case constraints of
          [] -> emptyEnv 
          cs -> envFrom $ head cs
    -- Check for new universally quantified expressions
    universals <- updateUniversals tempEnv $ conjunction $ concatMap (concatMap (allRFormulas checkMults) . typesFrom) constraints
    -- Generate numerical resource-usage formulas from typing constraints:
    constraintList <- mapM (generateFormula True universals . Right) constraints
    accFmls <- mapM (generateFormula False universals) oldConstraints
    let query = assembleQuery accFmls constraintList 
    -- Check satisfiability
    b <- satisfyResources (Set.toList universals) query
    let result = if b then "SAT" else "UNSAT"
    writeLog 5 $ nest 4 $ text "Accumulated resource constraints:" 
      $+$ prettyConjuncts (filter (isInteresting . constraint) accFmls)
    writeLog 3 $ nest 4 $ text "Solved resource constraint after conjoining formulas:" 
      <+> text result $+$ prettyConjuncts (filter (isInteresting . constraint) constraintList)
    if b 
      then 
        return $ Just $ if containsUnivs 
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

isTrivialTC (TaggedConstraint _ f) = isTrivial f

-- | 'generateFormula' @c@: convert constraint @c@ into a logical formula
--    If there are no universal quantifiers, we can cache the generated formulas (the Left case)
--    Otherwise, we must re-generate every time
generateFormula :: MonadSMT s => Bool -> Set Formula -> RConstraint -> RSolver s TaggedConstraint
generateFormula _ _ (Left tc)                      = return tc
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

generateFormula' :: MonadSMT s => Bool -> Bool -> Set Formula -> Constraint -> RSolver s TaggedConstraint 
generateFormula' shouldLog checkMults univs c@(Subtype env syms tl tr variant label) = do
  tass <- use typeAssignment
  let fmls = conjunction $ filter (not . isTrivial) $ case variant of 
        Nondeterministic -> assertSubtypes env syms tass checkMults tl tr
        _                -> directSubtypes checkMults tl tr
  let relevantFml = conjunction $ univs `Set.union` allFormulasOf checkMults tl `Set.union` allFormulasOf checkMults tr
  TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls relevantFml (Set.insert (refinementOf tl))
generateFormula' shouldLog checkMults univs c@(WellFormed env t label) = do
  let fmls = conjunction $ filter (not . isTrivial) $ map (|>=| fzero)  $ allRFormulas checkMults t
  let relevantFml = conjunction $ univs `Set.union` allFormulasOf checkMults t
  TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls relevantFml (Set.insert (refinementOf t))
generateFormula' shouldLog checkMults univs c@(SharedType env t tl tr label) = do 
  let fmls = conjunction $ partition checkMults t tl tr
  let relevantFml = conjunction $ univs `Set.union` allFormulasOf checkMults t 
  TaggedConstraint label <$> embedAndProcessConstraint shouldLog env c fmls relevantFml id
generateFormula' shouldLog checkMults univs c@(ConstantRes env label) = do 
  tass <- use typeAssignment
  let fml = assertZeroPotential checkMults tass env
  let relevantFml = conjunction univs 
  TaggedConstraint ("CT: " ++ label) <$> embedAndProcessConstraint shouldLog env c fml relevantFml id 
generateFormula' _ _ _ c = error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c

-- | Embed the environment assumptions and preproess the constraint for solving 
embedAndProcessConstraint :: MonadSMT s => Bool -> Environment -> Constraint -> Formula -> Formula -> (Set Formula -> Set Formula) -> RSolver s Formula
embedAndProcessConstraint shouldLog env c fmls relevantFml addTo = do 
  emb <- lift $ embedSynthesisEnv env relevantFml True
  -- Check if embedding is singleton { false }
  let isFSingleton s = (Set.size s == 1) && (Set.findMin s == ffalse)
  if isFSingleton emb  
    then return ftrue
    else do 
      -- As well as preprocessing to assume all unknowns, remove anything containing a datatype
      --  this is only temporary to develop CEGIS for numeric variables first. 
      let emb' = conjunction $ removeDTs (Map.keys (_measures env)) $ preprocessAssumptions $ addTo emb
      needsEmb <- isJust <$> use universalFmls
      -- Only include implication if its nontrivial and there are no universally quantified expressions
      let finalFml = if (emb' == ftrue) || not needsEmb then fmls else emb' |=>| fmls
      when shouldLog $ writeLog 3 (nest 4 $ pretty c $+$ text "Gives numerical constraint" <+> pretty finalFml)
      return finalFml

-- | Check the satisfiability of the generated resource constraints, instantiating universally 
--     quantified expressions as necessary.
satisfyResources :: MonadSMT s => [Formula] -> Formula -> RSolver s Bool
satisfyResources universals fml = do 
  shouldInstantiate <- lift $ asks _instantiateUnivs
  if null universals || not shouldInstantiate
    then do 
      (b, s) <- lift $ isSatWithModel fml
      writeLog 6 $ nest 2 (text "Solved with model") </> nest 6 (text s)
      return b
    else do
      maxIterations <- lift $ asks _cegisMax
      rVars <- Set.toList <$> use resourceVars
      -- Generate list of polynomial coefficients, 1 for each universally quantified expression and a constant term
      let constantTerm s = PolynomialTerm (constPolynomialVar s) Nothing
      -- Initialize all coefficients to zero (shouldn't matter what value is used)
      let polynomial s = constantTerm s : map (makePTerm s) universals
      -- Initialize polynomials for each resource variable
      let allPolynomials = zip rVars (map polynomial rVars)
      -- List of all coefficients in the list of all polynomials
      let allCoefficients = concatMap (coefficientsOf . snd) allPolynomials
      -- Initialize all coefficient values -- the starting value should not matter
      let initialProgram = Map.fromList $ zip allCoefficients (repeat (IntLit 0))
      -- Construct list of universally quantified expressions, storing the formula with a string representation
      let universalsWithVars = map Universal $ zip (map universalToString universals) universals
      writeLog 3 $ text "Solving resource constraint with CEGIS:" 
      writeLog 5 $ pretty fml
      writeLog 3 $ text "Over universally quantified expressions:" <+> pretty (map universalFml universalsWithVars)
      lift $ solveWithCEGIS maxIterations fml universalsWithVars [] (Map.fromList allPolynomials) initialProgram 

-- CEGIS test harness
testCEGIS :: MonadSMT s => Formula -> RSolver s Bool
testCEGIS fml = do 
  let fml' = adjustSorts fml
  let universals = map (Var IntS) ["n", "x11"]
  let rVars = ["p0", "p1"]
  -- max number of iterations through the CEGIS loop
  let maxIterations = length universals + 10
  let constantTerm s = PolynomialTerm (constPolynomialVar s) Nothing
  let polynomial s = constantTerm s : map (makePTerm s) universals
  let allPolynomials = zip rVars (map polynomial rVars)
  let allCoefficients = concatMap (coefficientsOf . snd) allPolynomials
  let initialProgram = Map.fromList $ zip allCoefficients (repeat (IntLit 0))
  let universalsWithVars = map Universal $ zip (map universalToString universals) universals
  writeLog 3 $ linebreak </> text "Solving resource constraint with CEGIS:" <+> pretty fml' 
    <+> text "Over universally quantified expressions:" <+> pretty (map universalFml universalsWithVars)
  lift $ solveWithCEGIS maxIterations fml' universalsWithVars [] (Map.fromList allPolynomials) initialProgram

-- constant term in resource polynomial    
constPolynomialVar s = s ++ "CONST"

adjustSorts (BoolLit b) = BoolLit b
adjustSorts (IntLit b) = IntLit b
adjustSorts (Var _ x) = Var IntS x
adjustSorts (Binary op f g) = Binary op (adjustSorts f) (adjustSorts g)
adjustSorts (Unary op f) = Unary op (adjustSorts f)

-- | 'allRFormulas' @t@ : return all resource-related formulas (potentials and multiplicities) from a refinement type @t@
allRFormulas :: Bool -> RType -> [Formula]
allRFormulas cm (FunctionT _ argT resT _) = allRFormulas cm argT ++ allRFormulas cm resT
allRFormulas cm (ScalarT base _ Infty)    = allRFormulasBase cm base
allRFormulas cm (ScalarT base _ (Fml p))  = p : allRFormulasBase cm base
allRFormulas _ _                          = [] 

allRFormulasBase :: Bool -> BaseType Formula -> [Formula]
allRFormulasBase cm (DatatypeT _ ts _)     = concatMap (allRFormulas cm) ts
allRFormulasBase _  (TypeVarT _ _ Infty)   = []
allRFormulasBase cm (TypeVarT _ _ (Fml m)) = [m | cm] 
allRFormulasBase _ _                       = []

-- | 'partition' @t tl tr@ : Generate numerical constraints referring to a partition of the resources associated with @t@ into types @tl@ and @tr@ 
partition :: Bool -> RType -> RType -> RType -> [Formula]
partition cm (ScalarT b _ Infty) (ScalarT bl _ Infty) (ScalarT br _ Infty) 
  = partitionBase cm b bl br
partition cm (ScalarT b _ (Fml f)) (ScalarT bl _ (Fml fl)) (ScalarT br _ (Fml fr)) 
  = (f |=| (fl |+| fr)) : partitionBase cm b bl br
partition _ _ _ _ = [] 

partitionBase :: Bool -> BaseType Formula -> BaseType Formula -> BaseType Formula -> [Formula]
partitionBase cm (DatatypeT _ ts _) (DatatypeT _ tsl _) (DatatypeT _ tsr _) 
  = concat $ zipWith3 (partition cm) ts tsl tsr
partitionBase _  (TypeVarT _ _ Infty) (TypeVarT _ _ Infty) (TypeVarT _ _ Infty)
  = []
partitionBase cm (TypeVarT _ _ (Fml m)) (TypeVarT _ _ (Fml ml)) (TypeVarT _ _ (Fml mr)) 
  = [m |=| (ml |+| mr) | cm] 
partitionBase _ _ _ _ = [] 

assertZeroPotential :: Bool -> TypeSubstitution -> Environment -> Formula
assertZeroPotential cm tass env = sumFormulas (fmap totalTopLevelPotential scalars) |=| fzero
  where 
    scalars = fmap (typeSubstitute tass . typeFromSchema) rawScalars
    rawScalars = Map.filterWithKey notEmptyCtor (symbolsOfArity 0 env) 
    notEmptyCtor x _ = Set.notMember x (_emptyCtors env) 

-- | 'assertSubtypes' @env tl tr@ : Generate formulas partitioning potential appropriately amongst
--    environment @env@ in order to check @tl@ <: @tr@
assertSubtypes :: Environment -> SymbolMap -> TypeSubstitution -> Bool -> RType -> RType -> [Formula]
assertSubtypes env syms tass cm tl@(ScalarT bl _ pl) tr@(ScalarT br _ pr) = 
  let -- Get map of only scalar types (excluding empty type constructors) in environment:
      scalarsOf smap = Map.filterWithKey notEmptyCtor $ fmap typeFromSchema $ fromMaybe Map.empty $ Map.lookup 0 smap
      -- Get top-level potentials from environment, after applying current type substitutions
      topPotentials = Map.mapMaybe (topPotentialFml . typeSubstitute tass) 
      -- Sum all top-level potential in an environment:
      envSum smap = sumFormulas $ topPotentials $ scalarsOf smap
      -- Assert that types in fresh context are well-formed (w.r.t top-level annotations)
      wellFormed smap = map (|>=| fzero) ((Map.elems . topPotentials) smap) 
      wellFormedAssertions = wellFormed $ scalarsOf syms
      -- True if the given variable is not an empty constructor for some data type
      notEmptyCtor x _ = Set.notMember x (_emptyCtors env) 
  in case (pl, pr) of 
    -- Infinite potential on the left side is a subtype of everything
    --   Still, assert that the left and right contexts have equal potential
    (Infty, _)       -> 
      let leftSum = envSum (_symbols env)
          rightSum = envSum syms
          subtypeAssertions = (leftSum `subtypeOp` rightSum) : directSubtypesBase cm bl br
      in subtypeAssertions ++ wellFormedAssertions
    -- Throw error if there is infinite potential on the right side without infinite potential on the left side
    (_, Infty)       -> 
      error $ show $ text "assertSubtypes: encountered infinite potential on the right side in type of a subtyping relation" 
        <+> pretty tl <+> text "<:" <+> pretty tr 
    -- Assert subtypes normally
    (Fml fl, Fml fr) -> 
      let leftSum = addFormulas fl (envSum (_symbols env)) 
          rightSum = addFormulas fr (envSum syms)
          subtypeAssertions = (leftSum `subtypeOp` rightSum) : directSubtypesBase cm bl br
      in subtypeAssertions ++ wellFormedAssertions
assertSubtypes _ _ _ _ _ _ = [] 

-- | 'directSubtypes' @env tl tr@ : Generate the set of all formulas in types @tl@ and @tr@, zipped by a binary operation @op@ on formulas 
directSubtypes :: Bool -> RType -> RType -> [Formula]
directSubtypes cm (ScalarT bl _ Infty) (ScalarT br _ _) = []
directSubtypes _  tl tr@(ScalarT _ _ Infty) =
  error $ show $ text "directSubtypes: encountered infinite potential on the right side of the subtyping relation"
                 <+> pretty tl <+> text "<:" <+> pretty tr
directSubtypes cm (ScalarT bl _ (Fml fl)) (ScalarT br _ (Fml fr)) = (fl `subtypeOp` fr) : directSubtypesBase cm bl br
directSubtypes _ _ _ = [] 

directSubtypesBase :: Bool -> BaseType Formula -> BaseType Formula -> [Formula]
directSubtypesBase cm (DatatypeT _ tsl _) (DatatypeT _ tsr _) = concat $ zipWith (directSubtypes cm) tsl tsr
directSubtypesBase _  (TypeVarT _ _ Infty) _ = []
directSubtypesBase _  tl tr@(TypeVarT _ _ Infty) = 
  error $ show $ text "directSubtypesBase: encountered infinite potential on the right side of the subtyping relation"
                 <+> pretty tl <+> text "<:" <+> pretty tr
directSubtypesBase cm (TypeVarT _ _ (Fml ml)) (TypeVarT _ _ (Fml mr)) = [fml | cm && not (isTrivial fml)] 
    where fml = ml `subtypeOp` mr
directSubtypesBase _ _ _ = []

totalTopLevelPotential :: RType -> Formula
totalTopLevelPotential (ScalarT base _ (Fml p)) = p 
totalTopLevelPotential (ScalarT _ _ Infty)      = error "Encountered empty type constructor when computing totalPotential"
totalTopLevelPotential _                        = fzero

-- Is given constraint relevant for resource analysis
isResourceConstraint :: Constraint -> Bool
isResourceConstraint (Subtype _ _ _ _ Consistency _) = False
isResourceConstraint (Subtype _ _ ScalarT{} ScalarT{} _variant _label) = True
isResourceConstraint WellFormed{}  = True
isResourceConstraint SharedType{}  = True
isResourceConstraint ConstantRes{} = True
isResourceConstraint _             = False

-- Return a set of all formulas (potential, multiplicity, refinement) of a type. 
--   Doesn't mean anything necesssarily, used to embed environment assumptions
allFormulasOf :: Bool -> RType -> Set Formula
allFormulasOf cm (ScalarT b f Infty)       = Set.singleton f `Set.union` allFormulasOfBase cm b 
allFormulasOf cm (ScalarT b f (Fml p))     = Set.singleton f `Set.union` Set.singleton p `Set.union` allFormulasOfBase cm b
allFormulasOf cm (FunctionT _ argT resT _) = allFormulasOf cm argT `Set.union` allFormulasOf cm resT
allFormulasOf cm (LetT x s t)              = allFormulasOf cm s `Set.union` allFormulasOf cm t
allFormulasOf _ t                          = Set.empty

allFormulasOfBase :: Bool -> BaseType Formula -> Set Formula
allFormulasOfBase _  (TypeVarT _ _ Infty)   = Set.empty
allFormulasOfBase cm (TypeVarT _ _ (Fml m)) = if cm then Set.singleton m else Set.empty
allFormulasOfBase cm (DatatypeT x ts ps)    = Set.unions (map (allFormulasOf cm) ts)
allFormulasOfBase _ b                       = Set.empty

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

-- | 'hasUniversals' @env sch@ : Indicates existence of universally quantified resource formulas in the potential
--    annotations of the type @sch@
-- Could be done more efficiently by returning as soon as a universal is found
allUniversals :: Environment -> RSchema -> Set Formula
allUniversals env sch = getUniversals univSyms $ conjunction $ allRFormulas True $ typeFromSchema sch 
  where
    -- Include function argument variable names in set of possible universally quantified expressions
    univSyms = varsOfType (typeFromSchema sch) `Set.union` universalSyms env
    varsOfType ScalarT{}                 = Set.empty
    varsOfType (FunctionT x argT resT _) = Set.insert x (varsOfType argT `Set.union` varsOfType resT)

-- | 'getUniversals' @env f@ : return the set of universally quantified terms in formula @f@ given set of universally quantified symbols @syms@ 
getUniversals :: Set String -> Formula -> Set Formula
getUniversals syms (SetLit s fs)   = Set.unions $ map (getUniversals syms) fs
getUniversals syms v@(Var s x)     = Set.fromList [v | Set.member x syms] 
getUniversals syms (Unary _ f)     = getUniversals syms f
getUniversals syms (Binary _ f g)  = getUniversals syms f `Set.union` getUniversals syms g
getUniversals syms (Ite f g h)     = getUniversals syms f `Set.union` getUniversals syms g `Set.union` getUniversals syms h
getUniversals syms p@(Pred s x fs) = Set.fromList [p | Set.member x syms]
getUniversals syms (Cons _ x fs)   = Set.unions $ map (getUniversals syms) fs
getUniversals syms (All f g)       = getUniversals syms g
getUniversals _ _                  = Set.empty 

-- | containsDT @ms f@ : return whether or not formula @f@ includes a measure (or a data type in general), the names of which are in @ms@
containsDT :: [String] -> Formula -> Bool
containsDT _  (Var _ x)          = x == valueVarName
containsDT ms (Pred _ name args) = (name `elem` ms) || any (containsDT ms) args
containsDT _  Cons{}             = True 
containsDT ms (Unary _ f)        = containsDT ms f
containsDT ms (Binary _ f g)     = containsDT ms f || containsDT ms g
containsDT ms (Ite f g h)        = containsDT ms f || containsDT ms g || containsDT ms h
containsDT ms (SetLit _ fs)      = any (containsDT ms) fs
containsDT ms (All f g)          = containsDT ms f || containsDT ms g
containsDT _ _                   = False
        
-- | Apply a list of substitutions to a formula
substituteManyInFml :: [(Formula, Formula)] -> Formula -> Formula
substituteManyInFml [] f       = f
substituteManyInFml xs fml = foldl (\f (g, ex) -> substituteForFml ex g f) fml xs

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

-- Maybe this will change? idk
subtypeOp = (|=|)

writeLog level msg = do 
  maxLevel <- lift $ asks _tcSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return ()