{-# LANGUAGE FlexibleContexts #-}

-- | Resource analysis
module Synquid.Solver.Resource (
  checkResources 
) where

import Synquid.Logic 
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Solver.Monad
import Synquid.Pretty
import Synquid.Error
import Synquid.Solver.Util

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

{- Implementation -}

-- | Check resource bounds: attempt to find satisfying expressions for multiplicity and potential annotations 
checkResources :: (MonadSMT s, MonadHorn s) => [Constraint] -> TCSolver s ()
checkResources constraints = do 
  tcParams <- ask 
  tcState <- get 
  oldConstraints <- use resourceConstraints 
  newC <- solveResourceConstraints oldConstraints (filter isResourceConstraint constraints)
  case newC of 
    Left err -> throwError $ text err
    Right f  -> resourceConstraints %= (++ f) 

-- | 'solveResourceConstraints' @oldConstraints constraints@ : Transform @constraints@ into logical constraints and attempt to solve the complete system by conjoining with @oldConstraints@
solveResourceConstraints :: (MonadHorn s, MonadSMT s) => [TaggedConstraint] -> [Constraint] -> TCSolver s (Either String [TaggedConstraint]) 
solveResourceConstraints oldConstraints constraints = do
    writeLog 3 $ linebreak <+> text "Generating resource constraints:"
    checkMults <- asks _checkMultiplicities
    -- Generate numerical resource-usage formulas from typing constraints:
    constraintList <- mapM (generateFormula checkMults) constraints
    let query = assembleQuery oldConstraints constraintList 
    -- Check satisfiability
    (b, s) <- isSatWithModel query
    let result = if b then "SAT" else "UNSAT"
    writeLog 5 $ nest 4 $ text "Accumulated resource constraints:" 
      $+$ prettyConjuncts (filter (isInteresting . constraint) oldConstraints)
    writeLog 3 $ nest 4 $ text "Solved resource constraint after conjoining formulas:" <+> text result 
      $+$ prettyConjuncts (filter (isInteresting . constraint) constraintList)
    if b 
      then do
        writeLog 6 $ nest 2 (text "Solved with model") </> nest 6 (text s) 
        return $ Right constraintList
      else Left <$> checkUnsatCause oldConstraints constraints 

-- | Given lists of constraints (newly-generated and accumulated), construct the corresponding solver query
assembleQuery :: [TaggedConstraint] -> [TaggedConstraint] -> Formula 
assembleQuery accConstraints constraints = 
  let fmlList = map constraint (filter (\(TaggedConstraint _ f) -> (not . isTrivial) f) constraints)
      accFmlList = map constraint accConstraints 
      query = conjunction $ accFmlList ++ fmlList
  in query

-- | checkUnsatCause : determine whether the constant-resource demands are the cause of unsatisfiability or not.
--     returns an appropriate error message
checkUnsatCause :: (MonadHorn s, MonadSMT s) => [TaggedConstraint] -> [Constraint] -> TCSolver s String 
checkUnsatCause oldConstraints constraints = do
  checkMults <- asks _checkMultiplicities
  constraintList <- mapM (generateFormula checkMults) (filter (not . isCTConstraint) constraints)
  let query = assembleQuery oldConstraints constraintList 
  (b, _) <- isSatWithModel query 
  if b 
    then return "Branching expression is not constant-time" 
    else return "Insufficient resources" 
    where 
      isCTConstraint (ConstantRes _ _) = True
      isCTConstraint _                 = False

            
-- | 'generateFormula' @c@: convert constraint @c@ into a logical formula
generateFormula :: (MonadHorn s, MonadSMT s) => Bool -> Constraint -> TCSolver s TaggedConstraint 
generateFormula checkMults c@(Subtype env syms tl tr variant label) = do
  tass <- use typeAssignment
  let fmls = conjunction $ Set.filter (not . isTrivial) $ case variant of 
        Nondeterministic -> assertSubtypes env syms tass checkMults tl tr
        _                -> directSubtypes checkMults tl tr
  TaggedConstraint label <$> embedAndProcessConstraint env c fmls (conjunction (allFormulasOf checkMults tl `Set.union` allFormulasOf checkMults tr)) (Set.insert (refinementOf tl))
generateFormula checkMults c@(WellFormed env t label) = do
  let fmls = conjunction $ Set.filter (not . isTrivial) $ Set.map (|>=| fzero) $ allRFormulas checkMults t
  TaggedConstraint label <$> embedAndProcessConstraint env c fmls (conjunction (allFormulasOf checkMults t)) (Set.insert (refinementOf t))
generateFormula checkMults c@(SharedType env t tl tr label) = do 
  let fmls = conjunction $ partition checkMults t tl tr
  TaggedConstraint label <$> embedAndProcessConstraint env c fmls (conjunction (allFormulasOf checkMults t)) id
generateFormula checkMults c@(ConstantRes env label) = do 
  tass <- use typeAssignment
  let fml = assertZeroPotential checkMults tass env 
  TaggedConstraint ("CT: " ++ label) <$> embedAndProcessConstraint env c fml fzero id -- Use fzero since it has no free variables
generateFormula _ c = error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c

-- | Embed the environment assumptions and preproess the constraint for solving 
embedAndProcessConstraint :: (MonadSMT s, MonadHorn s) => Environment -> Constraint -> Formula -> Formula -> (Set Formula -> Set Formula) -> TCSolver s Formula
embedAndProcessConstraint env c fmls relevantFml addTo = do 
  emb <- embedEnv env relevantFml True
  -- Check if embedding is singleton { false }
  let isFSingleton s = (Set.size s == 1) && (Set.findMin s == ffalse)
  if isFSingleton emb  
    then return ftrue
    else do 
      let emb' = preprocessAssumptions $ addTo emb
      writeLog 3 (nest 4 $ pretty c $+$ text "Gives numerical constraint" <+> pretty fmls) -- <+> text "from scalars" $+$ prettyScalars env)
      -- TODO: get universals from the assumptions as well!
      --checkUniversals env fmls -- Throw error if any universally quantified expressions! (for now)
      return $ conjunction emb' |=>| fmls
      --instantiateUniversals env fmls (conjunction emb')

checkUniversals :: (MonadSMT s, MonadHorn s) => Environment -> Formula -> TCSolver s Formula
checkUniversals env fml = do
  let universals = getUniversals env fml
  unless (null universals) $ throwError $ text "checkUniversals: found universally quantified expression(s) in resource annotation:" <+> pretty universals
  return fml

-- Map from resource variable names to the coefficient variables in the corresponding
--   resource polynomial
type ResourcePolynomials = Map String (Map String Formula)

-- | Check the satisfiability of the generated resource constraints, instantiating universally 
--     quantified expressions as necessary.
satisfyResources :: (MonadHorn s, MonadSMT s) => Environment -> Formula -> TCSolver s Bool
satisfyResources env fml = do 
  shouldInstantiate <- asks _instantiateUnivs 
  let universals = getUniversals env fml
  if null universals || not shouldInstantiate
    then fst <$> isSatWithModel fml
    else do
      let maxIterations = length universals + 1 -- TODO: what about branching expressiosn?
      rVars <- Set.toList <$> use resourceVars
      -- Initialize all coefficients to zero
      let polynomialCoefficientsOf s = constPolynomialVar s : map (makePolynomialVar s) universals
      let initialPolynomial s = Map.fromList $ zip (polynomialCoefficientsOf s) (repeat (IntLit 0))
      -- Initialize polynomials for each resource variable
      let initialProgram = Map.fromList $ zip rVars (map initialPolynomial rVars)
      let universalsWithVars = zip universals (map universalToString universals)

      solveWithCEGIS maxIterations fml universalsWithVars [] Map.empty


-- | Solve formula containing universally quantified expressions with counterexample-guided inductive synthesis
solveWithCEGIS :: (MonadHorn s, MonadSMT s) => Int -> Formula -> [(Formula, String)] -> [Formula] -> ResourcePolynomials -> TCSolver s Bool
solveWithCEGIS 0 _ _ _ _ = return False
solveWithCEGIS numIters fml universals examples prog = do
  -- TODO: replace fml with program! 
  counterexample <- getCounterexample fml (map snd universals) prog
  case counterexample of 
    Nothing -> return True -- No counterexamples exist, polynomials hold on all inputs
    Just cx -> return False -- Placeholder!!!
    {- do 
      params <- existsProgram
      case params of 
        Nothing -> return False -- No satisfying polynomials exist
        Just poly -> updatePolynomials
    -}

-- | Attempt to find valuations for universally quantified expressions under which @fml@ does not hold
getCounterexample :: (MonadHorn s, MonadSMT s) => Formula -> [String] -> ResourcePolynomials -> TCSolver s (Maybe (Map String Formula)) 
getCounterexample fml universalVars poly = lift . lift . lift $ solveAndGetAssignment (Unary Not fml) universalVars

-- Placeholder this is wrong!
findSatisfyingCoefficients :: (MonadHorn s, MonadSMT s) => Formula -> [String] -> ResourcePolynomials -> TCSolver s (Maybe (Map String Formula))
findSatisfyingCoefficients fml universalVars poly = lift . lift . lift $ solveAndGetAssignment fml universalVars 


{-
-- | 'instantiateUniversals' @b env fml ass@ : Instantiate universally quantified terms in @fml@ under @env@ with examples satisfying assumptions @ass@
instantiateUniversals :: (MonadHorn s, MonadSMT s) => Environment -> Formula -> Formula -> TCSolver s Formula
instantiateUniversals env fml ass = do
  shouldInstantiate <- asks _instantiateUnivs
  let universals = getUniversals env fml
  if null universals || not shouldInstantiate
    then return fml -- nothing universally quantified, can solve directly
    else do 
      let len = length universals + 1 
      exs <- assembleExamples len universals ass
      writeLog 1 $ text "Universally quantified formulas" <+> pretty universals $+$ nest 4 (text "Give examples" <+> pretty exs)
      fml' <- applyPolynomials fml universals
      let fmlSkeletons = replicate len fml'
      --let exampleAssumptions = map (foldl (\a (f, e) -> Binary And (Binary Eq f e) a) ass) exs
      --let query = zipWith (|=>|) exampleAssumptions fmlSkeletons
      let query = zipWith substituteManyInFml exs fmlSkeletons
      writeLog 3 $ nest 4 $ text "Universals instantiated to" <+> pretty exs <+> text "In formulas" $+$ vsep (map pretty query)
      return $ conjunction query 
-}

-- | 'allRFormulas' @t@ : return all resource-related formulas (potentials and multiplicities) from a refinement type @t@
allRFormulas :: Bool -> RType -> Set Formula 
allRFormulas cm (ScalarT base _ p) = Set.insert p (allRFormulasBase cm base)
allRFormulas _ _                   = Set.empty

allRFormulasBase :: Bool -> BaseType Formula -> Set Formula
allRFormulasBase cm (DatatypeT _ ts _) = Set.unions $ fmap (allRFormulas cm) ts
allRFormulasBase cm (TypeVarT _ _ m)   = if cm then Set.singleton m else Set.empty
allRFormulasBase _ _                   = Set.empty

-- | 'partition' @t tl tr@ : Generate numerical constraints referring to a partition of the resources associated with @t@ into types @tl@ and @tr@ 
partition :: Bool -> RType -> RType -> RType -> Set Formula 
partition cm (ScalarT b _ f) (ScalarT bl _ fl) (ScalarT br _ fr) 
  = Set.insert (f |=| (fl |+| fr)) $ partitionBase cm b bl br
partition _ _ _ _ = Set.empty

partitionBase :: Bool -> BaseType Formula -> BaseType Formula -> BaseType Formula -> Set Formula
partitionBase cm (DatatypeT _ ts _) (DatatypeT _ tsl _) (DatatypeT _ tsr _) 
  = Set.unions $ zipWith3 (partition cm) ts tsl tsr
partitionBase cm (TypeVarT _ _ m) (TypeVarT _ _ ml) (TypeVarT _ _ mr) 
  = if cm then Set.singleton (m |=| (ml |+| mr)) else Set.empty
partitionBase _ _ _ _ = Set.empty

assertZeroPotential :: Bool -> TypeSubstitution -> Environment -> Formula
assertZeroPotential cm tass env = sumFormulas (fmap (totalPotential cm) scalars) |=| fzero
  where 
    scalars = fmap (typeSubstitute tass . typeFromSchema) rawScalars
    rawScalars = Map.filterWithKey notEmptyCtor (symbolsOfArity 0 env) 
    notEmptyCtor x _ = Set.notMember x (_emptyCtors env) 

-- | 'assertSubtypes' @env tl tr@ : Generate formulas partitioning potential appropriately amongst
--    environment @env@ in order to check @tl@ <: @tr@
assertSubtypes :: Environment -> SymbolMap -> TypeSubstitution -> Bool -> RType -> RType -> Set Formula
assertSubtypes env syms tass cm (ScalarT bl _ fl) (ScalarT br _ fr) = 
  subtypeAssertions `Set.union` wellFormedAssertions
    where
      -- Get map of only scalar types (excluding empty type constructors) in environment:
      scalarsOf smap = Map.filterWithKey notEmptyCtor $ fmap typeFromSchema $ fromMaybe Map.empty $ Map.lookup 0 smap
      -- Get top-level potentials from environment, after applying current type substitutions
      topPotentials = Map.mapMaybe (topPotentialOf . typeSubstitute tass) 
      -- Sum all top-level potential in an environment:
      envSum f smap = addFormulas f $ sumFormulas $ topPotentials $ scalarsOf smap
      leftSum  = envSum fl (_symbols env)
      rightSum = envSum fr syms      
      -- Assert that types in fresh context are well-formed (w.r.t top-level annotations)
      wellFormed smap = Set.map (|>=| fzero) ((Set.fromList . Map.elems . topPotentials) smap)  -- TODO: Map k a -> Set a
      subtypeAssertions = Set.insert (leftSum `subtypeOp` rightSum) $ directSubtypesBase cm bl br
      wellFormedAssertions = wellFormed $ scalarsOf syms
      notEmptyCtor x _ = Set.notMember x (_emptyCtors env) 
assertSubtypes _ _ _ _ _ _ = Set.empty

-- | 'directSubtypes' @env tl tr@ : Generate the set of all formulas in types @tl@ and @tr@, zipped by a binary operation @op@ on formulas 
directSubtypes :: Bool -> RType -> RType -> Set Formula
directSubtypes cm (ScalarT bl _ fl) (ScalarT br _ fr) = Set.insert (fl `subtypeOp` fr) $ directSubtypesBase cm bl br
directSubtypes _ _ _ = Set.empty 

directSubtypesBase :: Bool -> BaseType Formula -> BaseType Formula -> Set Formula
directSubtypesBase cm (DatatypeT _ tsl _) (DatatypeT _ tsr _) = Set.unions $ zipWith (directSubtypes cm) tsl tsr
directSubtypesBase cm (TypeVarT _ _ ml) (TypeVarT _ _ mr) = 
  if cm && not (isTrivial fml)
    then Set.singleton fml
    else Set.empty
    where fml = ml `subtypeOp` mr
directSubtypesBase _ _ _ = Set.empty 

totalPotential :: Bool -> RType -> Formula
totalPotential cm (ScalarT base _ p) = p -- |+| totalPotentialBase cm base
totalPotential _ _                   = fzero

totalPotentialBase :: Bool -> BaseType Formula -> Formula
totalPotentialBase cm (DatatypeT _ ts _) = foldl addFormulas fzero (map (totalPotential cm) ts)
-- TODO: should we use the substitutions?
totalPotentialBase cm (TypeVarT _ _ m) = if cm then m else fzero
totalPotentialBase _ _ = fzero

-- Is given constraint relevant for resource analysis
isResourceConstraint :: Constraint -> Bool
isResourceConstraint (Subtype _ _ _ _ Consistency _) = False
isResourceConstraint (Subtype _ _ ScalarT{} ScalarT{} _variant _label) = True
isResourceConstraint WellFormed{}  = True
isResourceConstraint SharedType{}  = True
isResourceConstraint ConstantRes{} = True
isResourceConstraint _             = False

{-
-- | Get example set for a universally quantified formula
assembleExamples :: (MonadHorn s, MonadSMT s) => Int -> [Formula] -> Formula -> TCSolver s [[(Formula, Formula)]]
assembleExamples n universals ass = do 
  exs <- mapM (\f -> (,) f <$> getExamples n ass f) universals -- List of formula + list-of-example pairs
  return $ transform exs [] 
  where
    -- Transform list of formula + list-of-example pairs into a list of formula-example pairs
    -- ie transform [(Formula, [Formula])] -> [[(Formula, Formula)]]
    pairHeads :: [(Formula, [Formula])] -> [(Formula, Formula)]
    pairHeads []              = []
    pairHeads ((f, []):_)     = []
    pairHeads ((f, x:xs):exs) = (f, x) : pairHeads exs
    removeHeads :: [(Formula, [Formula])] -> [(Formula, [Formula])]
    removeHeads []              = []
    removeHeads ((f, []):_)     = []
    removeHeads ((f, x:xs):exs) = (f, xs) : removeHeads exs
    transform :: [(Formula, [Formula])] -> [[(Formula, Formula)]] -> [[(Formula, Formula)]]
    transform [] acc         = acc
    transform ((_,[]):_) acc = acc
    transform exs acc        = transform (removeHeads exs) (pairHeads exs : acc)
-}

-- | Replace universally quantified subexpressions in a Formula with polynomial
applyPolynomials :: (MonadHorn s, MonadSMT s) => Formula -> [Formula] -> TCSolver s Formula 
applyPolynomials v@(Var s x) universals = do 
  vs <- use resourceVars
  if Set.member x vs
    then return $ generatePolynomial x universals
    else return v
applyPolynomials (Unary op f) universals = Unary op <$> applyPolynomials f universals
applyPolynomials (Binary op f g) universals = (Binary op <$> applyPolynomials f universals) <*> applyPolynomials g universals
applyPolynomials (Ite f g h) universals = ((Ite <$> applyPolynomials f universals) <*> applyPolynomials g universals) <*> applyPolynomials h universals
applyPolynomials (Pred s x fs) universals = Pred s x <$> mapM (`applyPolynomials` universals) fs
applyPolynomials (Cons s x fs) universals = Cons s x <$> mapM (`applyPolynomials` universals) fs
applyPolynomials f@Unknown{} _ = do
  throwError $ text "applyPolynomials: predicate unknown in resource assertions"
  return f
applyPolynomials f@All{} _ = do 
  throwError $ text "applyPolynomials: universal quantifier in resource assertions"
  return f
applyPolynomials f@ASTLit{} _ = do 
  throwError $ text "applyPolynomials: Z3 AST literal in resource assertions"
  return f
applyPolynomials f _ = return f 

-- | Generate a first-degree polynomial over possible universally quanitified expressions
generatePolynomial :: String -> [Formula] -> Formula
generatePolynomial annotation universalVars = foldl addFormulas (constVar annotation) products
  where 
    products = map (\v -> Binary Times v (makeVar annotation v)) universalVars
    constVar s = Var IntS $ constPolynomialVar s
    makeVar s f = Var IntS $ makePolynomialVar s f

-- Coefficient variables for resource polynomial
makePolynomialVar :: String -> Formula -> String 
makePolynomialVar annotation f = textFrom f ++ "_" ++ toText annotation
  where 
    textFrom (Var _ x) = x
    textFrom (Pred _ x fs) = x ++ show (pretty fs)
    toText f = show (pretty f)
    
-- constant term in resource polynomial    
constPolynomialVar s = s ++ "CONST"

universalToString :: Formula -> String
universalToString (Var _ x) = x ++ "_univ"
universalToString (Pred _ x fs) = x ++ concatMap show fs ++ "_univ"
universalToString (Cons _ x fs) = x ++ concatMap show fs ++ "_univ"

-- Return a set of all formulas (potential, multiplicity, refinement) of a type. 
--   Doesn't mean anything necesssarily, used to embed environment assumptions
allFormulasOf :: Bool -> RType -> Set Formula
allFormulasOf cm (ScalarT b f p) = Set.singleton f `Set.union` Set.singleton p `Set.union` allFormulasOfBase cm b
allFormulasOf cm (FunctionT _ argT resT _) = allFormulasOf cm argT `Set.union` allFormulasOf cm resT
allFormulasOf cm (LetT x s t) = allFormulasOf cm s `Set.union` allFormulasOf cm t
allFormulasOf _ t = Set.empty

allFormulasOfBase :: Bool -> BaseType Formula -> Set Formula
allFormulasOfBase cm (TypeVarT _ _ m) = if cm then Set.singleton m else Set.empty
allFormulasOfBase cm (DatatypeT x ts ps) = Set.unions (map (allFormulasOf cm) ts)
allFormulasOfBase _ b = Set.empty

-- Return refinement of scalar type
refinementOf :: RType -> Formula 
refinementOf (ScalarT _ fml _) = fml
refinementOf _                 = error "error: Encountered non-scalar type when generating resource constraints"

-- | 'preprocessAssumptions' @fmls@ : eliminate assumptions that contain unknown predicates
preprocessAssumptions :: Set Formula -> Set Formula 
preprocessAssumptions fs = Set.map assumeUnknowns $ Set.filter (not . isUnknownForm) fs

-- Assume that unknown predicates in a formula evaluate to True
-- TODO: probably don't need as many cases
assumeUnknowns :: Formula -> Formula
assumeUnknowns (Unknown s id) = BoolLit True
assumeUnknowns (SetLit s fs) = SetLit s (fmap assumeUnknowns fs)
assumeUnknowns (Unary op f) = Unary op (assumeUnknowns f)
assumeUnknowns (Binary op fl fr) = Binary op (assumeUnknowns fl) (assumeUnknowns fr)
assumeUnknowns (Ite g t f) = Ite (assumeUnknowns g) (assumeUnknowns t) (assumeUnknowns f)
assumeUnknowns (Pred s x fs) = Pred s x (fmap assumeUnknowns fs)
assumeUnknowns (Cons s x fs) = Cons s x (fmap assumeUnknowns fs)
assumeUnknowns (All f g) = All (assumeUnknowns f) (assumeUnknowns g)
assumeUnknowns f = f

-- | 'getUniversals' @env f@ : return the set of universally quantified terms in formula @f@ given environment @env@ 
getUniversals :: Environment -> Formula -> [Formula] 
getUniversals env (SetLit s fs) = unions $ map (getUniversals env) fs
getUniversals env v@(Var s x)  = [v | Set.member x (allUniversals env)] 
getUniversals env (Unary _ f) = getUniversals env f
getUniversals env (Binary _ f g) = getUniversals env f `union` getUniversals env g
getUniversals env (Ite f g h) = getUniversals env f `union` getUniversals env g `union` getUniversals env h
getUniversals env p@(Pred s x fs) = [p | Set.member x (allUniversals env)]
getUniversals env (Cons _ x fs) = unions $ map (getUniversals env) fs
getUniversals env (All f g) = getUniversals env g
getUniversals _ _ = []

unions = foldl union []

{-
-- | 'getExamples' @n ass fml@ : returns @n@ unique instances of universally quantified formula @fml@ satisfying assumptions @ass@ paired with 
getExamples :: (MonadHorn s, MonadSMT s) => Int -> Formula -> Formula -> TCSolver s [Formula]
getExamples n ass fml = do 
  name <- fmlVarName fml 
  let v = Var IntS name
  let ass' = substituteForFml v fml ass
  exs <- getExamples' n ass' name [] 
  case exs of 
    Nothing -> do 
      throwError $ text "getExamples: Cannot find" <+> pretty n <+> text "unique valuations for" <+> pretty fml <+> text "satisfying assumptions:" <+> pretty ass
      return []
    Just exs' -> return exs'

-- Version of the above with accumulator that returns lists wrapped in Maybe
getExamples' :: (MonadHorn s, MonadSMT s) => Int -> Formula -> String -> [Formula] -> TCSolver s (Maybe [Formula])
getExamples' n ass fmlName acc = 
  if n <= 0
    then return (Just acc)
    else do 
      let fmlVar = Var IntS fmlName
      let unique = fmap (Binary Neq fmlVar) acc
      let query = conjunction (ass : unique)
      val <- lift . lift . lift $ solveAndGetAssignment query fmlName
      case val of 
        Just v -> getExamples' (n - 1) ass fmlName (uncurry ASTLit v : acc)
        Nothing -> return Nothing
-}
        
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

-- Variable name for example generation
fmlVarName :: Monad s => Formula -> TCSolver s String
fmlVarName (Var s x)     = return $ x ++ show s
fmlVarName (Pred _ x fs) = freshId "F"
fmlVarName f             = error $ "fmlVarName: Can only substitute fresh variables for variable or predicate, given " ++ show (pretty f)

-- Filter away "uninteresting" constraints for logging. Specifically, well-formednes
-- Definitely not complete, just "pretty good"
isInteresting (Binary Ge (IntLit _) (IntLit 0)) = False
isInteresting (Binary Ge (Var _ _) (IntLit 0))  = False
isInteresting (Binary Implies _ f)     = isInteresting f 
isInteresting (BoolLit True)           = False
isInteresting (Binary And f g)         = isInteresting f || isInteresting g 
isInteresting _                        = True

-- Maybe this will change? idk
subtypeOp = (|=|)

