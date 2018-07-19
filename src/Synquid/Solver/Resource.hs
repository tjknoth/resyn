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
    Nothing -> throwError $ text "Insufficient resources"
    Just f -> resourceConstraints %= (++ f) 

-- | 'solveResourceConstraints' @oldConstraints constraints@ : Transform @constraints@ into logical constraints and attempt to solve the complete system by conjoining with @oldConstraints@
solveResourceConstraints :: (MonadHorn s, MonadSMT s) => [Constraint] -> [Constraint] -> TCSolver s (Maybe [Constraint]) 
solveResourceConstraints oldConstraints constraints = do
    writeLog 3 $ linebreak <+> text "Generating resource constraints:"
    checkMults <- asks _checkMultiplicities
    -- Generate numerical resource-usage formulas from typing constraints:
    fmlList <- mapM (generateFormula True checkMults) constraints
    -- This is repeated every iteration, could be cached:
    accFmlList <- mapM (generateFormula False checkMults) oldConstraints
    -- Filter out trivial constraints, mostly for readability
    let fmls = Set.fromList (filter (not . isTrivial) fmlList)
    let query = conjunction fmls
    let accumlatedQuery = conjunction (Set.fromList accFmlList)
    -- Check satisfiability
    (b, s) <- isSatWithModel (accumlatedQuery |&| query)
    let result = if b then "SAT" else "UNSAT"
    writeLog 5 $ nest 4 $ text "Accumulated resource constraints" $+$ prettyConjuncts (filter isInteresting accFmlList)
    writeLog 3 $ nest 4 $ text "Solved resource constraint after conjoining formulas:" <+> text result $+$ prettyConjuncts (filter isInteresting fmlList)
    if b 
      then do
        writeLog 6 $ nest 2 (text "Solved with model") </> nest 6 (text s) 
        return $ Just constraints 
      else return Nothing
            
-- | 'generateFormula' @c@: convert constraint @c@ into a logical formula
generateFormula :: (MonadHorn s, MonadSMT s) => Bool -> Bool -> Constraint -> TCSolver s Formula 
generateFormula shouldLog checkMults c@(Subtype env tl tr _ name) = do
    let fmls = conjunction $ Set.filter (not . isTrivial) $ assertSubtypes env checkMults subtypeOp tl tr
    embedAndProcessConstraint env shouldLog c fmls (conjunction (allFormulasOf tl `Set.union` allFormulasOf tr)) (Set.insert (refinementOf tl))
generateFormula shouldLog checkMults c@(WellFormed env t) = do
    let fmls = conjunction $ Set.filter (not . isTrivial) $ Set.map (|>=| fzero) $ allRFormulas checkMults t
    embedAndProcessConstraint env shouldLog c fmls (conjunction (allFormulasOf t)) (Set.insert (refinementOf t))
generateFormula shouldLog checkMults c@(SharedType env v t tl tr) = do 
    let fmls = conjunction $ partition checkMults t tl tr
    embedAndProcessConstraint env shouldLog c fmls (conjunction (allFormulasOf t)) id
generateFormula _ _ c                            = error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c

embedAndProcessConstraint :: (MonadSMT s, MonadHorn s) => Environment -> Bool -> Constraint -> Formula -> Formula -> (Set Formula -> Set Formula) -> TCSolver s Formula
embedAndProcessConstraint env shouldLog c fmls relevantFml addTo = do 
  emb <- embedEnv env relevantFml True
  -- Check if embedding is singleton { false }
  let isFSingleton s = (Set.size s == 1) && (Set.findMin s == ffalse)
  if isFSingleton emb  
    then return ftrue
    else do 
      let emb' = preprocessAssumptions $ addTo emb
      when (shouldLog && isInteresting fmls) $ writeLog 3 (nest 4 $ pretty c $+$ text "Gives numerical constraint" <+> pretty fmls)
      instantiateUniversals shouldLog env fmls (conjunction emb')

-- | 'instantiateUniversals' @b env fml ass@ : Instantiate universally quantified terms in @fml@ under @env@ with examples satisfying assumptions @ass@
instantiateUniversals :: (MonadHorn s, MonadSMT s) => Bool -> Environment -> Formula -> Formula -> TCSolver s Formula
instantiateUniversals shouldLog env fml ass = do
  shouldInstantiate <- asks _instantiateUnivs
  let universals = getUniversals env fml
  if null universals || not shouldInstantiate
    then return fml -- nothing universally quantified, can solve directly
    else do 
      let len = length universals + 1 
      exs <- assembleExamples len universals ass
      when shouldLog $ writeLog 1 $ text "Universally quantified formulas" <+> pretty universals $+$ nest 4 (text "Give examples" <+> pretty exs)
      fml' <- applyPolynomials fml universals
      let fmlSkeletons = replicate len fml'
      --let exampleAssumptions = map (foldl (\a (f, e) -> Binary And (Binary Eq f e) a) ass) exs
      --let query = zipWith (|=>|) exampleAssumptions fmlSkeletons
      let query = zipWith substituteManyInFml exs fmlSkeletons
      writeLog 3 $ nest 4 $ text "Universals instantiated to" <+> pretty exs <+> text "In formulas" $+$ vsep (map pretty query)
      return $ conjunction (Set.fromList query)


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
partition cm (ScalarT b _ f) (ScalarT bl _ fl) (ScalarT br _ fr) = Set.insert (f |=| (fl |+| fr)) $ partitionBase cm b bl br
partition _ _ _ _ = Set.empty

partitionBase :: Bool -> BaseType Formula -> BaseType Formula -> BaseType Formula -> Set Formula
partitionBase cm (DatatypeT _ ts _) (DatatypeT _ tsl _) (DatatypeT _ tsr _) = Set.unions $ zipWith3 (partition cm) ts tsl tsr
partitionBase cm (TypeVarT _ _ m) (TypeVarT _ _ ml) (TypeVarT _ _ mr) = if cm then Set.singleton $ m |=| (ml |+| mr) else Set.empty
partitionBase _ _ _ _ = Set.empty

-- | 'joinAssertions' @op tl tr@  : Generate the set of all formulas in types @tl@ and @tr@, zipped by a binary operation @op@ on formulas 
assertSubtypes :: Environment -> Bool -> (Formula -> Formula -> Formula) -> RType -> RType -> Set Formula
assertSubtypes env cm op (ScalarT bl _ fl) (ScalarT br _ fr) = Set.insert (fl `op` fr) $ assertSubtypesBase env cm op bl br
-- TODO: add total potential from input and output environment to left and right sides
{-
assertSubtypes op (ScalarT bl _ fl) (ScalarT br _ fr) = Set.insert (( leftTotal |+| fl) `op` (rightTotal |+| fr)) $ assertSubtypesBase allsyms op bl br
  where 
    leftTotal = totalMultiplicity allsyms
    rightTotal = totalMultiplicity allsyms
-}
assertSubtypes _ _ op _ _ = Set.empty 

assertSubtypesBase :: Environment -> Bool -> (Formula -> Formula -> Formula) -> BaseType Formula -> BaseType Formula -> Set Formula
assertSubtypesBase env cm op (DatatypeT _ tsl _) (DatatypeT _ tsr _) = Set.unions $ zipWith (assertSubtypes env cm op) tsl tsr
assertSubtypesBase env cm op (TypeVarT _ _ ml) (TypeVarT _ _ mr) = 
  if cm && not (isTrivial fml)
    then Set.singleton fml
    else Set.empty
    where fml = ml `op` mr
assertSubtypesBase _ _ _ _ _ = Set.empty 

-- Is given constraint relevant for resource analysis
isResourceConstraint :: Constraint -> Bool
isResourceConstraint (Subtype e ScalarT{} ScalarT{} _ _) = True
isResourceConstraint WellFormed{} = True
isResourceConstraint SharedType{}  = True
isResourceConstraint _            = False

assembleExamples :: (MonadHorn s, MonadSMT s) => Int -> [Formula] -> Formula -> TCSolver s [[(Formula, Formula)]]
assembleExamples n universals ass = do 
  exs <- mapM (\f -> (,) f <$> getExamples n ass f) universals -- List of formula + list-of-example pairs
  return $ transform exs [] 
  where
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

applyPolynomials :: (MonadHorn s, MonadSMT s) => Formula -> [Formula] -> TCSolver s Formula 
applyPolynomials v@(Var s x) universals = do 
  vs <- use resourceVars
  if Set.member x vs
    then return $ generatePolynomial v universals
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


generatePolynomial :: Formula -> [Formula] -> Formula
generatePolynomial annotation universalVars = foldl (|+|) constVar products
  where 
    products = map (\v -> Binary Times v (makeVar v)) universalVars
    textFrom (Var _ x) = x
    textFrom (Pred _ x fs) = x ++ show (pretty fs)
    toText f = show (pretty f)
    constVar = Var IntS (toText annotation ++ "CONST")
    makeVar f = Var IntS (textFrom f ++ "_" ++ toText annotation)

-- | 'totalPotential' @schs@ : compute the total potential contained in a list of schemas @schs@
totalPotential :: [RSchema] -> Formula
totalPotential schs = foldl (|+|) (IntLit 0) $ catMaybes $ fmap (potentialOf . typeFromSchema) schs

-- | 'totalMultiplicity' @schs@ : compute the total of the multiplicities contained in a list of schemas @schs@
totalMultiplicity :: [RSchema] -> Formula
totalMultiplicity schs = foldl (|+|) (IntLit 0) $ catMaybes $ fmap (multiplicityOfType . typeFromSchema) schs

-- Extract potential from refinement type
potentialOf :: RType -> Maybe Formula
potentialOf (ScalarT (DatatypeT _ ts _) _ _) = case foldl (|+|) (IntLit 0) (catMaybes (fmap potentialOf ts)) of 
    (IntLit 0) -> Nothing
    f          -> Just f
potentialOf (ScalarT _ _ p) = Just p  
potentialOf _               = Nothing 

-- Total multiplicity in a refinement type
multiplicityOfType :: RType -> Maybe Formula 
multiplicityOfType (ScalarT base f p) = multiplicityOfBase base 
multiplicityOfType _                  = Nothing

-- Total multiplicity in a base type
multiplicityOfBase :: BaseType Formula -> Maybe Formula
multiplicityOfBase (TypeVarT _ _ m)      = Just m
multiplicityOfBase (DatatypeT name ts _) = case foldl (|+|) (IntLit 0) (catMaybes (fmap multiplicityOfType ts)) of 
    (IntLit 0) -> Nothing -- No multiplicities in constructors 
    f          -> Just f
multiplicityOfBase _                = Nothing

-- Return a set of all formulas (potential, multiplicity, refinement) of a type. Doesn't mean anything necesssarily, used to embed environment assumptions
allFormulasOf :: RType -> Set Formula
allFormulasOf (ScalarT b f p) = Set.singleton f `Set.union` Set.singleton p `Set.union` allFormulasOfBase b
allFormulasOf (FunctionT _ argT resT _) = allFormulasOf argT `Set.union` allFormulasOf resT
allFormulasOf (LetT x s t) = allFormulasOf s `Set.union` allFormulasOf t
allFormulasOf t = Set.empty

allFormulasOfBase :: BaseType Formula -> Set Formula
allFormulasOfBase (TypeVarT _ _ m) = Set.singleton m
allFormulasOfBase (DatatypeT x ts ps) = Set.unions (map allFormulasOf ts)
allFormulasOfBase b = Set.empty

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
      let query = conjunction $ Set.fromList (ass : unique)
      val <- lift . lift . lift $ solveAndGetAssignment query fmlName
      case val of 
        Just v -> getExamples' (n - 1) ass fmlName (uncurry ASTLit v : acc)
        Nothing -> return Nothing

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
isInteresting (Binary Ge _ (IntLit 0)) = False
isInteresting (Binary Implies _ f)     = isInteresting f 
isInteresting (BoolLit True)           = False
isInteresting (Binary And f g)         = isInteresting f && isInteresting g 
isInteresting _                        = True

-- Maybe this will change? idk
subtypeOp = (|=|)

