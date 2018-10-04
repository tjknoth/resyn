module Synquid.Solver.CEGIS (
  Universal(..),
  PolynomialTerm(..),
  solveWithCEGIS,
  coefficientsOf,
  formatUniversals,
  makePTerm,
  universalVar,
  universalFml,
  initializePolynomial,
  initialCoefficients
) where 

import Synquid.Logic
import Synquid.Pretty
import Synquid.Solver.Monad
import Synquid.Solver.Util

import Control.Monad.State
import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List

{- Data structures for CEGIS solver -}

-- Universally quantified variable
newtype Universal = Universal (String, Formula)
  deriving (Eq, Show, Ord)

-- Term of a polynomial: coefficient * universal
data PolynomialTerm = PolynomialTerm {
  coefficient :: String,
  universal :: Maybe Universal 
} deriving (Eq, Show, Ord)

-- Polynomial represented as a list of coefficient-variable pairs (where a Nothing in the coefficient position indicates the constant term)
type Polynomial = [PolynomialTerm]

-- Map from resource variable name to its corresponding polynomial
type PolynomialSkeletons = Map String Polynomial
-- Map from resource variable name to its corresponding polynomial (as a formula)
type RPolynomials = Map String Formula

-- Map from universally quantified expression (in string form) to its valuation
type Example = Map String Formula

-- Coefficient valuations in a valid program
type ResourceSolution = Map String Formula

-- Set of all counterexamples
type ExampleSet = [Example]

-- Solver queries are either asking for counterexamples or 
--   a parameterization of the program
data QueryType = Counterexample | Param 

{- Top-level interface -}

-- | Solve formula containing universally quantified expressions with counterexample-guided inductive synthesis
solveWithCEGIS :: MonadSMT s => Int -> Formula -> [Universal] -> ExampleSet -> PolynomialSkeletons -> ResourceSolution -> TCSolver s Bool
solveWithCEGIS 0 fml universals _ polynomials program = do
  -- Base case: If there is a counterexample, @fml@ is UNSAT, SAT otherwise
  counterexample <- getCounterexample fml universals polynomials program 
  case counterexample of 
    Nothing -> return True
    Just cx -> do 
      writeLog 4 $ text "Last counterexample:" <+> pretty (Map.assocs cx) </> linebreak
      return False

solveWithCEGIS numIters fml universals examples polynomials program = do
  -- Attempt to find point for which current parameterization fails
  counterexample <- getCounterexample fml universals polynomials program 
  case counterexample of 
    Nothing -> return True -- No counterexamples exist, polynomials hold on all inputs
    Just cx ->  
      do 
        writeLog 4 $ text "Counterexample:" <+> pretty (Map.assocs cx)
        -- Update example list
        let examples' = cx : examples
        -- Attempt to find parameterization holding on all examples
        params <- getParameters fml polynomials examples'
        case params of
          Nothing -> return False -- No parameters exist, formula is unsatisfiable
          Just p  -> do 
            writeLog 6 $ text "Params:" <+> printParams p polynomials
            solveWithCEGIS (numIters - 1) fml universals examples' polynomials p

-- | 'getCounterexample' @fml universals polynomials program@ 
--    Find a valuation for @universals@ such that (not @formula@) holds, under parameter valuation @program@
getCounterexample :: MonadSMT s => Formula -> [Universal] -> PolynomialSkeletons -> ResourceSolution -> TCSolver s (Maybe (Map String Formula))
getCounterexample fml universals polynomials program = do 
  -- Generate polynomials by substituting parameter valuations for coefficients
  let cxPolynomials = fmap (polynomialToFml Counterexample program) polynomials
  -- Replace resource variables with appropriate polynomials and negate the resource constraint
  let cxQuery = fnot $ applyPolynomials cxPolynomials fml 
  writeLog 7 $ linebreak <+> text "CEGIS counterexample query:" </> pretty cxQuery
  -- Query solver for a counterexample
  lift . lift . lift $ solveAndGetAssignment cxQuery (map universalVar universals)

-- | 'getParameters' @fml polynomials examples@
--   Find a valuation for all coefficients such that @fml@ holds on all @examples@
getParameters :: MonadSMT s => Formula -> PolynomialSkeletons -> ExampleSet -> TCSolver s (Maybe (Map String Formula))
getParameters fml polynomials examples = do
  -- For each example, substitute its value for the universally quantified expressions in each polynomial skeleton
  let paramPolynomials = map (\ex -> fmap (polynomialToFml Param ex) polynomials) examples
  -- For each example, substitute its value for the universally quantified expressions in the actual resource constraint
  let fmls' = map (`substitute` fml) examples
  -- Assert that any parameterization must hold for all examples
  let paramQuery = conjunction $ zipWith applyPolynomials paramPolynomials fmls'
  -- Collect all parameters
  let allCoefficients = concatMap coefficientsOf (Map.elems polynomials)
  writeLog 7 $ text "CEGIS param query:" </> pretty paramQuery
  lift . lift . lift $ solveAndGetAssignment paramQuery allCoefficients

    
-- | Convert an abstract polynomial into a formula
polynomialToFml :: QueryType -> Map String Formula -> Polynomial -> Formula
polynomialToFml Counterexample coeffMap poly = sumFormulas $ map (pTermForCX coeffMap) poly
polynomialToFml Param univMap poly           = sumFormulas $ map (pTermForProg univMap) poly

-- | Assemble a polynomial term, given a variable prefix and a universally quantified expression
makePTerm :: String -> Formula -> PolynomialTerm
makePTerm prefix fml = PolynomialTerm coeff (Just univ)
  where 
    coeff  = makePolynomialVar prefix fml
    univ   = Universal (fmlStr, fml)
    fmlStr = universalToString fml

universalVar (Universal (name, _)) = name
universalFml (Universal (_, fml))  = fml

coefficientsOf = map coefficient

-- | Convert PolynomialTerm into a formula for use in the counterexample query (ie instantiate the coefficients)
pTermForCX :: ResourceSolution -> PolynomialTerm -> Formula
pTermForCX coeffVals (PolynomialTerm coeff Nothing)  = exprValue coeffVals coeff 
pTermForCX coeffVals (PolynomialTerm coeff (Just u)) = exprValue coeffVals coeff |*| universalFml u 

-- | Convert PolynomialTerm into a formula for use in the program query (ie instantiate the universals)
pTermForProg :: Example -> PolynomialTerm -> Formula
pTermForProg univVals (PolynomialTerm coeff Nothing)  = Var IntS coeff
pTermForProg univVals (PolynomialTerm coeff (Just u)) = Var IntS coeff |*| exprValue univVals (universalVar u)

-- | Get the value of some expression from a map of valuations (either Example or ResourceSolution)
exprValue :: Map String Formula -> String -> Formula
exprValue coeffVals coeff = 
  case Map.lookup coeff coeffVals of 
    Nothing -> error $ "exprValue: valuation not found for expression" ++ coeff
    Just f  -> f

-- | Replace resource variables in a formula with the appropriate polynomial
applyPolynomials :: RPolynomials -> Formula -> Formula
applyPolynomials poly v@(Var _ name)   = fromMaybe v (Map.lookup name poly)
applyPolynomials poly (Unary op f)     = Unary op (applyPolynomials poly f)
applyPolynomials poly (Binary op f g)  = Binary op (applyPolynomials poly f) (applyPolynomials poly g)
applyPolynomials poly (Ite f g h)      = Ite (applyPolynomials poly f) (applyPolynomials poly g) (applyPolynomials poly h)
applyPolynomials poly (Pred s name fs) = Pred s name $ map (applyPolynomials poly) fs
applyPolynomials poly (Cons s name fs) = Cons s name $ map (applyPolynomials poly) fs
applyPolynomials poly (SetLit s fs)    = SetLit s $ map (applyPolynomials poly) fs
applyPolynomials _ f@(Unknown _ _)     = error $ show $ text "applyPolynomials: predicate unknown in resource expression:" <+> pretty f
applyPolynomials _ f@(All _ _)         = error $ show $ text "applyPolynomials: universal quantifier in resource expression:" <+> pretty f
applyPolynomials _ f                   = f

-- | Helper to print the parameters alongside the actual resource polynomial
printParams :: ResourceSolution -> PolynomialSkeletons -> Doc
printParams prog polynomials = pretty $ map (\(rvar, poly) -> text rvar <+> operator "=" <+> printPolynomial poly) (Map.assocs polynomials)
  where 
    printPolynomial p = pretty $ polynomialToFml Counterexample prog p 

-- Coefficient variables for resource polynomial
makePolynomialVar :: String -> Formula -> String 
makePolynomialVar annotation f = textFrom f ++ "_" ++ toText annotation
  where 
    textFrom (Var _ x) = x
    textFrom (Pred _ x fs) = x ++ show (pretty fs)
    toText f = show (pretty f)

-- Turn a list of universally quantified formulas into a list of Universal 
--   data structures (formula-string pairs)
formatUniversals univs = map Universal $ zip (map universalToString univs) univs

-- Initialize polynomial over universally quantified @fmls@, using variable prefix @s@
initializePolynomial fmls s = constantPTerm s : map (makePTerm s) fmls

-- Constant term in a polynomial, using variable prefix @s@
constantPTerm s = PolynomialTerm (constPolynomialVar s) Nothing

constPolynomialVar s = s ++ "CONST"

-- Initialize all coefficients to zero when starting CEGIS
initialCoefficients = repeat $ IntLit 0

universalToString :: Formula -> String
universalToString (Var _ x) = x -- ++ "_univ"
universalToString (Pred _ x fs) = x ++ concatMap show fs ++ "_univ"
universalToString (Cons _ x fs) = x ++ concatMap show fs ++ "_univ"