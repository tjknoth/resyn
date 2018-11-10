{-# LANGUAGE FlexibleInstances #-}

module Synquid.Solver.CEGIS (
  CEGISParams,
  RMonad(..),
  solveWithCEGIS,
  coefficientsOf,
  formatUniversals,
  makePTerm,
  universalFml,
  initializePolynomial,
  initialCoefficients,
  possibleMeasureApps
) where 

import Synquid.Type
import Synquid.Logic
import Synquid.Pretty
import Synquid.Solver.Monad
import Synquid.Solver.Util
import qualified Synquid.Z3 as Z3
import Synquid.Program 

import Control.Monad.State
import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Lens
import Debug.Trace

{- Data structures for CEGIS solver -}


-- Universally quantified variable
newtype UVar = UVar { unUVar :: (String, Formula) }
  deriving (Eq, Show, Ord)

-- Uninterpreted function (measure) relevant for constraint solving
type UMeasure = (String, MeasureDef)

-- Term of a polynomial: coefficient * universal
data PolynomialTerm = PolynomialTerm {
  coefficient :: String,
  universal :: Maybe UVar 
} deriving (Eq, Show, Ord)

-- Polynomial represented as a list of coefficient-variable pairs (where a Nothing in the coefficient position indicates the constant term)
type Polynomial = [PolynomialTerm]

-- Map from resource variable name to its corresponding polynomial
type PolynomialSkeletons = Map String Polynomial

-- Map from resource variable name to its corresponding polynomial (as a formula)
type RPolynomials = Map String Formula

-- Coefficient valuations in a valid program
type ResourceSolution = Map String Formula

-- Set of all counterexamples
type ExampleSet = [Counterexample]

-- Map from universally quantified expression (in string form) to its valuation
data Counterexample = CX {
  measureInterps :: Map String Z3UFun,
  constructorInterps :: Map String Z3UFun,
  variables :: Map String Formula,
  model :: SMTModel
} deriving (Eq)

{- Instances -}

-- Uninterpreted function instance for measures
instance UF MeasureDef where 
  argSorts mdef = map snd (_constantArgs mdef) ++ [_inSort mdef]
  resSort = _outSort

-- Uninterpreted function instance for constructors requires an environment
--   and the name of the constructor
instance UF (Environment, String) where 
  argSorts (env, dt) = 
    case Map.lookup dt (allSymbols env) of 
      Nothing -> error $ "argSorts: constructor " ++ dt ++ " not found"
      Just cons -> allArgSorts $ typeFromSchema cons
  resSort (env, dt) = 
    case Map.lookup dt (allSymbols env) of 
      Nothing -> error $ "resSort: constructor " ++ dt ++ " not found"
      Just cons -> resultSort $ typeFromSchema cons

instance Declarable MeasureDef where 
  declare _ = Z3.function

instance Declarable (Environment, String) where 
  declare _ = Z3.typeConstructor

{- Top-level interface -}

-- | Solve formula containing universally quantified expressions with counterexample-guided inductive synthesis
solveWithCEGIS :: RMonad s 
               => Int 
               -> Formula 
               -> Formula
               -> [UVar] 
               -> [UMeasure] 
               -> ExampleSet 
               -> PolynomialSkeletons 
               -> ResourceSolution 
               -> TCSolver s Bool
solveWithCEGIS 0 fml ass universals measures _ polynomials program = do
  -- Base case: If there is a counterexample, @fml@ is UNSAT, SAT otherwise
  counterexample <- getCounterexample (ass |=>| fml) universals measures polynomials program 
  case counterexample of 
    Nothing -> return True
    Just cx -> do 
      writeLog 4 $ text "Last counterexample:" <+> pretty (Map.assocs (variables cx)) </> linebreak
      return False

solveWithCEGIS n fml ass universals measures examples polynomials program = do
  -- Attempt to find point for which current parameterization fails
  counterexample <- getCounterexample (ass |=>| fml) universals measures polynomials program 
  case counterexample of 
    Nothing -> return True -- No counterexamples exist, polynomials hold on all inputs
    Just cx ->  
      do 
        writeLog 4 $ text "Counterexample:" <+> pretty (Map.assocs (variables cx))
        writeLog 4 $ text "      measures:" <+> pretty (Map.assocs (measureInterps cx))
        -- Update example list
        let examples' = cx : examples
        -- Attempt to find parameterization holding on all examples
        -- Assumptions shouldn't be relevant for this query
        params <- getParameters fml polynomials examples'
        case params of
          Nothing -> return False -- No parameters exist, formula is unsatisfiable
          Just p  -> do 
            pstr <- lift . lift . lift $ printParams p polynomials
            writeLog 6 $ text "Params:" <+> pstr 
            solveWithCEGIS (n - 1) fml ass universals measures examples' polynomials p

-- | 'getCounterexample' @fml universals polynomials program@ 
--    Find a valuation for @universals@ such that (not @formula@) holds, under parameter valuation @program@
getCounterexample :: RMonad s 
                  => Formula 
                  -> [UVar] 
                  -> [UMeasure] 
                  -> PolynomialSkeletons 
                  -> ResourceSolution 
                  -> TCSolver s (Maybe Counterexample)
getCounterexample fml universals measures polynomials program = do 
  let runInSolver = lift . lift . lift
  -- Generate polynomials by substituting parameter valuations for coefficients
  cxPolynomials <- runInSolver $ mapM (mkCXPolynomial program) polynomials
  --cxpstr <- printParams program cxPolynomials
  -- Replace resource variables with appropriate polynomials and negate the resource constraint
  let cxQuery = fnot $ applyPolynomials cxPolynomials fml 
  writeLog 7 $ linebreak <+> text "CEGIS counterexample query:" </> pretty cxQuery
  -- Query solver for a counterexample
  model <- runInSolver $ solveAndGetModel cxQuery 
  assignments <- runInSolver . sequence 
    $ (modelGetAssignment (map universalVar universals) <$> model)
  minterps <- runInSolver . sequence 
    $ (modelGetUFs measures <$> model)
  ienv <- use initEnv
  let dts = filter (`notElem` setConstructors) $ concatMap _constructors 
              $ Map.elems $ ienv^.datatypes
  -- This is ugly currently: need to zip the names twice because of how the UF instances are designed
  let cons = zip dts $ zip (repeat ienv) dts
  cinterps <- runInSolver . sequence 
    $ (modelGetUFs cons <$> model)
  return $ (CX <$> minterps) <*> cinterps <*> join assignments <*> model
  

-- | 'getParameters' @fml polynomials examples@
--   Find a valuation for all coefficients such that @fml@ holds on all @examples@
getParameters :: RMonad s 
              => Formula 
              -> PolynomialSkeletons 
              -> ExampleSet 
              -> TCSolver s (Maybe (Map String Formula))
getParameters fml polynomials examples = do
  let runInSolver = lift . lift . lift
  -- For each example, substitute its value for the universally quantified expressions in each polynomial skeleton
  paramPolynomials <- runInSolver 
    $ mapM (\ex -> mapM (mkParamPolynomial ex) polynomials) examples
  -- For each example, substitute its value for the universally quantified expressions in the actual resource constraint
  let fmls' = map ((`substitute` fml) . variables) examples
  -- Evaluate the measure applications within the model from the counterexample
  fmls'' <- runInSolver $ zipWithM evalMeasures examples fmls' 
  iEnv <- use initEnv
  -- Assert that any parameterization must hold for all examples
  let paramQuery = conjunction $ zipWith applyPolynomials paramPolynomials fmls''
  -- Collect all parameters
  let allCoefficients = concatMap coefficientsOf (Map.elems polynomials)
  writeLog 7 $ text "CEGIS param query:" </> pretty paramQuery
  model <- runInSolver $ solveAndGetModel paramQuery 
  join <$> (runInSolver . sequence $ (modelGetAssignment allCoefficients <$> model))

evalMeasures :: RMonad s => Counterexample -> Formula -> s Formula
evalMeasures cx fml = case fml of 
  Pred s x args -> 
    case Map.lookup x (measureInterps cx) of 
    -- Counterexample did not include measure definition, doesn't matter what we use:
      Nothing   -> return defaultInterp 
      Just md   -> evalInModel args (model cx) md
  Var{}         -> return fml
  SetLit b xs   -> SetLit b <$> mapM (evalMeasures cx) xs
  Unary op e    -> Unary op <$> evalMeasures cx e
  Binary op f g -> Binary op <$> evalMeasures cx f <*> evalMeasures cx g
  Ite g t f     -> Ite <$> evalMeasures cx g <*> evalMeasures cx t <*> evalMeasures cx f
  Cons s x args -> --Cons s x <$> mapM (evalMeasures cx) as
    case Map.lookup x (constructorInterps cx) of 
      Nothing   -> return $ Cons s x args 
      Just md   -> evalInModel args (model cx) md
  All{}         -> return fml
  _             -> return fml

mkCXPolynomial coeffMap poly = sumFormulas <$> mapM (pTermForCX coeffMap) poly
mkParamPolynomial cx poly = sumFormulas <$> mapM (pTermForProg cx) poly

-- | Assemble a polynomial term, given a variable prefix and a universally quantified expression
makePTerm :: String -> Formula -> PolynomialTerm
makePTerm prefix fml = PolynomialTerm coeff (Just univ)
  where 
    coeff  = makePolynomialVar prefix fml
    univ   = UVar (fmlStr, fml)
    fmlStr = universalToString fml

universalVar = fst . unUVar 
universalFml = snd . unUVar 

coefficientsOf = map coefficient

defaultInterp = fzero

-- | Convert PolynomialTerm into a formula for use in the counterexample query (ie instantiate the coefficients)
pTermForCX :: RMonad s => ResourceSolution -> PolynomialTerm -> s Formula
pTermForCX coeffVals (PolynomialTerm coeff Nothing)  = return $ exprValue coeffVals coeff 
pTermForCX coeffVals (PolynomialTerm coeff (Just u)) = return $ exprValue coeffVals coeff |*| universalFml u 

-- | Convert PolynomialTerm into a formula for use in the program query (ie instantiate the universals)
pTermForProg :: RMonad s => Counterexample -> PolynomialTerm -> s Formula
pTermForProg cx (PolynomialTerm coeff Nothing)  = return $ Var IntS coeff
pTermForProg cx (PolynomialTerm coeff (Just u)) = (Var IntS coeff |*|) <$> val
  where 
    val = case unUVar u of 
      (s, Var{})    -> return $ exprValue (variables cx) s
      (_, f@Pred{}) -> evalMeasures cx f

-- | Get the value of some expression from a map of valuations (either Example or ResourceSolution)
exprValue :: Map String Formula -> String -> Formula
exprValue coeffVals coeff = 
  case Map.lookup coeff coeffVals of 
    Nothing -> error $ "exprValue: valuation not found for expression " ++ coeff
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
printParams :: RMonad s => ResourceSolution -> PolynomialSkeletons -> s Doc
printParams prog polynomials = pretty <$> mapM str (Map.assocs polynomials)
  where 
    str (rvar, poly)  = (\p -> text rvar <+> operator "=" <+> p) <$> printPolynomial poly 
    printPolynomial p = pretty <$> mkCXPolynomial prog p 

-- Coefficient variables for resource polynomial
makePolynomialVar :: String -> Formula -> String 
makePolynomialVar annotation f = textFrom f ++ "_" ++ toText annotation
  where 
    textFrom (Var _ x) = x
    textFrom (Pred _ x fs) = x ++ show (pretty fs)
    toText f = show (pretty f)

-- Turn a list of universally quantified formulas into a list of Universal 
--   data structures (formula-string pairs)
formatUniversals univs = map UVar $ zip (map universalToString univs) univs

-- Initialize polynomial over universally quantified @fmls@, using variable prefix @s@
initializePolynomial :: Environment 
                     -> AnnotationDomain
                     -> [Formula] 
                     -> [UMeasure] 
                     -> String 
                     -> Polynomial 
initializePolynomial env sty univs ms s = 
  constantPTerm s : initializePolynomial' env sty univs ms s

initializePolynomial' env Variable universals _ s = map (makePTerm s) universals
initializePolynomial' env Measure universals ms s = 
  map (makePTerm s) (possibleMeasureApps env universals ms)
initializePolynomial' env Both universals ms s = 
  initializePolynomial' env Variable universals ms s 
  ++ initializePolynomial' env Measure universals ms s

possibleMeasureApps :: Environment 
                    -> [Formula]
                    -> [UMeasure]
                    -> [Formula]
possibleMeasureApps env universals ms = 
  let cargs = env^.measureConstArgs 
      -- Assemble relevant logical formulas
      mkVar (x, s) = Var s x
      mkApp x def arg = Pred (def^.outSort) x (map mkVar (def^.constantArgs) ++ [arg])
      -- variables in context of relevant sort
      possibleArgs s = filter (\uvar -> (sortShape . sortOf) uvar == sortShape s) universals
      possibleApps x def = map (mkApp x def) (possibleArgs (def^.inSort))
      -- all constant-argument combinations for a given measure
      mkAllApps m def = allMeasureApps (Map.lookup m cargs) (def^.constantArgs)
  in concat $ concatMap (\(m, def) -> map (mkAllApps m def) (possibleApps m def)) ms

-- Constant term in a polynomial, using variable prefix @s@
constantPTerm s = PolynomialTerm (constPolynomialVar s) Nothing

constPolynomialVar s = s ++ "CONST"

-- Initialize all coefficients to zero when starting CEGIS
initialCoefficients = repeat $ IntLit 0

universalToString :: Formula -> String
universalToString (Var _ x) = x -- ++ "_u"
universalToString (Pred _ x fs) = x ++ concatMap show fs ++ "_u"
universalToString (Cons _ x fs) = x ++ concatMap show fs ++ "_u"