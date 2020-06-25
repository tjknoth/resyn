{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Synquid.Solver.CEGIS (
  Universals(..),
  coefficient,
  solveWithCEGIS,
  coefficientsOf,
  formatUniversals,
  allValidCArgs,
  initializePolynomial,
  initialCoefficients,
  mkFuncVar,
  mkFuncString,
  mkCXPolynomial,
  updateCEGISState,
  initCEGISState,
  runCEGIS
) where

import Synquid.Logic
import Synquid.Pretty
import Synquid.Program
import Synquid.Solver.Monad
import Synquid.Solver.Types

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Lens
import Control.Monad.State
import Control.Monad.Reader (asks)
import Debug.Trace

type CEGISSolver s = StateT CEGISState s

runCEGIS :: CEGISSolver s a -> CEGISState -> s (a, CEGISState)
runCEGIS = runStateT

{- Top-level interface -}

-- | Solve formula containing universally quantified expressions with counterexample-guided inductive synthesis
solveWithCEGIS :: RMonad s
               => Int
               -> [ProcessedRFormula]
               -> Universals
               -> CEGISSolver s Bool
solveWithCEGIS 0 rfmls universals = do
  -- Base case: If there is a counterexample, @fml@ is UNSAT, SAT otherwise
  counterexample <- verify rfmls universals 
  case counterexample of
    Nothing -> return True
    Just cx -> do
      traceM "warning: CEGIS failed on last iteration"
      writeLog 4 $ text "Last counterexample:" <+> text (maybe "" (snd . model) counterexample)
      return False

solveWithCEGIS n rfmls universals = do
  -- Attempt to find point for which current parameterization fails
  counterexample <- verify rfmls universals 
  --res <- verifyOnePass rfmls 
  case counterexample of
  --case res of 
    Nothing -> do
      pstr <- printParams 
      writeLog 5 $ text "Solution wth" <+> pretty n <+> text "iterations left:" <+> pstr
      return True -- No counterexamples exist, polynomials hold on all inputs
    Just cx ->
    --Just (rfmls', cx) ->
      do
        -- Update example list, attempt to find parameterization holding on all examples
        rfmls' <- getRelevantConstraints rfmls cx 
        writeLog 5 $ text "Violated formulas:" </> pretty (map bodyFml rfmls')
        params <- synthesize rfmls' cx
        case params of
          Nothing -> do
            writeLog 3 $ text "CEGIS failed with" <+> pretty n <+> text "iterations left"
            return False -- No parameters exist, formula is unsatisfiable
          Just p  -> do
            updateProgram p
            pstr <- printParams 
            writeLog 6 $ text "Params:" <+> pstr
            solveWithCEGIS (n - 1) rfmls universals



-- | 'verify' @fml universals polynomials program@
--    Find a valuation for @universals@ such that (not @formula@) holds, under parameter valuation @program@
verify :: RMonad s
       => [ProcessedRFormula]
       -> Universals
       -> CEGISSolver s (Maybe Counterexample)
verify rfmls universals = do
  polys <- use polynomials
  prog <- use rprogram
  -- Generate polynomials by substituting parameter valuations for coefficients
  cxPolynomials <- mapM mkCXPolynomial polys
  -- Replace resource variables with appropriate polynomials (with pending substitutions applied)
  --   and negate the resource constraint
  let substRFml = applyPolynomial mkCXPolynomial completeFml
  fml <- conjunction <$> mapM substRFml rfmls
  let cxQuery = fnot $ substitute prog fml
  writeLog 7 $ linebreak <+> text "CEGIS counterexample query:" </> pretty cxQuery
  -- Query solver for a counterexample
  model <- lift $ solveAndGetModel cxQuery
  writeLog 4 $ text "CX model:" <+> text (maybe "" snd model)
  vars <- lift . sequence
    $ (modelGetAssignment (map fst (uvars universals)) <$> model)
  measures <- lift . sequence
    $ (modelGetAssignment (map fst (ufuns universals)) <$> model)
  return $ CX <$> measures <*> vars <*> model

{-
verifyOnePass :: RMonad s 
              => [ProcessedRFormula]
              -> CEGISSolver s (Maybe ([ProcessedRFormula], Counterexample))
verifyOnePass rfmls = do 
  prog <- use rprogram
  let substRFml = applyPolynomial mkCXPolynomial completeFml
  fml <- conjunction <$> mapM substRFml rfmls 
  let cxQuery = fnot $ substitute prog fml
  writeLog 7 $ linebreak <+> text "CEGIS counterexample query:" </> pretty cxQuery
  model <- lift $ solveAndGetModel cxQuery
  case model of 
    Nothing -> return Nothing 
    Just md -> do
      writeLog 4 $ text "CX model:" <+> text (snd md) -- (maybe "" snd model)
      rfmls' <- lift $ filterPreds rfmls md -- <$> model
      let nameOf (Var _ x) = x
      let allVars = map nameOf $ concatMap (Map.elems . _varSubsts) rfmls' 
      let allFuns = map nameOf $ concatMap (Set.toList . _renamedPreds) rfmls' 
      vars <- lift $ modelGetAssignment allVars md 
      funs <- lift $ modelGetAssignment allFuns md 
      return $ Just (rfmls', CX funs vars md)
-}

-- | 'getRelevantPreds' @rfml cx program polynomials@
-- Given a counterexample @cx@, a @program@, and a list of verification conditions @rfmls@
--   return only those violated by the model
getRelevantConstraints :: RMonad s
                      => [ProcessedRFormula]
                      -> Counterexample
                      -> CEGISSolver s [ProcessedRFormula]
getRelevantConstraints rfmls cx = do
  prog <- use rprogram
  let substRFml = applyPolynomial (mkEvalPolynomial prog cx) completeFml
  let check f = lift $ f `checkPredWithModel` model cx
  let isSatisfied rfml = check =<< substRFml rfml
  filterM (fmap not . isSatisfied) rfmls

-- | 'synthesize' @fml polynomials examples@
--   Find a valuation for all coefficients such that @fml@ holds on all @examples@
synthesize :: RMonad s
           => [ProcessedRFormula]
           -> Counterexample
           -> CEGISSolver s (Maybe ResourceSolution)
synthesize rfmls counterexample = do
  cxfml <- applyCounterexample rfmls counterexample
  counterexamples %= (cxfml :)
  paramQuery <- use counterexamples
  -- Evaluate the measure applications within the model from the counterexample
  -- Assert that any parameterization must hold for all examples
  -- Collect all parameters
  allCoefficients <- use coefficients
  writeLog 7 $ text "CEGIS param query:" </> pretty paramQuery 
  model <- lift $ solveAndGetModel (conjunction paramQuery)
  writeLog 8 $ text "Param model:" <+> text (maybe "" snd model)
  lift . sequence $ (modelGetAssignment allCoefficients <$> model)

-- | Substitute a counterexample into a set of resource formulas
applyCounterexample :: RMonad s 
                    => [ProcessedRFormula]
                    -> Counterexample
                    -> CEGISSolver s Formula 
applyCounterexample rfmls cx = do 
  let substRFml = applyPolynomial (mkParamPolynomial cx) bodyFml
  fml <- conjunction <$> mapM substRFml rfmls
  let fml' = substitute (allVariables cx) fml
  lift $ translate fml'

-- TODO: are examples ever applied to the actual variables?? not in polynomials?
applyPolynomial :: RMonad s 
                => (Polynomial -> CEGISSolver s Formula)
                -> (ProcessedRFormula -> Formula)
                -> ProcessedRFormula
                -> CEGISSolver s Formula
applyPolynomial mkPolynomial mkFormula rfml =
  applyPolynomial' mkPolynomial (_varSubsts rfml) (mkFormula rfml)

applyPolynomial' mkPolynomial subs f =
  let sub = applyPolynomial' mkPolynomial in 
  case f of 
    v@(Var s x)   -> do 
      polys <- use polynomials
      case Map.lookup x polys of 
        Nothing -> return v 
        Just p  -> 
          let p'      = substPolynomial subs p
           in mkPolynomial p' 
    WithSubst p e -> WithSubst p <$> sub (subs `composeSubstitutions` p) e
    SetLit s fs   -> SetLit s <$> mapM (sub subs) fs
    Unary op f    -> Unary op <$> sub subs f
    Binary op f g -> Binary op <$> sub subs f <*> sub subs g 
    Ite g t f     -> Ite <$> sub subs g <*> sub subs t <*> sub subs f
    Pred s x fs   -> Pred s x <$> mapM (sub subs) fs
    Cons s x fs   -> Cons s x <$> mapM (sub subs) fs 
    All q f       -> All q <$> sub subs f -- there shouldn't be foralls by now anyway
    Unknown s x   -> error $ "applySynthesisPolynomial: condition unknown " ++ x ++ " present"
    lit           -> return lit


substPolynomial :: Substitution -> Polynomial -> Polynomial 
substPolynomial subs = map subPterm
  where 
    subPterm p@(PolynomialTerm _ Nothing) = p
    subPterm (PolynomialTerm c (Just (ustr, u))) = PolynomialTerm c (Just (ustr', u'))
      where 
        u' = substitute subs u 
        ustr' = universalToString u'  

mkCXPolynomial :: RMonad s => Polynomial -> CEGISSolver s Formula 
mkCXPolynomial poly = do 
  prog <- use rprogram
  sumFormulas <$> mapM (pTermForCX prog) poly

mkEvalPolynomial :: RMonad s => ResourceSolution -> Counterexample -> Polynomial -> CEGISSolver s Formula 
mkEvalPolynomial coeffMap cx poly = do 
  prog <- use rprogram
  sumFormulas <$> mapM (pTermForEval coeffMap (allVariables cx)) poly

mkParamPolynomial :: RMonad s => Counterexample -> Polynomial -> CEGISSolver s Formula
mkParamPolynomial cx poly = sumFormulas <$> mapM (pTermForProg (allVariables cx)) poly

mkSimplePolynomial :: RMonad s => Map String Formula -> Polynomial -> CEGISSolver s Formula
mkSimplePolynomial cx poly = sumFormulas <$> mapM (pTermForPrinting cx) poly

-- | Assemble a polynomial term, given a variable prefix and a universally quantified expression
mkPTerm :: String -> Formula -> PolynomialTerm
mkPTerm prefix fml = PolynomialTerm coeff (Just (fmlStr, fml))
  where
    coeff  = mkPolynomialVar prefix fml
    fmlStr = universalToString fml

coefficientsOf = map coefficient

pTermForEval :: RMonad s => ResourceSolution -> Map String Formula -> PolynomialTerm -> CEGISSolver s Formula
pTermForEval coeffVals cx (PolynomialTerm c Nothing) =
  return $ exprValue coeffVals c
pTermForEval coeffVals cx (PolynomialTerm c (Just u)) =
  return $ exprValue coeffVals c |*| exprValue cx (fst u)

-- | Convert PolynomialTerm into a formula for use in the counterexample query (ie instantiate the coefficients)
pTermForCX :: RMonad s => ResourceSolution -> PolynomialTerm -> CEGISSolver s Formula
pTermForCX coeffVals (PolynomialTerm coeff Nothing)  =
  return $ exprValue coeffVals coeff
pTermForCX coeffVals (PolynomialTerm coeff (Just u)) =
  return $ exprValue coeffVals coeff |*| mkPForm (snd u)

-- | Convert PolynomialTerm into a formula for use in the program query (ie instantiate the universals)
pTermForProg :: RMonad s => Map String Formula -> PolynomialTerm -> CEGISSolver s Formula
pTermForProg cx (PolynomialTerm coeff Nothing)  =
  return $ Var IntS coeff
pTermForProg cx (PolynomialTerm coeff (Just u)) =
  return $ Var IntS coeff |*| exprValue cx (fst u)

pTermForPrinting cx (PolynomialTerm coeff u) =
  let c = exprValue cx coeff in
  -- Hack comparing against the string form to account for ASTLit case
  if show (pretty c) == "0"
    then return fzero
    else case u of
      Nothing -> return c
      Just u  -> return $ c |*| mkPForm (snd u)

-- | Get the value of some expression from a map of valuations (either Example or ResourceSolution)
exprValue :: Map String Formula -> String -> Formula
exprValue valAssignments val =
  fromMaybe
    (error ("exprValue: valuation not found for expression " ++ val ++ " in " ++ show (pretty (Map.assocs valAssignments))))
    (Map.lookup val valAssignments)

-- | Helper to print the parameters alongside the actual resource polynomial
printParams :: RMonad s => CEGISSolver s Doc
printParams = do 
  polys <- use polynomials
  prog <- use rprogram
  printParams' polys prog

printParams' :: RMonad s => PolynomialSkeletons -> ResourceSolution -> CEGISSolver s Doc
printParams' polys prog = pretty <$> mapM toDoc (Map.assocs polys) 
  where
    toDoc (rvar, poly)  = (\p -> text rvar <+> pretty (varsIn poly) <+> operator "=" <+> p) <$> printPolynomial poly
    varsIn = fmap fst . mapMaybe universal
    printPolynomial = fmap pretty . mkSimplePolynomial prog 

-- Coefficient variables for resource polynomial
mkPolynomialVar :: String -> Formula -> String
mkPolynomialVar annotation f = textFrom f ++ "_" ++ toText annotation
  where
    textFrom (Var _ x) = x
    textFrom (Pred _ x fs) = x ++ show (plain (pretty fs))
    toText f = show (pretty f)

-- Given a set of universally quantified expressions and newly generated resource
--   variables, update the state of the CEGIS solver
updateCEGISState :: Monad s => TCSolver s CEGISState
updateCEGISState = do  
  pDomain <- asks _polynomialDomain
  ll <- asks _tcSolverLogLevel
  newRVs <- use resourceVars
  st <- use cegisState
  env <- use initEnv 
  let init name info = initializePolynomial env pDomain (name, info)
  let newPolynomials = Map.mapWithKey init newRVs
  let newCoefficients = concat $ Map.elems $ fmap coefficientsOf newPolynomials 
  let newParameters = Map.fromList $ zip newCoefficients initialCoefficients 
  return $ 
    over polynomials (Map.union newPolynomials) $
    over rprogram (Map.union newParameters) $ 
    over coefficients (++ newCoefficients) $ 
    set cegisSolverLogLevel ll st

updateProgram :: Monad s => ResourceSolution -> CEGISSolver s ()
updateProgram prog = rprogram .= prog -- Map.union prog 

initCEGISState :: CEGISState 
initCEGISState = CEGISState {
    _rprogram = Map.empty,
    _polynomials = Map.empty,
    _coefficients = [],
    _cegisSolverLogLevel = 0,
    _counterexamples = []
  }

-- Initialize polynomial over universally quantified @fmls@, using variable prefix @s@
initializePolynomial :: Environment
                     -> RSolverDomain 
                     -> (String, [Formula])
                     -> Polynomial
initializePolynomial env Constant (name, _) = [constantPTerm name]
initializePolynomial env Dependent (name, uvars) =
  constantPTerm name : initializePolynomial' env (name, uvars)

initializePolynomial' env (name, uvars) = map (mkPTerm name) uvars


-- All variables that can fill the "constant" argument slots -- those that
--   unify with the formal type, given the non-constant argument
allValidCArgs :: Environment
              -> MeasureDef
              -> Formula
              -> [Substitution]
allValidCArgs env (MeasureDef inS outS defs cargs post) (Pred s x args) =
  let possibleCArgs =
        Set.toList $ Map.findWithDefault Set.empty x (env^.measureConstArgs)
      sortAssignment args =
        foldl assignSorts (Just Map.empty) (zip (map sortOf args) (map snd cargs))
      constructSubst valid =
        Map.fromList $ zip (map (\(Var _ x) -> x) args) valid
      checkValid as = case assignSorts (sortAssignment as) (sortOf (last args), inS) of
            Nothing -> Nothing
            Just _  -> Just as
      validCArgs = mapMaybe checkValid possibleCArgs
  in  map constructSubst validCArgs

-- Attempt to unify two sorts
assignSorts :: Maybe SortSubstitution -> (Sort, Sort) -> Maybe SortSubstitution
assignSorts Nothing _ = Nothing
assignSorts (Just substs) (argSort, formalSort) =
  case formalSort of
    BoolS ->
      case argSort of
        BoolS -> Just substs
        _     -> Nothing -- What about polymorphic sorts?
    IntS ->
      case argSort of
        IntS -> Just substs
        _    -> Nothing
    VarS x ->
      case argSort of
        VarS y ->
          if y == x
            then Just substs
            else
              case Map.lookup y substs of
                Just v  -> if v == VarS x then Just substs else Nothing
                Nothing -> Just $ Map.insert y (VarS x) substs
        _      -> Nothing
    DataS x ts ->
      case argSort of
        DataS y qs ->
          if x == y
            then foldl assignSorts (Just substs) (zip qs ts)
            else Nothing
        _ -> Nothing
    SetS s ->
      case argSort of
        SetS s' -> assignSorts (Just substs) (s', s)
        _       -> Nothing
    AnyS ->
      case argSort of
        AnyS -> Just substs
        _    -> Nothing

{- Some utilities -}

mkPForm v@Var{} = v
mkPForm p = mkFuncVar p

mkFuncVar m@(Pred s _ _) = Var s $ mkFuncString m
mkFuncVar m@(Cons s _ _) = Var s $ mkFuncString m
mkFuncVar f = f

mkFuncString (Pred _ m args) = m ++ show (plain (pretty args))
mkFuncString (Cons _ c args) = c ++ show (plain (pretty args))

-- Turn a list of universally quantified formulas into a list of Universal
--   data structures (formula-string pairs)
formatUniversals univs = zip (map universalToString univs) univs

allVariables (CX ms vs _) = Map.unions [ms, vs]

constantPTerm s = PolynomialTerm (constPolynomialVar s) Nothing
  where
    constPolynomialVar s = s ++ "CONST"

initialCoefficients = repeat $ IntLit 0

universalToString (Var _ x) = x
universalToString p = mkFuncString p

writeLog level msg = do
  maxLevel <- use cegisSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return () 