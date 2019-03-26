{-# LANGUAGE FlexibleInstances #-}

module Synquid.Solver.CEGIS (
  RMonad(..),
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
  mkCXPolynomial
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
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Lens
import Debug.Trace
import Control.Monad.Reader (asks)

{- Data structures for CEGIS solver -}

-- Universally quantified variable
type UVar = (String, Formula)

-- Uninterpreted function (measure) relevant for constraint solving
type UMeasure = (String, MeasureDef)

data Universals = Universals {
  uvars :: ![UVar],
  ufuns :: ![UVar]
} deriving (Show, Eq)

-- Term of a polynomial: coefficient * universal
data PolynomialTerm = PolynomialTerm {
  coefficient :: !String,
  universal :: !(Maybe UVar)
} deriving (Eq, Show, Ord)

-- Polynomial represented as a list of coefficient-variable pairs (where a Nothing in the coefficient position indicates the constant term)
type Polynomial = [PolynomialTerm]

-- Map from resource variable name to its corresponding polynomial
type PolynomialSkeletons = Map String Polynomial

-- Map from resource variable name to its corresponding polynomial (as a formula)
type RPolynomials = Map String Formula

-- Coefficient valuations in a valid program
type ResourceSolution = Map String Formula

-- Map from universally quantified expression (in string form) to its valuation
data Counterexample = CX {
  funcInterps :: !(Map String Formula),
  variables :: !(Map String Formula),
  model :: !SMTModel
} deriving (Eq)

{- Instances -}

-- Uninterpreted function instance for measures
instance UF MeasureDef where
  argSorts mdef = map snd (_constantArgs mdef) ++ [_inSort mdef]
  resSort = _outSort

instance Declarable MeasureDef where
  declare _ = Z3.function

{- Top-level interface -}

-- | Solve formula containing universally quantified expressions with counterexample-guided inductive synthesis
solveWithCEGIS :: RMonad s
               => Int
               -> [ProcessedRFormula]
               -> Universals
               -> [Formula]
               -> PolynomialSkeletons
               -> ResourceSolution
               -> TCSolver s Bool
solveWithCEGIS 0 rfmls universals _ polynomials program = do
  -- Base case: If there is a counterexample, @fml@ is UNSAT, SAT otherwise
  counterexample <- verify rfmls universals polynomials program
  case counterexample of
    Nothing -> return True
    Just cx -> do
      writeLog 4 $ text "Last counterexample:" <+> pretty (Map.assocs (variables cx))
      writeLog 4 $ text "           measures:" <+> pretty (Map.assocs (funcInterps cx)) </> linebreak
      return False

solveWithCEGIS n rfmls universals examples polynomials program = do
  -- Attempt to find point for which current parameterization fails
  counterexample <- verify rfmls universals polynomials program
  case counterexample of
    Nothing -> do
      pstr <- lift . lift . lift $ printParams program polynomials
      cMax <- lift $ asks _cegisMax
      writeLog 4 $ text "Solution on iteration" <+> pretty (cMax - n) <+> operator ":" <+> pstr
      return True -- No counterexamples exist, polynomials hold on all inputs
    Just cx ->
      do
        writeLog 4 $ text "Counterexample:" <+> pretty (Map.assocs (variables cx))
        writeLog 4 $ text "      measures:" <+> pretty (Map.assocs (funcInterps cx))
        --writeLog 4 $ text "  constructors:" <+> pretty (Map.assocs (constructorInterps cx)) </> linebreak
        -- Update example list
        -- Attempt to find parameterization holding on all examples
        --rfmls' <- getRelevantPreds rfmls cx program polynomials
        --writeLog 5 $ text "Violated formulas:" </> pretty (map rformula rfmls')
        --(examples', params) <- synthesize rfmls' examples polynomials cx
        (examples', params) <- synthesize rfmls examples polynomials cx
        case params of
          Nothing -> do
            cMax <- lift $ asks _cegisMax
            writeLog 3 $ text "CEGIS failed on iteration " <+> pretty (cMax - n)
            return False -- No parameters exist, formula is unsatisfiable
          Just p  -> do
            --let prog' = Map.union p program
            let prog' = p
            pstr <- lift . lift . lift $ printParams prog' polynomials
            writeLog 6 $ text "Params:" <+> pstr
            solveWithCEGIS (n - 1) rfmls universals examples' polynomials prog'

-- | 'verify' @fml universals polynomials program@
--    Find a valuation for @universals@ such that (not @formula@) holds, under parameter valuation @program@
verify :: RMonad s
       => [ProcessedRFormula]
       -> Universals
       -> PolynomialSkeletons
       -> ResourceSolution
       -> TCSolver s (Maybe Counterexample)
verify rfmls universals polynomials program = do
  let runInSolver = lift . lift . lift
  -- Generate polynomials by substituting parameter valuations for coefficients
  cxPolynomials <- runInSolver $ mapM (mkCXPolynomial program) polynomials
  -- Replace resource variables with appropriate polynomials (with pending substitutions applied)
  --   and negate the resource constraint
  let substRFml (RFormula _ _ _ subs pending f) = 
        runInSolver $ applyPolynomial mkCXPolynomial program polynomials pending subs f
  fml <- conjunction <$> mapM substRFml rfmls
  let cxQuery = fnot $ substitute program fml
  writeLog 7 $ linebreak <+> text "CEGIS counterexample query:" </> pretty cxQuery
  -- Query solver for a counterexample
  model <- runInSolver $ solveAndGetModel cxQuery
  writeLog 5 $ text "CX model:" <+> text (maybe "" snd model)
  vars <- runInSolver . sequence
    $ (modelGetAssignment (map fst (uvars universals)) <$> model)
  measures <- runInSolver . sequence
    $ (modelGetAssignment (map fst (ufuns universals)) <$> model)
  return $ CX <$> measures <*> vars <*> model

-- | 'getRelevantPreds' @rfml cx program polynomials@
-- Given a counterexample @cx@, a @program@, and a list of verification conditions @rfmls@
--   return only those violated by the model
getRelevantPreds :: RMonad s
                 => [ProcessedRFormula]
                 -> Counterexample
                 -> ResourceSolution
                 -> PolynomialSkeletons
                 -> TCSolver s [ProcessedRFormula]
getRelevantPreds rfmls cx program polynomials = do
  let runInSolver = lift . lift . lift
  evalPolynomials <- runInSolver $ mapM (mkEvalPolynomial program cx) polynomials
  let substRFml (RFormula _ _ _ subs pending f) = substAndApplyPolynomial pending evalPolynomials f
  let isRelevant rfml = not <$> checkPredWithModel (substRFml rfml) (model cx)
  runInSolver $ filterM isRelevant rfmls


-- | 'synthesize' @fml polynomials examples@
--   Find a valuation for all coefficients such that @fml@ holds on all @examples@
synthesize :: RMonad s
           => [ProcessedRFormula]
           -> [Formula]
           -> PolynomialSkeletons
           -> Counterexample
           -> TCSolver s ([Formula], Maybe ResourceSolution)
synthesize rfmls pastExamples polynomials counterexample = do
  let runInSolver = lift . lift . lift
  -- For each example, substitute its value for the universally quantified expressions in each polynomial skeleton
  paramPolynomials <- runInSolver $ mapM (mkParamPolynomial (allVariables counterexample)) polynomials
  -- Replace resource variables with appropriate polynomials after applying pending substitutions
  let substRFml (RFormula _ _ _ subs pending f) = 
        runInSolver $ applyPolynomial mkParamPolynomial (allVariables counterexample) polynomials pending subs f
  fml <- conjunction <$> mapM substRFml rfmls
  -- Substitute example valuations of universally quantified expressions in resource constraint
  -- TODO: this was commented out for some reason!! why???
  --   shouldn't be necessary...
  let fml' = substitute (allVariables counterexample) fml
  -- Evaluate the measure applications within the model from the counterexample
  -- Assert that any parameterization must hold for all examples
  let paramQuery = fml' : pastExamples
  -- Collect all parameters
  let allCoefficients = concatMap coefficientsOf (Map.elems polynomials)
  writeLog 7 $ text "CEGIS param query:" </> pretty paramQuery
  model <- runInSolver $ solveAndGetModel (conjunction paramQuery)
  writeLog 8 $ text "Param model:" <+> text (maybe "" snd model)
  sol <- runInSolver . sequence $ (modelGetAssignment allCoefficients <$> model)
  return (paramQuery, sol)

applyPolynomial :: RMonad s 
                => (Map String Formula -> Polynomial -> s Formula)
                -> Map String Formula
                -> PolynomialSkeletons
                -> Map Formula Substitution
                -> Substitution
                -> Formula 
                -> s Formula
applyPolynomial mkPolynomial vals polynomials pendingSubs subs f = 
  let sub = applyPolynomial mkPolynomial vals polynomials pendingSubs subs in 
  case f of 
    v@(Var s x)   -> 
      case Map.lookup x polynomials of 
        Nothing -> return v 
        Just p  -> 
          let pending = fromMaybe Map.empty (Map.lookup v pendingSubs)
              subst   = composeSubstitutions pending subs
              p'      = substPolynomial x subst p in
          mkPolynomial vals p' 
    SetLit s fs   -> SetLit s <$> mapM sub fs
    Unary op f    -> Unary op <$> sub f
    Binary op f g -> Binary op <$> sub f <*> sub g 
    Ite g t f     -> Ite <$> sub g <*> sub t <*> sub f
    Pred s x fs   -> Pred s x <$> mapM sub fs
    Cons s x fs   -> Cons s x <$> mapM sub fs 
    All q f       -> All q <$> sub f -- there shouldn't be foralls by now anyway
    Unknown{}     -> error "applySynthesisPolynomial: condition unknown present"
    lit           -> return lit


substAndApplyPolynomial :: Map Formula Substitution -> Map String Formula -> Formula -> Formula
substAndApplyPolynomial substs polynomials f =
  let sub = substAndApplyPolynomial substs polynomials in
  case f of
    v@(Var s x) ->
      let xpoly = Map.lookup x polynomials
          xsubst = fromMaybe Map.empty $ Map.lookup v substs
      in  maybe v (substitute xsubst) xpoly
    SetLit s fs    -> SetLit s $ map sub fs
    Unary op f     -> Unary op $ sub f
    Binary op f g  -> Binary op (sub f) (sub g)
    Ite g t f      -> Ite (sub g) (sub t) (sub f)
    Pred s x fs    -> Pred s x $ map sub fs
    Cons s x fs    -> Cons s x $ map sub fs
    -- TODO: is this OK?
    All q f        -> All q $ sub f
    ASTLit s a str -> ASTLit s a str
    Unknown _ _    -> error "substAndApplyPolynomial: condition unknown present"
    lit            -> lit

substPolynomial :: String -> Substitution -> Polynomial -> Polynomial 
substPolynomial rvar subs = map subPterm
  where 
    subPterm p@(PolynomialTerm _ Nothing) = p
    subPterm (PolynomialTerm c (Just (ustr, u))) = PolynomialTerm c (Just (ustr', u'))
      where 
        u' = substitute subs u 
        ustr' = universalToString u'  

mkCXPolynomial coeffMap poly = sumFormulas <$> mapM (pTermForCX coeffMap) poly
mkParamPolynomial cx poly = sumFormulas <$> mapM (pTermForProg cx) poly
mkSimplePolynomial cx poly = sumFormulas <$> mapM (pTermForPrinting cx) poly
mkEvalPolynomial coeffMap cx poly = sumFormulas <$> mapM (pTermForEval coeffMap cx) poly

polynomialVars poly = sumFormulas $ mapMaybe (fmap snd . universal) poly 

-- | Assemble a polynomial term, given a variable prefix and a universally quantified expression
mkPTerm :: String -> Formula -> PolynomialTerm
mkPTerm prefix fml = PolynomialTerm coeff (Just (fmlStr, fml))
  where
    coeff  = mkPolynomialVar prefix fml
    fmlStr = universalToString fml

coefficientsOf = map coefficient

defaultInterp = fzero

pTermForEval :: RMonad s => ResourceSolution -> Counterexample -> PolynomialTerm -> s Formula
pTermForEval coeffVals cx (PolynomialTerm c Nothing) =
  return $ exprValue coeffVals c
pTermForEval coeffVals cx (PolynomialTerm c (Just u)) =
  return $ exprValue coeffVals c |*| exprValue (allVariables cx) (fst u)

-- | Convert PolynomialTerm into a formula for use in the counterexample query (ie instantiate the coefficients)
pTermForCX :: RMonad s => ResourceSolution -> PolynomialTerm -> s Formula
pTermForCX coeffVals (PolynomialTerm coeff Nothing)  =
  return $ exprValue coeffVals coeff
pTermForCX coeffVals (PolynomialTerm coeff (Just u)) =
  return $ exprValue coeffVals coeff |*| mkPForm (snd u)

-- | Convert PolynomialTerm into a formula for use in the program query (ie instantiate the universals)
pTermForProg :: RMonad s => Map String Formula -> PolynomialTerm -> s Formula
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
printParams :: RMonad s => ResourceSolution -> PolynomialSkeletons -> s Doc
printParams prog polynomials = pretty <$> mapM str (Map.assocs polynomials)
  where
    str (rvar, poly)  = (\p -> text rvar <+> pretty (varsIn poly) <+> operator "=" <+> p) <$> printPolynomial poly
    varsIn p = fst <$> mapMaybe universal p
    printPolynomial p = pretty <$> mkSimplePolynomial prog p

-- Coefficient variables for resource polynomial
mkPolynomialVar :: String -> Formula -> String
mkPolynomialVar annotation f = textFrom f ++ "_" ++ toText annotation
  where
    textFrom (Var _ x) = x
    textFrom (Pred _ x fs) = x ++ show (plain (pretty fs))
    toText f = show (pretty f)

-- Initialize polynomial over universally quantified @fmls@, using variable prefix @s@
initializePolynomial :: Environment
                     -> AnnotationDomain
                     -> [UMeasure]
                     -> (String, [Formula])
                     -> Polynomial
initializePolynomial env sty ms (name, uvars) =
  constantPTerm name : initializePolynomial' env sty ms (name, uvars)

initializePolynomial' env Variable _ (name, uvars) = map (mkPTerm name) uvars
initializePolynomial' env Measure ms (name, uvars) =
  map (mkPTerm name) (allPossibleMeasureApps env uvars ms)
initializePolynomial' env Both ms rvar =
  initializePolynomial' env Variable ms rvar
  ++ initializePolynomial' env Measure ms rvar

allPossibleMeasureApps :: Environment
                       -> [Formula]
                       -> [UMeasure]
                       -> [Formula]
allPossibleMeasureApps env universals = concatMap (possibleMeasureApps env universals)

possibleMeasureApps :: Environment
                    -> [Formula]
                    -> UMeasure
                    -> [Formula]
possibleMeasureApps env universals (m, MeasureDef inS outS defs cargs post) =
  let possibleCArgs =
        Set.toList $ Map.findWithDefault Set.empty m (env^.measureConstArgs)
      sortAssignment args =
        foldl assignSorts (Just Map.empty) (zip (map sortOf args) (map snd cargs))
      mkPred args f = Pred outS m (args ++ [f])
      attemptToAssign ass f =
        (`sortSubstituteFml` f) <$> assignSorts ass (sortOf f, inS)
      tryAllUniversals args =
        map (mkPred args) $ mapMaybe (attemptToAssign (sortAssignment args)) universals
  in  concatMap tryAllUniversals possibleCArgs

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