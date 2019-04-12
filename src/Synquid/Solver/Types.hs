{-# LANGUAGE TemplateHaskell, DeriveFunctor, FlexibleInstances #-}

-- | Different types used to interface between the different solvers
module Synquid.Solver.Types where

import Synquid.Logic
import Synquid.Pretty
import Synquid.Program

import Data.Set (Set)
import Data.Map (Map)
import qualified Z3.Monad as Z3
import Data.Functor.Foldable (Recursive(..), Corecursive(..), Base(..)) 
import Control.Lens
import Debug.Trace

-- Resource Constraint body AST

data LinearExp a = 
    LA !a !a               -- Atom: product of coefficient and variable
  | LS !Int ![LinearExp a] -- Sum of atoms
  deriving (Eq, Ord, Show, Functor)

data LinearConstraint a =
  LC !BinOp !a !a
  deriving (Eq, Ord, Show, Functor)

type FmlLE = LinearExp Formula

instance Pretty a => Pretty (LinearExp a) where 
  pretty (LA x y) = pretty x <+> text "*" <+> pretty y
  pretty (LS c xs) = pretty c <+> text "+" <+> (hsep . punctuate (text "+")) (map pretty xs)

instance Pretty a => Pretty (LinearConstraint a) where 
  pretty (LC op f g) = pretty f <+> pretty op <+> pretty g

-- | Wrapper for Z3 Model data structure
type SMTModel = (Z3.Model, String)

data AnnotationDomain = 
  Variable | Measure | Both
  deriving (Show, Eq)

{- Types for solving resource formulas -}

type PendingRSubst = Map Formula Substitution

-- RFormula : Logical formula and meta-info
data RFormula k u c = RFormula {
  _knownAssumptions :: !k,
  _unknownAssumptions :: !u,
  _renamedPreds :: !(Set Formula),
  _varSubsts :: !Substitution,
  _pendingSubsts :: !PendingRSubst,
  _rconstraints :: ![c] -- ![FmlLC]
} deriving (Eq, Show, Ord)

makeLenses ''RFormula

type RawRFormula = RFormula (Set Formula) (Set Formula) (LinearConstraint Formula)
type ProcessedRFormula = RFormula Formula () (LinearConstraint FmlLE) 

instance Pretty c => Pretty (RFormula k u c) where 
  pretty = pretty . _rconstraints

{- Types for CEGIS solver -}

-- Coefficient valuations in a valid program
type ResourceSolution = Map String Formula

-- Universally quantified variable
type UVar = (String, Formula)

-- Uninterpreted function (measure) relevant for constraint solving
type UMeasure = (String, MeasureDef)

data Universals = Universals {
  uvars :: ![UVar],
  ufuns :: ![UVar]
} deriving (Show, Eq, Ord)

-- Term of a polynomial: coefficient * universal
data PolynomialTerm = PolynomialTerm {
  coefficient :: !String,
  universal :: !(Maybe UVar)
} deriving (Eq, Show, Ord)

-- Polynomial represented as a list of coefficient-variable pairs 
type Polynomial = [PolynomialTerm]

-- Map from resource variable name to its corresponding polynomial
type PolynomialSkeletons = Map String Polynomial

-- Map from universally quantified expression (in string form) to its valuation
data Counterexample = CX {
  funcInterps :: !(Map String Formula),
  variables :: !(Map String Formula),
  model :: !SMTModel
} deriving (Eq)

data CEGISState = CEGISState {
  _rprogram :: !ResourceSolution,
  _polynomials :: !PolynomialSkeletons,
  _coefficients :: ![String],
  _cegisSolverLogLevel :: !Int,
  _counterexamples :: ![Formula]
} -- deriving (Show, Eq, Ord)

makeLenses ''CEGISState

-----------------------------------------------
-----------------------------------------------
-- Linear expressions as potential annotations
-----------------------------------------------
-----------------------------------------------

($=$)  = LC Eq
($>=$) = LC Ge 
($<=$) = LC Le 
($>$)  = LC Gt
($<$)  = LC Lt

makeLE :: Formula -> FmlLE
makeLE = LA (IntLit 1)

leToFml :: FmlLE -> Formula 
leToFml (LA f g) = f |*| g
leToFml (LS const fs)  = IntLit const |+| sumFormulas (map leToFml fs)


class Fml a where
  toFml :: a -> Formula

instance Fml Formula where 
  toFml = id

instance Fml FmlLE where 
  toFml = leToFml

instance Fml a => Fml (LinearConstraint a) where 
  toFml (LC op f g) = Binary op (toFml f) (toFml g)


bodyFml :: Fml c => RFormula k u c -> Formula 
bodyFml = conjunction . map toFml . _rconstraints

completeFml :: Fml c => RFormula Formula u c -> Formula
completeFml f = _knownAssumptions f |=>| bodyFml f

-- Combine literals when possible
multiplyLE :: Formula -> FmlLE -> FmlLE
multiplyLE f (LA coeff g) = 
  case (f, coeff) of 
    (IntLit x, IntLit y) -> LA (IntLit (x * y)) g
    _                    -> LA (f |*| coeff) g
multiplyLE f (LS c fs) = 
  case f of 
    (IntLit x) -> LS (c * x) $ map (multiplyLE f) fs
    _          -> LS 0 $ LA (IntLit c) f : map (multiplyLE f) fs

negateLE :: FmlLE -> FmlLE
negateLE = multiplyLE (IntLit (-1))

addLE :: FmlLE -> FmlLE -> FmlLE
addLE f@LA{}    g@LA{}    = LS 0 [f, g]
addLE f@LA{}    (LS c fs) = LS c (f:fs)
addLE (LS c fs) f@LA{}    = LS c (f:fs)
addLE (LS c fs) (LS d gs) = LS (c + d) (fs ++ gs)

subtractLE :: FmlLE -> Formula -> FmlLE
subtractLE le f = addLE le (negateLE (makeLE f))

leAddVar :: FmlLE -> Formula -> FmlLE 
leAddVar f@LA{} x@Var{} = LS 0 [f, makeLE x]
leAddVar (LS c fs) x@Var{} = LS c (makeLE x : fs)
leAddVar le f = error $ show $ text "leAddVar: unexpected formula" <+> pretty f

-- Convert a Formula to a FmlLE, assuming that the Formula is a sum of products 
--   with the following structure:
-- A sum, with all multiplications and negations propagated to the leaves:
--         +
--        / \
--       +   +
--      / \ 1 \
--     *   2   *
--    / \     / \
--  -1  p1   *  p2    coefficients go on the left
--          / \
--        -3   n     constant coefficients folded together
-- If @univs@ is true, expect universally quantified multipliers.
sumToLE :: Bool -> Formula -> FmlLE
sumToLE univs f = LS (constOf f) (summands univs f)

-- TODO: support ITE

constOf :: Formula -> Int
constOf = 
  let cAlg (IntLitF x)         = x
      cAlg (VarF _ _)          = 0
      cAlg (BinaryF Plus x y)  = x + y
      cAlg (BinaryF Minus x y) = x - y -- Shouldn't appear except in top-level annotation
      cAlg (BinaryF Times x y) = 0
      cAlg f                   = error $ "constOf: unexpected structure " ++ show f
  in  cata cAlg

summands :: Bool -> Formula -> [FmlLE] 
summands univs IntLit{}           = []
summands univs x@Var{}            = [makeLE x]
summands univs (Binary Plus f g)  = summands univs f ++ summands univs g
summands univs (Binary Minus c x) = summands univs $ Binary Plus c (negateFml x) -- Shouldn't appear except in top-level annotation
summands univs m@(Binary Times c x@Var{}) =
  case collapseConstants c of 
    (const, Nothing) -> [LA (IntLit const) x]
    (const, Just g)  -> if univs 
      then [LA (IntLit const |*| g) x]
      else error $ show $ text "summands: did not expect universally quantified multipliers in" <+> pretty m


collapseConstants :: Formula -> (Int, Maybe Formula)
collapseConstants (IntLit x) = (x, Nothing)
collapseConstants x@Var{}    = (1, Just x)
collapseConstants (Binary Times f g) = 
  let (fc, ff) = collapseConstants f 
      (gc, gg) = collapseConstants g in 
  (fc * gc, Binary Times <$> ff <*> gg)
collapseConstants f = error $ show $ text "collapseConstants: unexpected structure" <+> pretty f