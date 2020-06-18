{-# LANGUAGE TemplateHaskell, DeriveFunctor #-}

-- | Different types used to interface between the different solvers
module Synquid.Solver.Types where

import Synquid.Logic
import Synquid.Pretty
import Synquid.Program

import Data.Set (Set)
import Data.Map (Map)
import qualified Z3.Monad as Z3
import Control.Lens

data ResourceSolver = CVC4 | CEGIS | Incremental
  deriving (Show)

-- Resource Constraint body AST

data LinearExp a = 
    LA !a !a               -- Atom: product of coefficient and variable
  | LS !Int ![LinearExp a] -- Sum of atoms
  deriving (Eq, Ord, Show, Functor)

data LinearConstraint a =
  LC !BinOp !(LinearExp a) !(LinearExp a)
  deriving (Eq, Ord, Show, Functor)

type FmlLE = LinearExp Formula
type FmlLC = LinearConstraint Formula

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

instance Semigroup AnnotationDomain where
 Variable <> Variable = Variable
 Variable <> _ = Both
 Measure <> Measure = Measure
 Measure <> _ = Both
 _ <> _ = Both
 

{- Types for solving resource formulas -}

type PendingRSubst = Map Formula Substitution

-- RFormula : Logical formula and meta-info
data RFormula a b = RFormula {
  _knownAssumptions :: !a,
  _unknownAssumptions :: !b,
  _renamedPreds :: !(Set Formula),
  _varSubsts :: !Substitution,
  _pendingSubsts :: !PendingRSubst,
  _rconstraints :: !Formula -- ![FmlLC]
} deriving (Eq, Show, Ord)

makeLenses ''RFormula

type RawRFormula = RFormula (Set Formula) (Set Formula)
type ProcessedRFormula = RFormula Formula () 

instance Pretty (RFormula a b) where 
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

lcToFml :: FmlLC -> Formula 
lcToFml (LC op fs gs) = Binary op (leToFml fs) (leToFml gs)

bodyFml :: RFormula a b -> Formula 
bodyFml = _rconstraints -- conjunction . map lcToFml . _rconstraints

completeFml :: RFormula Formula b -> Formula
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
