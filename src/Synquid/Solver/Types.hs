{-# LANGUAGE TemplateHaskell #-}

-- | Different types used to interface between the different solvers
module Synquid.Solver.Types where

import Synquid.Logic
import Synquid.Pretty
import Synquid.Program

import Data.Set (Set)
import Data.Map (Map)
import qualified Z3.Monad as Z3
import Control.Lens

-- | Wrapper for Z3 Model data structure
type SMTModel = (Z3.Model, String)

data AnnotationDomain = 
  Variable | Measure | Both
  deriving (Show, Eq)

{- Types for solving resource formulas -}

type PendingRSubst = Map Formula Substitution

-- RFormula : Logical formula and meta-info
data RFormula a b = RFormula {
  _knownAssumptions :: !a,
  _unknownAssumptions :: !b,
  _renamedPreds :: !(Set Formula),
  _varSubsts :: !Substitution,
  _pendingSubsts :: !PendingRSubst,
  _rformula :: !Formula
} deriving (Eq, Show, Ord)

makeLenses ''RFormula

type RawRFormula = RFormula (Set Formula) (Set Formula)
type ProcessedRFormula = RFormula Formula () 

instance Pretty (RFormula a b) where 
  pretty = pretty . _rformula

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
  _cegisSolverLogLevel :: !Int
} -- deriving (Show, Eq, Ord)

makeLenses ''CEGISState