{-# LANGUAGE TemplateHaskell #-}

-- | Interface to SMT solvers
module Synquid.Solver.Monad where

import Synquid.Logic
import Synquid.Program
import Synquid.Type
import Synquid.Pretty
import Synquid.Util
import Synquid.Error

import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Lens
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Except
import Z3.Monad (Model)


-- | Wrapper for Z3 Model data structure
type SMTModel = (Model, String)

-- Interpretation of a measure in a Z3 model
data Z3Measure = Z3Measure {
  _measureName :: String,
  _measureDef :: MeasureDef,
  _entries :: Map [Formula] Formula,
  _defaultVal :: Formula
} deriving (Show, Eq)

makeLenses ''Z3Measure

class (Monad s, Applicative s) => MonadSMT s where  
  initSolver :: Environment -> s ()                                                  -- ^ Initialize solver  
  isSat :: Formula -> s Bool                                                         -- ^ 'isSat' @fml@: is @fml@ satisfiable?
  allUnsatCores :: Formula -> Formula -> [Formula] -> s [[Formula]]                  -- ^ 'allUnsatCores' @assumption@ @mustHave@ @fmls@: all minimal unsatisfiable subsets of @fmls@ with @mustHave@, which contain @mustHave@, assuming @assumption@

class (Monad s, Applicative s) => RMonad s where
  solveAndGetModel :: Formula -> s (Maybe SMTModel)                                  -- ^ 'solveAndGetModel' @fml@: Evaluate @fml@ and, if satisfiable, return the model object
  solveAndGetAssignment :: Formula -> [String] -> s (Maybe (Map String Formula))     -- ^ 'solveAndGetAssignment' @fml@ @vars@: If @fml@ is satsiable, return the assignments of variables @vars@
  modelGetAssignment :: [String] -> SMTModel -> s (Maybe (Map String Formula))       -- ^ 'modelGetAssignment' @vals@ @m@: Get assignments of all variables @vals@ in model @m@
  modelGetMeasures :: [(String, MeasureDef)] -> SMTModel -> s (Map String Z3Measure) -- ^ 'modelGetMeasures' @ms model@: Get interpretations of all measures @ms@ given @model@
  evalInModel :: [Formula] -> SMTModel -> Z3Measure -> s Formula
  

class (Monad s, Applicative s) => MonadHorn s where
  initHornSolver :: Environment -> s Candidate                                                -- ^ Initial candidate solution
  preprocessConstraint :: Formula -> s [Formula]                                              -- ^ Convert a Horn clause to the format this solver can handle
  checkCandidates :: Bool -> [Formula] -> ExtractAssumptions ->[Candidate] -> s [Candidate]   -- ^ Check validity or consistency of constraints under current candidates
  refineCandidates :: [Formula] -> QMap -> ExtractAssumptions -> [Candidate] -> s [Candidate] -- ^ Refine current candidates to satisfy new constraints
  pruneQualifiers :: QSpace -> s QSpace                                                       -- ^ Prune redundant qualifiers
 
-- | Parameters of type constraint solving
data TypingParams = TypingParams {
  _condQualsGen :: Environment -> [Formula] -> QSpace,              -- ^ Qualifier generator for conditionals
  _matchQualsGen :: Environment -> [Formula] -> QSpace,             -- ^ Qualifier generator for match scrutinees
  _typeQualsGen :: Environment -> Formula -> [Formula] -> QSpace,   -- ^ Qualifier generator for types
  _predQualsGen :: Environment -> [Formula] -> [Formula] -> QSpace, -- ^ Qualifier generator for bound predicates
  _tcSolverSplitMeasures :: Bool,
  _tcSolverLogLevel :: Int,                                         -- ^ How verbose logging is
  _checkResourceBounds :: Bool,                                     -- ^ Is resource checking enabled
  _checkMultiplicities :: Bool,                                     -- ^ Should multiplicities be considered when generating resource constraints
  _instantiateUnivs :: Bool,                                        -- ^ When solving exists-forall constraints, instantiate universally quantified expressions
  _constantRes :: Bool,                                             -- ^ Check constant-timedness or not
  _cegisMax :: Int                                                  -- ^ Maximum number of iterations through the CEGIS loop
}

makeLenses ''TypingParams

-- | Command line arguments relevant to resource analysis
data ResourceArgs = ResourceArgs {
  _checkRes :: Bool,
  _checkMults :: Bool,
  _instantiateForall :: Bool,
  _constantTime :: Bool,
  _cegisBound :: Int 
} 

makeLenses ''ResourceArgs

-- Store either the generated formulas or the entire constraint (if the resource bounds include universal quantifiers)
type RConstraint = Either TaggedConstraint Constraint

-- | State of type constraint solving
data TypingState = TypingState {
  -- Persistent state:
  _typingConstraints :: [Constraint],           -- ^ Typing constraints yet to be converted to horn clauses
  _typeAssignment :: TypeSubstitution,          -- ^ Current assignment to free type variables
  _predAssignment :: Substitution,              -- ^ Current assignment to free predicate variables  _qualifierMap :: QMap,
  _qualifierMap :: QMap,                        -- ^ Current state space for predicate unknowns
  _candidates :: [Candidate],                   -- ^ Current set of candidate liquid assignments to unknowns
  _initEnv :: Environment,                      -- ^ Initial environment
  _idCount :: Map String Int,                   -- ^ Number of unique identifiers issued so far
  _isFinal :: Bool,                             -- ^ Has the entire program been seen?
  _resourceConstraints :: [RConstraint],        -- ^ Constraints relevant to resource analysis
  _resourceVars :: Set String,                  -- ^ Set of variables created to replace potential/multiplicity annotations
  _resourceMeasures :: Map String MeasureDef,   -- ^ List of measure definitions used in resource annotations
  -- Temporary state:
  _simpleConstraints :: [Constraint],           -- ^ Typing constraints that cannot be simplified anymore and can be converted to horn clauses or qualifier maps
  _hornClauses :: [Formula],                    -- ^ Horn clauses generated from subtyping constraints
  _consistencyChecks :: [Formula],              -- ^ Formulas generated from type consistency constraints
  _errorContext :: (SourcePos, Doc),            -- ^ Information to be added to all type errors
  _universalFmls :: Maybe (Set Formula)         -- ^ Set of universally quantified resource expressions, if there are any
}

makeLenses ''TypingState

-- | Computations that solve type constraints, parametrized by the the horn solver @s@
type TCSolver s = StateT TypingState (ReaderT TypingParams (ExceptT ErrorMessage s))

-- | 'runTCSolver' @params st go@ : execute a typing computation @go@ with typing parameters @params@ in a typing state @st@
runTCSolver :: TypingParams -> TypingState -> TCSolver s a -> s (Either ErrorMessage (a, TypingState))
runTCSolver params st go = runExceptT $ runReaderT (runStateT go st) params


instance Eq TypingState where
  (==) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (_idCount st1) == restrictDomain (Set.fromList ["a", "u"]) (_idCount st2)) &&
                  _typeAssignment st1 == _typeAssignment st2 &&
                  _candidates st1 == _candidates st2

instance Ord TypingState where
  (<=) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (_idCount st1) <= restrictDomain (Set.fromList ["a", "u"]) (_idCount st2)) &&
                _typeAssignment st1 <= _typeAssignment st2 &&
                _candidates st1 <= _candidates st2
