{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

-- | Monadic structure of solvers
module Synquid.Solver.Monad where

import Synquid.Logic
import Synquid.Program
import Synquid.Type
import Synquid.Pretty
import Synquid.Util
import Synquid.Error
import Synquid.Solver.Types

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Lens
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Except

{- Monadic structure of solvers -}

class (Monad s, Applicative s, MonadFail s) => MonadSMT s where  
  initSolver :: Environment -> s ()                                                  -- ^ Initialize solver  
  isSat :: Formula -> s Bool                                                         -- ^ 'isSat' @fml@: is @fml@ satisfiable?
  allUnsatCores :: Formula -> Formula -> [Formula] -> s [[Formula]]                  -- ^ 'allUnsatCores' @assumption@ @mustHave@ @fmls@: all minimal unsatisfiable subsets of @fmls@ with @mustHave@, which contain @mustHave@, assuming @assumption@

class (Monad s, Applicative s, MonadIO s) => RMonad s where
  solveAndGetModel :: Formula -> s (Maybe SMTModel)                                  -- ^ 'solveAndGetModel' @fml@: Evaluate @fml@ and, if satisfiable, return the model object
  optimizeAndGetModel :: Formula -> [(String, Maybe Formula)] -> s (Maybe SMTModel)  -- ^ 'optimizeAndGetModel' @fml vs@: Evaluate @fml@ and optimize for inferred potl vars @vs@ in decreasing order of importance; if satisfiable, return the model object. @vs@ is a listified map from the name of the var to its previous value as a formula, if it has one.
  modelGetAssignment :: [String] -> SMTModel -> s RSolution                          -- ^ 'modelGetAssignment' @vals@ @m@: Get assignments of all variables @vals@ in model @m@
  checkPredWithModel :: Formula -> SMTModel -> s Bool                                -- ^ 'checkWithModel' @fml model@: check if boolean-sorted formula holds under a given model
  filterPreds :: [ProcessedRFormula] -> SMTModel -> s [ProcessedRFormula]
  translate :: Formula -> s Formula

class (Monad s, Applicative s, MonadFail s) => MonadHorn s where
  initHornSolver :: Environment -> s Candidate                                                -- ^ Initial candidate solution
  preprocessConstraint :: Formula -> s [Formula]                                              -- ^ Convert a Horn clause to the format this solver can handle
  checkCandidates :: Bool -> [Formula] -> ExtractAssumptions ->[Candidate] -> s [Candidate]   -- ^ Check validity or consistency of constraints under current candidates
  refineCandidates :: [Formula] -> QMap -> ExtractAssumptions -> [Candidate] -> s [Candidate] -- ^ Refine current candidates to satisfy new constraints
  pruneQualifiers :: QSpace -> s QSpace                                                       -- ^ Prune redundant qualifiers

-- | Command line arguments relevant to resource analysis
data ResourceParams = ResourceParams {
  _shouldCheckResources :: Bool,
  _checkMultiplicities :: Bool,
  _constantTime :: Bool,
  _cegisBound :: Int,
  _enumerate :: Bool,
  _inferResources :: Bool,
  _rsolver :: ResourceSolver,
  _sygusLog :: Maybe String,
  _cvc4 :: String,
  _rSolverDomain :: RDomain,
  _polynomialDomain :: RDomain
} 

makeLenses ''ResourceParams

-- | Parameters of type constraint solving
data TypingParams = TypingParams {
  _condQualsGen :: Environment -> [Formula] -> QSpace,              -- ^ Qualifier generator for conditionals
  _matchQualsGen :: Environment -> [Formula] -> QSpace,             -- ^ Qualifier generator for match scrutinees
  _typeQualsGen :: Environment -> Formula -> [Formula] -> QSpace,   -- ^ Qualifier generator for types
  _predQualsGen :: Environment -> [Formula] -> [Formula] -> QSpace, -- ^ Qualifier generator for bound predicates
  _tcSolverSplitMeasures :: Bool,
  _tcSolverLogLevel :: Int,                                         -- ^ How verbose logging is
  _resourceArgs :: ResourceParams
}

makeLenses ''TypingParams

-- | Typing state that could potentially persist across checking multiple functions
data PersistentTState = PersistentTState
  { _idCount :: Map String Int                   -- ^ Number of unique identifiers issued so far
  , _versionCount :: Map String Int              -- ^ Number of unique identifiers issued so far
  , _resourceConstraints :: [ProcessedRFormula]  -- ^ Constraints relevant to resource analysis
  , _resourceVars :: Map Id [Formula]            -- ^ Set of variables created to replace potential/multiplicity annotations; maps from name of potl var to arguments the potl var depends on
  , _inferredRVars :: PotlSubstitution           -- ^ A map from the id of an inferred variable to the formula we think it has, if it's already been inferred
  , _universalVars :: Set Id                     -- ^ Set of universally quantified resource expressions, if there are any
  , _universalMeasures :: Set Formula            -- ^ Set of universally quantified measure applications, in string form
  } deriving (Show)

makeLenses ''PersistentTState

-- | State of type constraint solving
data TypingState = TypingState {
  _persistentState :: PersistentTState,          -- ^ Persistent state which is preserved across fns
  _typingConstraints :: [Constraint],           -- ^ Typing constraints yet to be converted to horn clauses
  _typeAssignment :: TypeSubstitution,          -- ^ Current assignment to free type variables
  _predAssignment :: Substitution,              -- ^ Current assignment to free predicate variables  _qualifierMap :: QMap,
  _qualifierMap :: QMap,                        -- ^ Current state space for predicate unknowns
  _candidates :: [Candidate],                   -- ^ Current set of candidate liquid assignments to unknowns
  _initEnv :: Environment,                      -- ^ Initial environment
  _isFinal :: Bool,                             -- ^ Has the entire program been seen?
  _matchCases :: Set Formula,                   -- ^ Set of all generated match cases
  _cegisState :: CEGISState,                    -- ^ Current state of CEGIS solver
  _solveResConstraints :: Bool,                 -- ^ Whether to actually solve resource constraints or just collect them
  -- Temporary state:
  _simpleConstraints :: [Constraint],           -- ^ Typing constraints that cannot be simplified anymore and can be converted to horn clauses or qualifier maps
  _hornClauses :: [Formula],                    -- ^ Horn clauses generated from subtyping constraints
  _consistencyChecks :: [Formula],              -- ^ Formulas generated from type consistency constraints
  _errorContext :: (SourcePos, Doc)             -- ^ Information to be added to all type errors
}

makeLenses ''TypingState


-- | Computations that solve type constraints, parametrized by the the horn solver @s@
type TCSolver s = StateT TypingState (ReaderT TypingParams (ExceptT ErrorMessage s))

-- | 'runTCSolver' @params st go@ : execute a typing computation @go@ with typing parameters @params@ in a typing state @st@
runTCSolver :: TypingParams -> TypingState -> TCSolver s a -> s (Either ErrorMessage (a, TypingState))
runTCSolver params st go = runExceptT $ runReaderT (runStateT go st) params


instance Eq TypingState where
  (==) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (st1 ^. (persistentState . idCount)) == restrictDomain (Set.fromList ["a", "u"]) (st2 ^. (persistentState . idCount))) &&
                  _typeAssignment st1 == _typeAssignment st2 &&
                  _candidates st1 == _candidates st2

instance Ord TypingState where
  (<=) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (st1 ^. (persistentState . idCount)) <= restrictDomain (Set.fromList ["a", "u"]) (st2 ^. (persistentState . idCount))) &&
                _typeAssignment st1 <= _typeAssignment st2 &&
                _candidates st1 <= _candidates st2
