{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

-- | Basically just a ton of types used throughout the various solvers
module Synquid.Solver.Monad where

import Synquid.Logic
import Synquid.Program
import Synquid.Type
import Synquid.Pretty
import Synquid.Util
import Synquid.Error

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Lens
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Except
import qualified Z3.Monad as Z3 
import qualified Data.Bimap as Bimap
import Data.Bimap (Bimap)

{- Types for interacting with Z3 -}

data AnnotationDomain = 
  Variable | Measure | Both
  deriving (Show, Eq)

-- | Wrapper for Z3 Model data structure
type SMTModel = (Z3.Model, String)

-- Interpretation of an uniterpreted function in a Z3 model
data Z3UFun = Z3UFun {
  _functionName :: String,
  _entries :: Map [Formula] Formula,
  _defaultVal :: Formula
} deriving (Show, Eq)

makeLenses ''Z3UFun

instance Pretty Z3UFun where
  pretty (Z3UFun m es defVal) = text "measure" <+> text m </> prettyEntries es </> prettydef 
    where 
      prettyEntries es = nest 2 $ pretty $ Map.assocs es
      prettydef = nest 2 $ pretty defVal 

class UF a where 
  argSorts :: a -> [Sort]
  resSort :: a -> Sort

{- Types for solving resource formulas -}

type PendingRSubst = Map Formula Substitution

-- RFormula : Logical formula and a set of pending substitutions
data RFormula a = RFormula {
  knownAssumptions :: !a,
  unknownAssumptions :: !a,
  varSubsts :: !Substitution,
  pendingSubsts :: !PendingRSubst,
  rformula :: !Formula
} deriving (Eq, Show, Ord)

type RawRFormula = RFormula (Set Formula) 
type ProcessedRFormula = RFormula ()

instance Pretty (RFormula a) where 
  pretty = pretty . rformula

data Z3Env = Z3Env {
  envSolver  :: Z3.Solver,
  envContext :: Z3.Context
}

-- | Z3 state while building constraints
data Z3Data = Z3Data {
  _mainEnv :: Z3Env,                          -- ^ Z3 environment for the main solver
  _sorts :: Map Sort Z3.Sort,                 -- ^ Mapping from Synquid sorts to Z3 sorts
  _vars :: Map Id Z3.AST,                     -- ^ AST nodes for scalar variables
  _functions :: Map Id Z3.FuncDecl,           -- ^ Function declarations for measures, predicates, and constructors
  _storedDatatypes :: Set Id,                 -- ^ Datatypes mapped directly to Z3 datatypes (monomorphic and non-recursive)
  _controlLiterals :: Bimap Formula Z3.AST,   -- ^ Control literals for computing UNSAT cores
  _auxEnv :: Z3Env,                           -- ^ Z3 environment for the auxiliary solver
  _boolSortAux :: Maybe Z3.Sort,              -- ^ Boolean sort in the auxiliary solver
  _controlLiteralsAux :: Bimap Formula Z3.AST -- ^ Control literals for computing UNSAT cores in the auxiliary solver
}

makeLenses ''Z3Data

type Z3State = StateT Z3Data IO

class Declarable a where 
  declare :: (Z3.MonadZ3 s, MonadState Z3Data s) => a -> (Sort -> String -> [Sort] -> s Z3.FuncDecl)

{- Monadic structure of solvers -}


class (Monad s, Applicative s) => MonadSMT s where  
  initSolver :: Environment -> s ()                                                  -- ^ Initialize solver  
  isSat :: Formula -> s Bool                                                         -- ^ 'isSat' @fml@: is @fml@ satisfiable?
  allUnsatCores :: Formula -> Formula -> [Formula] -> s [[Formula]]                  -- ^ 'allUnsatCores' @assumption@ @mustHave@ @fmls@: all minimal unsatisfiable subsets of @fmls@ with @mustHave@, which contain @mustHave@, assuming @assumption@

class (Monad s, Applicative s) => RMonad s where
  solveAndGetModel :: Formula -> s (Maybe SMTModel)                                  -- ^ 'solveAndGetModel' @fml@: Evaluate @fml@ and, if satisfiable, return the model object
  solveAndGetAssignment :: Formula -> [String] -> s (Maybe (Map String Formula))     -- ^ 'solveAndGetAssignment' @fml@ @vars@: If @fml@ is satsiable, return the assignments of variables @vars@
  modelGetAssignment :: [String] -> SMTModel -> s (Maybe (Map String Formula))       -- ^ 'modelGetAssignment' @vals@ @m@: Get assignments of all variables @vals@ in model @m@
  checkPredWithModel :: Formula -> SMTModel -> s Bool                                -- ^ 'checkWithModel' @fml model@: check if boolean-sorted formula holds under a given model

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
  _constantRes :: Bool,                                             -- ^ Check constant-timedness or not
  _cegisMax :: Int,                                                 -- ^ Maximum depth of CEGIS solver 
  _cegisDomain :: Maybe AnnotationDomain,
  _enumAndCheck ::Bool
}

makeLenses ''TypingParams

-- | Command line arguments relevant to resource analysis
data ResourceArgs = ResourceArgs {
  _checkRes :: Bool,
  _checkMults :: Bool,
  _constantTime :: Bool,
  _cegisBound :: Int,
  _enumerate :: Bool
} 

makeLenses ''ResourceArgs

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
  _resourceConstraints :: [ProcessedRFormula],  -- ^ Constraints relevant to resource analysis
  _resourceVars :: Map String [Formula],        -- ^ Set of variables created to replace potential/multiplicity annotations
  _matchCases :: Set Formula,                   -- ^ Set of all generated match cases
  -- Temporary state:
  _simpleConstraints :: [Constraint],           -- ^ Typing constraints that cannot be simplified anymore and can be converted to horn clauses or qualifier maps
  _hornClauses :: [Formula],                    -- ^ Horn clauses generated from subtyping constraints
  _consistencyChecks :: [Formula],              -- ^ Formulas generated from type consistency constraints
  _errorContext :: (SourcePos, Doc),            -- ^ Information to be added to all type errors
  _universalFmls :: Set Formula,                -- ^ Set of universally quantified resource expressions, if there are any
  _universalMeasures :: Set Formula             -- ^ Set of universally quantified measure applications, in string form
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
