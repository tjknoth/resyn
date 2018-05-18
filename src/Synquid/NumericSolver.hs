{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module Synquid.NumericSolver (
    NumericSolverParams (..),
    NumericSolver,
    runNumSolver,
    solveResourceConstraints
) where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.SolverMonad
import Synquid.Z3

import Data.Maybe 
import Data.Map hiding (partition)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.State 
import Control.Monad.Trans.Except 
import Control.Monad.Reader
import Control.Lens
import Debug.Trace

data NumericSolverParams = NumericSolverParams {
    _maxPolynomialDegree :: Int, -- ^ Maximum degree of resource polynomials
    _solverLogLevel :: Int       -- ^ How verbose logging is
} deriving (Show, Eq)

makeLenses ''NumericSolverParams

type NumericSolver s = ReaderT NumericSolverParams (ExceptT ErrorMessage s)

runNumSolver :: NumericSolverParams -> NumericSolver s a -> s (Either ErrorMessage a)
runNumSolver params go = runExceptT $ runReaderT go params 

solveResourceConstraints :: MonadSMT s => [Constraint] -> NumericSolver s ()
solveResourceConstraints constraints = do 
    let fmls = Set.fromList $ fmap generateFormula constraints 
    let query = conjunction fmls
    b <- isSatFml query
    let result = if b then "SAT" else "UNSAT"
    writeLog 2 $ text "Solving resource constraint:" <+> pretty query <+> text "--" <+> text result 
    return ()

isSatFml :: MonadSMT s => Formula -> NumericSolver s Bool
isSatFml fml = lift . lift . isSat $ fml

-- Placeholder formulas!
-- For now not computing \Phi! (or even using the conjunction of everything in the environment!)
generateFormula :: Constraint -> Formula 
generateFormula (Subtype env tl tr _ name) = conjunction fmls
  where fmls = joinAssertions (|<=|) tl tr 
generateFormula (WellFormed env t)         = conjunction $ Set.map (|>=| fzero) $ allFormulas t
generateFormula (SplitType e t tl tr)      = conjunction $ partition t tl tr
generateFormula c                          = error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c 

allFormulas :: RType -> Set Formula 
allFormulas (ScalarT base _ p) = Set.insert p (allFormulasBase base)
allFormulas _                  = Set.empty

allFormulasBase :: BaseType Formula -> Set Formula
allFormulasBase (DatatypeT _ ts _) = Set.unions $ fmap allFormulas ts
allFormulasBase (TypeVarT _ _ m) = Set.singleton m
allFormulasBase _                = Set.empty

partition :: RType -> RType -> RType -> Set Formula 
partition (ScalarT b _ f) (ScalarT bl _ fl) (ScalarT br _ fr) = Set.insert (f |=| (fl |+| fr)) $ partitionBase b bl br
partition _ _ _ = Set.empty

partitionBase :: BaseType Formula -> BaseType Formula -> BaseType Formula -> Set Formula
partitionBase (DatatypeT _ ts _) (DatatypeT _ tsl _) (DatatypeT _ tsr _) = Set.unions $ zipWith3 partition ts tsl tsr
partitionBase (TypeVarT _ _ m) (TypeVarT _ _ ml) (TypeVarT _ _ mr) = Set.singleton $ m |=| (ml |+| mr)
partitionBase _ _ _ = Set.empty

joinAssertions :: (Formula -> Formula -> Formula) -> RType -> RType -> Set Formula
joinAssertions op (ScalarT bl _ fl) (ScalarT br _ fr) = Set.insert (fl `op` fr) $ joinAssertionsBase op bl br 
joinAssertions op _ _ = Set.empty 

joinAssertionsBase :: (Formula -> Formula -> Formula) -> BaseType Formula -> BaseType Formula -> Set Formula
joinAssertionsBase op (DatatypeT _ tsl _) (DatatypeT _ tsr _) = Set.unions $ zipWith (joinAssertions op) tsl tsr
joinAssertionsBase op (TypeVarT _ _ ml) (TypeVarT _ _ mr) = Set.singleton $ ml `op` mr
joinAssertionsBase _ _ _ = Set.empty 


relevantConstraint :: Constraint -> Bool
relevantConstraint Subtype{} = True
relevantConstraint WellFormed{} = True
relevantConstraint SplitType{} = True

writeLog level msg = do 
    maxLevel <- asks _solverLogLevel
    when (level <= maxLevel) $
        traceShow (plain msg) $ return ()