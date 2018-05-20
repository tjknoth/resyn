{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module Synquid.NumericSolver (
    NumericSolverParams (..),
    NumericSolver,
    runNumSolver,
    solveResourceConstraints,
    isResourceConstraint
) where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.SolverMonad
import Synquid.Z3

import Data.Maybe 
import Data.Map hiding (partition, filter)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.State 
import Control.Monad.Trans.Except 
import Control.Monad.Reader
import Control.Lens
import Debug.Trace

data NumericSolverParams = NumericSolverParams {
    _maxPolynomialDegree :: Int,   -- ^ Maximum degree of resource polynomials
    _solverLogLevel :: Int         -- ^ How verbose logging is
} deriving (Show, Eq)

makeLenses ''NumericSolverParams

type NumericSolver s = ReaderT NumericSolverParams s

runNumSolver :: NumericSolverParams -> NumericSolver s a -> s a 
runNumSolver params go = runReaderT go params 

solveResourceConstraints :: MonadSMT s => Formula -> [Constraint] -> NumericSolver s (Maybe Formula) 
solveResourceConstraints oldConstraints constraints = do
    fmlList <- mapM generateFormula constraints
    -- Filter out trivial constraints, mostly for readability
    let fmls = Set.fromList (filter (not . isTrivial) fmlList)
    let query = conjunction fmls
    b <- isSatFml (oldConstraints |&| query)
    let result = if b then "SAT" else "UNSAT"
    writeLog 4 $ text "Old constraints" <+> pretty oldConstraints
    writeLog 3 $ text "Solving resource constraint:" <+> pretty query <+> text "--" <+> text result 
    if b then return $ Just query 
         else return Nothing 

isSatFml :: MonadSMT s => Formula -> NumericSolver s Bool
isSatFml fml = lift . isSat $ fml

-- Placeholder formulas!
-- For now not computing \Phi! (or even using the conjunction of everything in the environment!)
generateFormula :: MonadSMT s => Constraint -> NumericSolver s Formula 
generateFormula c@(Subtype env tl tr _ name) = do 
    let fmls = conjunction $ joinAssertions (|=|) tl tr
    writeLog 2 (nest 2 $ text "Resource constraint:" <+> pretty c $+$ text "Gives" <+> pretty fmls)
    return fmls  
generateFormula c@(WellFormed env t)         = do
    let fmls = conjunction $ Set.map (|>=| fzero) $ allFormulas t
    writeLog 2 (nest 2 $ text "Resource constraint:" <+> pretty c $+$ text "Gives" <+> pretty fmls)
    return fmls
generateFormula c@(SplitType e v t tl tr)      = do 
    let fmls = conjunction $ partition t tl tr
    writeLog 2 (nest 2 $ text "Resource constraint:" <+> pretty c $+$ text "Gives" <+> pretty fmls)
    return fmls
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
joinAssertionsBase op (TypeVarT _ _ ml) (TypeVarT _ _ mr) = 
    if isTrivial fml 
        then Set.empty 
        else Set.singleton $ ml `op` mr
    where fml = ml `op` mr
joinAssertionsBase _ _ _ = Set.empty 


isResourceConstraint :: Constraint -> Bool
isResourceConstraint Subtype{} = True
isResourceConstraint WellFormed{} = True
isResourceConstraint SplitType{} = True

-- Remove some trivial resources constraints (ie 0 == 0...)
isTrivial :: Formula -> Bool
isTrivial (BoolLit True)    = True 
isTrivial (Binary Eq f1 f2) = f1 == f2
isTrivial _                 = False 


writeLog level msg = do 
    maxLevel <- asks _solverLogLevel
    when (level <= maxLevel) $
        traceShow (plain msg) $ return ()