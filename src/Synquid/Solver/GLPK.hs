module Synquid.Solver.GLPK (
    solveGLPK
) where

import Synquid.Logic
import Synquid.Pretty
import Synquid.Solver.Monad
import Synquid.Solver.Types

import Data.Map (Map)
import qualified Data.Map as Map 
import Control.Monad.LPMonad


-------------------------------------
-------------------------------------
-- Interface to GLPK LP solver
-------------------------------------
-------------------------------------

solveGLPK :: Monad s => [ProcessedRFormula] -> TCSolver s Bool
solveGLPK rfmls = fst <$> runLPT (solve rfmls)

solve :: Monad s => [ProcessedRFormula] -> LPT String Int (TCSolver s) Bool
solve rfmls = return True