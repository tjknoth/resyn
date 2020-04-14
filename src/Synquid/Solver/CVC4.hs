module Synquid.Solver.CVC4 (
  solveWithCVC4
) where

import Synquid.Solver.Types
import Synquid.Solver.Monad

import Control.Monad.State


type SYGUSSolver s = StateT SYGUSState s

runCVC4 :: SYGUSSolver s a -> SYGUSState -> s (a, SYGUSState)
runCVC4 = runStateT

solveWithCVC4 :: RMonad s
              => [ProcessedRFormula]
              -> Universals
              -> SYGUSSolver s Bool
solveWithCVC4 rfmls universals = return False -- placeholder

-- TODO: don't hardcode this!
logfile :: FilePath
logfile = "~/Research/resyn/logs/resyn.sl"

-- conduit architecture

-- source : resyn
-- sink : either a file or a cvc4 process
-- Modes:
-- resyn (source) >> file (sink) >> cvc4 process (source)
-- resyn >> cvc4 process

-- Placeholder
type SYGUSState = String

-- CEGIS problem components:
-- set logic
-- goal
-- constraint
-- footer