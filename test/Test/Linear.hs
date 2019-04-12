module Test.Linear (
    runLinearTests
) where

import Common
import Synquid.Logic
import Synquid.Parser
import Synquid.Solver.Types

import Test.Tasty

runLinearTests = runTests []

conversion :: TestTree
conversion = testGroup "CONVERSION TO LC" 
  []