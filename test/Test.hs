import Test.Tasty
import Test.Tasty.HUnit
import Control.Monad
import qualified Data.Set as Set
import qualified Data.Map as Map

import Test.Logic
import Test.Linear

import Synquid.Logic
import Synquid.Parser
import Synquid.Pretty

main :: IO ()
main = do 
  runLogicTests 
  runLinearTests