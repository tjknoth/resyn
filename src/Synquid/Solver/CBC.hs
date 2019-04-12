{-# LANGUAGE DataKinds #-}

module Synquid.Solver.CBC (
  solveCBC
) where

import Synquid.Logic
import Synquid.Pretty
import Synquid.Solver.Monad
import Synquid.Solver.Types

import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace
import Numeric.Limp.Program.Linear
import Numeric.Limp.Program.ResultKind (K(..))
import Numeric.Limp.Rep.IntDouble
import Numeric.Limp.Rep.Rep (rOf)
import Numeric.Limp.Program.Program 
import Numeric.Limp.Solvers.Cbc
import qualified Numeric.Limp.Program.Constraint as C

---------------------------------------
---------------------------------------
-- Interface to COIN-OR CBC solver
---------------------------------------
---------------------------------------

{-
solveAndGetAssignment :: [String] -> [ProcessedRFormula] -> Maybe (Map String Formula)
solveAndGetAssignment vars rfmls = 
  let constraints = concatMap (map lcToConstraint . _rconstraints) rfmls
      fml = foldl (C.:&&) C.CTrue constraints
      prog = program Minimise trivialLinear fml [] 
      mkPair ass v = (v, IntLit (truncate (unwrapR (rOf ass v)))) in
  case solve prog of 
    Left err -> trace ("LP solver error: " ++ show err) Nothing
    Right ass -> Just $ Map.fromList $ map (mkPair ass) vars 
-}

solveCBC :: Monad s => [ProcessedRFormula] -> TCSolver s Bool
solveCBC rfmls = do 
  let constraints = concatMap (map lcToConstraint . _rconstraints) rfmls
  let fml = foldl (C.:&&) C.CTrue constraints
  let prog = program Minimise objective fml []
  case solve prog of 
    Left err -> do 
      traceM $ "LP solver error: " ++ show err
      return False
    Right _  -> return True

-- This is a hack: the optimization problem needs to range over some resource variable
--  that occurs in the constraints. Hopefully "fp1" always shows up.
objective :: Linear String String IntDouble 'KR
objective = r1 "fp1" 

makeAtom :: FmlLE -> (Either z String, R IntDouble)
makeAtom (LA (IntLit x) (Var _ name)) = (Right name, R (fromIntegral x))
makeAtom a@LA{} = error $ show $ text "makeAtom: non-canonical atomic term" <+> pretty a
makeAtom a      = error $ show $ text "makeAtom: non-atomic term" <+> pretty a

lcToConstraint :: LinearConstraint FmlLE -> C.Constraint String String IntDouble
lcToConstraint (LC op f g) = leToLinear f `op'` leToLinear g
  where 
    op' = case op of 
      Eq -> (C.:==)
      Ge -> (C.:>=) 
      Le -> (C.:<=) 

leToLinear :: FmlLE -> Linear String String IntDouble 'KR 
leToLinear f@LA{}    = LR [makeAtom f] (R 0)
leToLinear (LS c fs) = LR (map makeAtom fs) (R (fromIntegral c))
