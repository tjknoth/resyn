{-# LANGUAGE DataKinds #-}

module Synquid.Solver.LP where

import Synquid.Logic
import Synquid.Pretty
import Synquid.Solver.Types

import Numeric.Limp.Program.Linear
import Numeric.Limp.Program.ResultKind (K(..))
import Numeric.Limp.Rep.IntDouble
import qualified Numeric.Limp.Program.Constraint as C

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

trivialLinear :: Linear String String IntDouble 'KR
trivialLinear = r1 "test" 


makeAtom :: FmlLE -> (Either z String, R IntDouble)
makeAtom (LA (IntLit x) (Var _ name)) = (Right name, R (fromIntegral x))
makeAtom a@LA{} = error $ show $ text "makeAtom: non-canonical atomic term" <+> pretty a
makeAtom a      = error $ show $ text "makeAtom: non-atomic term" <+> pretty a

lcToConstraint :: FmlLC -> C.Constraint z String IntDouble
lcToConstraint (LC op f g) = leToLinear f `op'` leToLinear g
  where 
    op' = case op of 
      Eq -> (C.:==)
      Ge -> (C.:>=) 
      Le -> (C.:<=) 

leToLinear :: FmlLE -> Linear z String IntDouble 'KR 
leToLinear f@LA{}    = LR [makeAtom f] (R 0)
leToLinear (LS c fs) = LR (map makeAtom fs) (R (fromIntegral c))
