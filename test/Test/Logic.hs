module Test.Logic (
    runLogicTests
) where

import Common
import Synquid.Logic 
import Synquid.Parser
import Synquid.Pretty

import Test.Tasty
import qualified Data.Set as Set
import qualified Data.Map as Map

runLogicTests = runTests [ logicAST, logic ] 

logicAST :: TestTree
logicAST =
  let f1 = "x + y - z"
      f2 = "if x > 0 then 1 else z"
      f3 = ffalse
      f4 = "if elem x [1,2,z] then y else (y + z)"
      f5 = All (var "x") (fneg (var "x" |>=| fzero))
      f6 = "(pred f) && (if elem x [1,2,z] then y else (y + z))"
      u1 = Unknown Map.empty "u"
      u2 = Unknown Map.empty "t"
      var = Var AnyS
  in  testGroup "LOGIC AST"
      [ mkFmlTest
          varsOf
          f1
          (Set.fromList [var "x", var "y", var "z"])
          (text "varsOf" <+> text f1)
      , mkFmlTest
          varsOf
          f2
          (Set.fromList [var "x", var "z"])
          (text "varsOf" <+> text f2)
      , mkTest
          varsOf
          f3
          Set.empty
          (text "varsOf" <+> pretty f3)
      , mkFmlTest
          varsOf
          f4
          (Set.fromList [var "x", var "z", var "y"])
          (text "varsOf" <+> text f4)
      , mkTest
          varsOf
          f5
          Set.empty
          (text "varsOf" <+> pretty f5)
      , mkTest
          unknownsOf
          (u1 |&| u2)
          (Set.fromList [u1, u2])
          (text "unknownsOf" <+> pretty (u1 |&| u2))
      , mkTest
          unknownsOf
          (u1 |&| u2 ||| u2)
          (Set.fromList [u1, u2])
          (text "unknownsOf" <+> pretty (u1 |&| u2 ||| u2))
      , mkTest
          unknownsOf
          f5
          Set.empty
          (text "unknownsOf" <+> pretty f5)
      , mkFmlTest
          predsOf
          f4
          (Set.singleton "elem")
          (text "predsOf" <+> text f4)
      , mkFmlTest
          predsOf
          f2
          Set.empty
          (text "predsOf" <+> text f2)
      , mkFmlTest
          predsOf
          f6
          (Set.fromList ["pred", "elem"])
          (text "predsOf" <+> text f6)
      , mkFmlTest
          hasPred
          f1
          False
          (text "hasPred" <+> text f1)
      , mkFmlTest
          hasPred
          f4
          True
          (text "hasPred" <+> text f4)
      , mkFmlTest
          hasPred
          f6
          True
          (text "hasPred" <+> text f6)
      , mkTest
          hasPred
          f5
          False
          (text "hasPred" <+> pretty f5)
      , mkTest
          hasVar
          u1
          False
          (text "hasVar" <+> pretty u1)
      , mkFmlTest
          hasVar
          "1 + 2 + True"
          False
          (text "hasVar" <+> text "1 + 2 + True")
      , mkFmlTest
          hasVar
          f4
          True
          (text "hasVar" <+> text f4)
      , mkFmlTest
          hasVar
          f6
          True
          (text "hasVar" <+> text f6)
      , mkTest
          hasVar
          f5
          True
          (text "hasVar" <+> pretty f5)
      , mkFmlTest
          isExecutable
          f1
          True
          (text "isExecutable" <+> text f1)
      , mkTest
          isExecutable
          f3
          True
          (text "isExecutable" <+> pretty f3)
      , mkFmlTest
          isExecutable
          f4
          False
          (text "isExecutable" <+> pretty f4)
      , mkTest
          isExecutable
          f5
          False
          (text "isExecutable" <+> pretty f5)
      ]

logic :: TestTree
logic =
  let var = Var AnyS
      subst = Map.fromList [("x", var "foo")]
      pretty' = pretty . Map.assocs
      f1 = "x + y - z"
      f2 = "foo + y - z"
  in  testGroup "LOGIC"
  [  mk2FmlTest
      (substitute subst)
      f1
      f2
      (text "substitute" <+> pretty' subst <+> text "in" <+> text f1)
  , mk2FmlTest
      (substitute subst)
      f2
      f2
      (text "substitute" <+> pretty' subst <+> text "in" <+> text f2)
  ]