import Test.Tasty
import Test.Tasty.HUnit
import Control.Monad
import qualified Data.Set as Set
import qualified Data.Map as Map

import Synquid.Logic
import Synquid.Parser
import Synquid.Pretty

main :: IO ()
main = runTests [ logicAST, logic ]

runTests :: [TestTree] -> IO ()
runTests groups = defaultMain $ testGroup "test" groups


doTest :: (Pretty b, Eq b) => (a -> b) -> IO a -> IO b -> Doc -> TestTree
doTest f x correct name =
    testCase (show name) $ do
        res <- f <$> x
        wrong <- (res /=) <$> correct
        msg <- errorMsg correct res
        when wrong $ assertFailure msg

mkTest :: (Pretty b, Eq b) => (a -> b) -> a -> b -> Doc -> TestTree
mkTest f x correct = doTest f (return x) (return correct)

errorMsg :: Pretty a => IO a -> a -> IO String
errorMsg right wrong = do
    rstr <- right
    return $ show $ text "Expected" <+> pretty rstr <+> text "got" <+> pretty wrong

mkFmlTest :: (Pretty b, Eq b) => (Formula -> b) -> String -> b -> Doc -> TestTree
mkFmlTest f str correct = doTest f (getArg str) (return correct)
  where
    getArg s = do
        fml <- readFormula s
        case fml of
            Left err   -> do { assertFailure (show err) ; return fzero }
            Right fml' -> return fml'

mk2FmlTest :: (Formula -> Formula) -> String -> String -> Doc -> TestTree
mk2FmlTest f str correct = doTest f (getArg str) (getArg correct)
  where
    getArg s = do
        fml <- readFormula s
        case fml of
            Left err   -> do { assertFailure (show err) ; return fzero }
            Right fml' -> return fml'

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
      , mkTest
          (hasVar Set.empty)
          u1
          False
          (text "hasVar" <+> pretty u1)
      , mkFmlTest
          (hasVar Set.empty)
          "1 + 2 + True"
          False
          (text "hasVar" <+> text "1 + 2 + True")
      , mkFmlTest
          (hasVar (Set.singleton "z"))
          f4
          True
          (text "hasVar" <+> text f4)
      , mkFmlTest
          (hasVar (Set.singleton "y"))
          f6
          True
          (text "hasVar" <+> text f6)
      , mkTest
          (hasVar (Set.singleton "x"))
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