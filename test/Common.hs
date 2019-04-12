module Common where 

import Synquid.Logic
import Synquid.Parser
import Synquid.Pretty

import Test.Tasty
import Test.Tasty.HUnit
import Control.Monad


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