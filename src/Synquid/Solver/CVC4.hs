module Synquid.Solver.CVC4 (
    solveWithCVC4
  , getResult -- TODO: don't export
  , asSexp -- TODO: don't export
  , ConstraintMode(..)
  , SygusProblem(..)
  , SygusGoal(..)
) where

import Synquid.Pretty
import Synquid.Logic
import Synquid.Util
import Synquid.Solver.Types
import Synquid.Solver.Monad

import           Conduit
-- import           Data.Conduit
import           Data.Conduit.Process
import qualified Data.Conduit.List as CL
import qualified Data.Text as T
import           Data.Map (Map)
-- import           Control.Monad.

solveWithCVC4 :: RMonad s
              => Maybe String
              -> Map String [Formula]
              -> [ProcessedRFormula]
              -> Universals
              -> s Bool
solveWithCVC4 withLog rvars rfmls univs =
  let log = maybe Direct Debug withLog
   in parseSat <$> getResult log (assembleSygus rvars rfmls univs) 

data ConstraintMode = Direct | Debug String -- pipe directly to solver, or write to file first for debugging
  deriving (Show, Eq)

data SygusGoal = SygusGoal {
  name :: Id,
  arity :: Int,
  sort :: Sort,
  args :: [(Id, Sort)]
} deriving (Show, Eq)

data SygusProblem = SygusProblem {
  constraints :: [Formula],
  functions :: [SygusGoal],
  universals :: [(Id, Sort)]
} deriving (Show, Eq)

-- Parse satisfiability from CVC4 output
parseSat :: String -> Bool
parseSat s = 
  let res = head $ lines s
   in res == "unsat" -- when problem is satisfiable, CVC4 outputs "unsat" for some reason...

-- get output of cvc4 as string
-- getResult :: MonadIO s => ConstraintMode -> SygusProblem -> s String
getResult :: RMonad s => ConstraintMode -> SygusProblem -> s String
getResult mode problem = unwords . map T.unpack <$>
  case mode of
    Direct -> liftIO $ do 
      let cmd = unwords $ cvc4 ++ flags
      (exitCode, res, err) <- sourceCmdWithStreams cmd (yieldMany (printSygus problem) .| mapC (T.pack . show) .| encodeUtf8C) -- stdin
                                                       (decodeUtf8C .| sinkList) -- stdout 
                                                       (decodeUtf8C .| sinkList) -- stderr
      return res -- TODO: is there something smarter than writing all output to memory?
    Debug logfile -> liftIO $ do 
      runResourceT $ runConduit $ yieldMany (printSygus problem) 
                               .| mapC (T.pack . show) 
                               .| unlinesC
                               .| encodeUtf8C 
                               .| sinkFile logfile  -- write to file
      let cmd = unwords $ cvc4 ++ [logfile] ++ flags 
      (exitCode, res) <- sourceCmdWithConsumer cmd (decodeUtf8C .| sinkList)
      return res 

assembleSygus :: Map String [Formula] -> [ProcessedRFormula] -> Universals -> SygusProblem
assembleSygus rvars rfmls univs = undefined
  

---------------------------------------------
---------------------------------------------
-- Converting problem to sygus language
---------------------------------------------
---------------------------------------------

printSygus :: SygusProblem -> [Doc]
printSygus (SygusProblem cs fs us) = header :
  (map declareGoal fs ++ map declareUniversal us ++ map declareConstraint cs ++ [footer])

header :: Doc
header = sexp (text "set-logic") ["LIA"]

footer :: Doc
footer = parens $ text "check-synth"

declareGoal :: SygusGoal -> Doc
declareGoal (SygusGoal f _ outSort args) = sexp (text "synth-fun") [text f, prettyArgs, pretty outSort]
  where
    prettyArgs = parens $ hsep $ map (\(x, s) -> parens (text x <+> pretty s)) args

declareUniversal :: (Id, Sort) -> Doc
declareUniversal (x, s) = sexp (text "declare-var") [text x, pretty s]

declareConstraint :: Formula -> Doc
declareConstraint f = sexp (text "constraint") [asSexp f]

-- Print formula to sygus language
asSexp :: Formula -> Doc
asSexp = plain . asSexp'

asSexp' f =  
 case f of
  (BoolLit True)  -> text "true"  -- need lowercase booleans
  (BoolLit False) -> text "false"
  (IntLit x)      -> pretty x
  (Var s x)       -> pretty x
  (Unary op f)    -> sexp (pretty op) [asSexp f]
  (Binary op f g) -> sexp (pretty op) [asSexp f, asSexp g]
  (Ite g t f)     -> sexp (text "ite") [asSexp g, asSexp t, asSexp f]
  (Pred s f xs)   -> sexp (text f) (map asSexp xs)
  _ -> error $ "unexpected formula sent to Sygus solver: " ++ show (pretty f)

sexp :: Pretty a => Doc -> [a] -> Doc
sexp f args = parens $ f <+> hsep (map pretty args)

cvc4 :: [String]
cvc4 = ["cvc4"]

flags :: [String]
flags = ["--lang=sygus2", "--cegqi-si=all", "--cegqi-si-abort", "--cbqi", "--cbqi-prereg-inst"]