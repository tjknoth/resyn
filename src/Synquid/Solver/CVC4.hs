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
import Synquid.Program
import Synquid.Solver.Types
import Synquid.Solver.Monad

import           Conduit
import           Data.Conduit.Process
import qualified Data.Conduit.List as CL
import qualified Data.Text as T
import           Data.Map (Map)
import qualified Data.Map as Map
import           System.Exit

solveWithCVC4 :: RMonad s
              => Maybe String
              -> Environment
              -> Map String [Formula]
              -> [ProcessedRFormula]
              -> Universals
              -> s Bool
solveWithCVC4 withLog env rvars rfmls univs =
  let log = maybe Direct Debug withLog
   in parseSat <$> getResult log (assembleSygus env rvars rfmls univs) 

data ConstraintMode = Direct | Debug String -- pipe directly to solver, or write to file first for debugging
  deriving (Show, Eq)

data SygusGoal = SygusGoal {
  name :: Id,
  arity :: Int,
  sort :: Sort,
  args :: [(Id, Sort)]
} deriving (Show, Eq)

data SygusProblem = SygusProblem {
  declarations :: Map Id DatatypeDef,
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
      let send = yieldMany (printSygus problem) .| mapC (T.pack . show) .| unlinesC .| encodeUtf8C
      (exitCode, res, err) <- sourceCmdWithStreams cmd send -- stdin 
                                                       (decodeUtf8C .| sinkList) -- stdout 
                                                       (decodeUtf8C .| sinkList) -- stderr
      case exitCode of 
        ExitSuccess -> return res -- TODO: is there something smarter than writing all output to memory?
        ExitFailure e -> error $ "CVC4 exited with error " ++ show e ++ "\n" ++ show (head err)
    Debug logfile -> liftIO $ do 
      runResourceT $ runConduit $ yieldMany (printSygus problem) 
                               .| mapC (T.pack . show) 
                               .| unlinesC
                               .| encodeUtf8C 
                               .| sinkFile logfile  -- write to file
      let cmd = unwords $ cvc4 ++ [logfile] ++ flags 
      (exitCode, res) <- sourceCmdWithConsumer cmd (decodeUtf8C .| sinkList)
      case exitCode of 
        ExitSuccess -> return res 
        ExitFailure e -> error $ "CVC4 exited with error " ++ show e

assembleSygus :: Environment -> Map String [Formula] -> [ProcessedRFormula] -> Universals -> SygusProblem
assembleSygus env rvars rfmls univs = SygusProblem dts cs fs us
  where
    collectArgs (Var s x) = (x, s)
    buildSygusGoal x args = SygusGoal x (length args) IntS (map collectArgs args)
    cs = map (\rf -> _knownAssumptions rf |=>| _rconstraints rf) rfmls
    fs = Map.elems $ Map.mapWithKey buildSygusGoal rvars  
    us = map (\(_, Var s x) -> (x, s)) (uvars univs)
    dts = _datatypes env

---------------------------------------------
---------------------------------------------
-- Converting problem to sygus language
---------------------------------------------
---------------------------------------------

printSygus :: SygusProblem -> [Doc]
printSygus (SygusProblem _ cs fs us) = header :
  (map declareGoal fs ++ map declareUniversal us ++ map declareConstraint cs ++ [footer])

header :: Doc -- TODO: support datatypes in declaration?
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

declareData :: Id -> DatatypeDef -> Doc
declareData dt (DatatypeDef tps pps pvs cs _ _) = sexp (text "declare-datatype") [dt]

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