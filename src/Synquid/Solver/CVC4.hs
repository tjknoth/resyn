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
import           Control.Lens
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
   in getResult log (assembleSygus env rvars rfmls univs)

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
getResult :: RMonad s => ConstraintMode -> SygusProblem -> s Bool
getResult mode problem =
  case mode of
    Direct -> liftIO $ do 
      let cmd = unwords $ cvc4 ++ flags
      let send = yieldMany (printSygus problem) .| mapC (T.pack . show) .| unlinesC .| encodeUtf8C
      (exitCode, res, err) <- sourceCmdWithStreams cmd send -- stdin 
                                                       (decodeUtf8C .| sinkList) -- stdout 
                                                       (decodeUtf8C .| sinkList) -- stderr
      case exitCode of 
        ExitSuccess -> error "yeehaw"
        ExitFailure e -> error $ "CVC4 exited with error " ++ show e ++ "\n" ++ show (head err)
    Debug logfile -> liftIO $ do 
      runResourceT $ runConduit $ yieldMany (printSygus problem) 
                               .| mapC (T.pack . show) 
                               .| unlinesC
                               .| encodeUtf8C 
                               .| sinkFile logfile  -- write to file
      let cmd = unwords $ cvc4 ++ [logfile] ++ flags
      (exitCode, res) <- sourceCmdWithConsumer cmd (decodeUtf8C .| sinkList)
      let r = parseSat $ unwords $ map T.unpack res
      case exitCode of 
        ExitSuccess -> return r
        ExitFailure e -> error $ "CVC4 exited with error " ++ show e

assembleSygus :: Environment -> Map String [Formula] -> [ProcessedRFormula] -> Universals -> SygusProblem
assembleSygus env rvars rfmls univs = SygusProblem dts cs fs us
  where
    isData (DataS _ _) = True
    isData _ = False
    collectArgs (Var s x) = (x, s)

    buildSygusGoal x args = SygusGoal x (length args) IntS (map collectArgs args)
    vs = fmap (filter (not . isData . sortOf)) rvars  
    cs = map (\rf -> _knownAssumptions rf |=>| _rconstraints rf) $ transformFmls vs rfmls
    fs = Map.elems $ Map.mapWithKey buildSygusGoal vs
    us = map (\(_, Var s x) -> (x, s)) (uvars univs)
    dts = _datatypes env

-- | Applies two transformations to each formula to make them usable
-- | for CVC4:
-- |
-- | 1. Fresh annotations are changed from variables to function applications
-- | 2. Any operations which exist only in the Synquid logic are transformed
-- |    to their equivalent SyGuS forms
transformFmls :: Map String [Formula] -- ^ We assume each list of formulas contains vars only, no datatypes
              -> [ProcessedRFormula]
              -> [ProcessedRFormula]
transformFmls rvars rfmls = fmap (\fml -> over rconstraints (substitute (_varSubsts fml) . xf) fml) rfmls
  where
    -- We combine both transforms into the same function
    -- This is probably poor form, but it also probably helps
    -- with performance (only traversing through each formula once)

    -- Transforms for SyGuS ops
    xf (Binary Neq f1 f2) = Unary Not (Binary Eq (xf f1) (xf f2))
    xf (Binary Iff f1 f2) = Binary And (Binary Implies x1 x2) (Binary Implies x2 x1)
      where
        x1 = xf f1
        x2 = xf f2

    -- Transforms for fresh vars -> fns
    xf (Var IntS v) = Pred IntS v $ Map.findWithDefault [] v rvars

    -- Everything else
    xf (SetLit s fs) = SetLit s (xf <$> fs)
    xf (Unary o f) = Unary o (xf f)
    xf (Binary o f1 f2) = Binary o (xf f1) (xf f2)
    xf (Ite i t e) = Ite (xf i) (xf t) (xf e)
    xf (Pred s i fs) = Pred s i (xf <$> fs)
    xf (Cons s i fs) = Cons s i (xf <$> fs)
    xf (All fs gs) = All (xf fs) (xf gs)
    xf x = x

---------------------------------------------
---------------------------------------------
-- Converting problem to sygus language
---------------------------------------------
---------------------------------------------

prettyMono :: Sort -> Doc
prettyMono (VarS _)    = pretty IntS
prettyMono (DataS d _) = error $ "prettyMono: found data sort " ++ d
prettyMono s           = pretty s

printSygus :: SygusProblem -> [Doc]
printSygus (SygusProblem _ cs fs us) = header :
  (map declareGoal fs ++ map declareUniversal us ++ map declareConstraint cs ++ [footer])

header :: Doc -- TODO: support datatypes in declaration?
header = sexp (text "set-logic") ["LIA"]

footer :: Doc
footer = parens $ text "check-synth"

declareGoal :: SygusGoal -> Doc
declareGoal (SygusGoal f _ outSort args) = sexp (text "synth-fun") [text f, prettyArgs, prettyMono outSort]
  where
    prettyArgs = parens $ hsep $ map (\(x, s) -> parens (text x <+> prettyMono s)) args

declareUniversal :: (Id, Sort) -> Doc
declareUniversal (x, s) = sexp (text "declare-var") [text x, prettyMono s]

declareConstraint :: Formula -> Doc
declareConstraint f = sexp (text "constraint") [asSexp f]

-- Unused for now -- just ignore datatypes
-- declareData :: Id -> DatatypeDef -> Doc
-- declareData dt (DatatypeDef tps pps pvs cs _ _) = sexp (text "declare-datatype") [dt]

-- Print formula to sygus language
asSexp :: Formula -> Doc
asSexp = plain . asSexp'

asSexp' f =  
 case f of
  (BoolLit True)  -> text "true"  -- need lowercase booleans
  (BoolLit False) -> text "false"
  (IntLit x)      -> pretty x
  (Var s x)       -> pretty x
  (Unary op f)    -> sexp (prettyUOp op) [asSexp f]
  (Binary op f g) -> sexp (prettyBOp op) [asSexp f, asSexp g]
  (Ite g t f)     -> sexp (text "ite") [asSexp g, asSexp t, asSexp f]
  (Pred s f xs)   -> sexp (text f) (map asSexp xs)
  _ -> error $ "unexpected formula sent to Sygus solver: " ++ show (pretty f)

-- Need to handle cases where sygus syntax differs from synquid language
prettyBOp :: BinOp -> Doc
prettyBOp Implies = text "=>"
prettyBOp Eq = text "="
prettyBOp And = text "and"
prettyBOp Or = text "or"
prettyBOp op = pretty op

-- Need to handle cases where sygus syntax differs from synquid language
prettyUOp :: UnOp -> Doc
prettyUOp Neg = pretty Neg
prettyUOp Not = text "not"


sexp :: Pretty a => Doc -> [a] -> Doc
sexp f args = parens $ f <+> hsep (map pretty args)

cvc4 :: [String]
cvc4 = ["cvc4"]

flags :: [String]
flags = ["--lang=sygus2", "--sygus-si=all", "--cegqi", "--cegqi-prereg-inst"]
