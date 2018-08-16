{-# LANGUAGE FlexibleContexts #-}

-- Solver utilities
module Synquid.Solver.Util (
    embedEnv,
    potentialVars,
    freshId,
    freshVar,
    somewhatFreshVar,
    isSatWithModel,
    throwError,
    writeLog
) where

import Synquid.Logic
import Synquid.Type 
import Synquid.Program
import Synquid.Util
import Synquid.Pretty
import Synquid.Error
import Synquid.Solver.Monad

import qualified Data.Set as Set 
import Data.Set (Set)
import qualified Data.Map as Map
import Control.Monad (when)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (throwE)
import Control.Monad.Reader (asks)
import Control.Lens hiding (both)
import Debug.Trace

-- | Assumptions encoded in an environment
embedding :: Monad s => Environment -> Set Id -> Bool -> TCSolver s (Set Formula)
embedding env vars includeQuantified = do
    tass <- use typeAssignment
    pass <- use predAssignment
    qmap <- use qualifierMap
    let ass = Set.map (substitutePredicate pass) (env ^. assumptions)
    let allVars = vars `Set.union` potentialVars qmap (conjunction ass)
    return $ addBindings env tass pass qmap ass allVars
  where
    addBindings env tass pass qmap fmls vars =
      if Set.null vars
        then fmls
        else let (x, rest) = Set.deleteFindMin vars in
              case Map.lookup x (allSymbols env) of
                Nothing -> addBindings env tass pass qmap fmls rest -- Variable not found (useful to ignore value variables)
                Just (Monotype t) -> case typeSubstitute tass t of
                  ScalarT baseT fml pot ->
                    let allPost = allMeasurePostconditions includeQuantified baseT env
                        fmls' = Set.fromList $ map (substitute (Map.singleton valueVarName (Var (toSort baseT) x)) . substitutePredicate pass)
                                          (fml : allPost) 
                        newVars = Set.delete x $ setConcatMap (potentialVars qmap) fmls' in 
                    addBindings env tass pass qmap (fmls `Set.union` fmls') (rest `Set.union` newVars)
                  LetT y tDef tBody -> addBindings (addVariable x tBody . addVariable y tDef . removeVariable x $ env) tass pass qmap fmls vars
                  AnyT -> Set.singleton ffalse
                  _ -> error $ unwords ["embedding: encountered non-scalar variable", x, "in 0-arity bucket"]
                Just sch -> addBindings env tass pass qmap fmls rest -- TODO: why did this work before?
    allSymbols = symbolsOfArity 0 

embedEnv :: (MonadHorn s, MonadSMT s) => Environment -> Formula -> Bool -> TCSolver s (Set Formula)
embedEnv env fml consistency = do 
  qmap <- use qualifierMap
  let relevantVars = potentialVars qmap fml
  embedding env relevantVars consistency

bottomValuation :: QMap -> Formula -> Formula
bottomValuation qmap fml = applySolution bottomSolution fml
  where
    unknowns = Set.toList $ unknownsOf fml
    bottomSolution = Map.fromList $ zip (map unknownName unknowns) (map (Set.fromList . lookupQualsSubst qmap) unknowns)

-- | 'potentialVars' @qmap fml@ : variables of @fml@ if all unknowns get strongest valuation according to @quals@
potentialVars :: QMap -> Formula -> Set Id
potentialVars qmap fml = Set.map varName $ varsOf $ bottomValuation qmap fml

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: Monad s => String -> TCSolver s String
freshId prefix = do
  i <- uses idCount (Map.findWithDefault 0 prefix)
  idCount %= Map.insert prefix (i + 1)
  return $ prefix ++ show i

freshVar :: Monad s => Environment -> String -> TCSolver s String
freshVar env prefix = do
  x <- freshId prefix
  if Map.member x (allSymbols env)
    then freshVar env prefix
    else return x

-- | 'somewhatFreshVar' @env prefix sort@ : A variable of sort @sort@ not bound in @env@
-- Exists to generate fresh variables for multi-argument measures without making all of the constructor axiom instantiation code monadic
somewhatFreshVar :: Environment -> String -> Sort -> Formula
somewhatFreshVar env prefix s = Var s name 
  where 
    name = unbound 0 (prefix ++ show 0)
    unbound n v = if Set.member v (allUniversals env)
                    then unbound (n + 1) (v ++ show n)
                    else v

-- | 'isSatWithModel' : check satisfiability and return the model accordingly
isSatWithModel :: MonadSMT s => Formula -> TCSolver s (Bool, String)
isSatWithModel = lift . lift . lift . solveWithModel


-- | Signal type error
throwError :: MonadHorn s => Doc -> TCSolver s ()
throwError msg = do
  (pos, ec) <- use errorContext
  lift $ lift $ throwE $ ErrorMessage TypeError pos (msg $+$ ec)

writeLog level msg = do
  maxLevel <- asks _tcSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return () 