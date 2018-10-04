{-# LANGUAGE FlexibleContexts #-}

-- Solver utilities
module Synquid.Solver.Util (
    embedEnv,
    embedSynthesisEnv,
    instantiateConsAxioms,
    potentialVars,
    freshId,
    freshVar,
    somewhatFreshVar,
    freshValueVars,
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

import Data.Maybe (fromMaybe, mapMaybe, catMaybes)
import qualified Data.Set as Set 
import Data.Set (Set)
import qualified Data.Map as Map
import Control.Monad (when)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (throwE)
import Control.Monad.Trans.Maybe (MaybeT(..), runMaybeT)
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
                    let fmls' = Set.fromList $ map (substitute (Map.singleton valueVarName (Var (toSort baseT) x)) . substitutePredicate pass)
                                          (fml : allMeasurePostconditions includeQuantified baseT env) 
                        newVars = Set.delete x $ setConcatMap (potentialVars qmap) fmls' in 
                    addBindings env tass pass qmap (fmls `Set.union` fmls') (rest `Set.union` newVars)
                  LetT y tDef tBody -> addBindings (addVariable x tBody . addVariable y tDef . removeVariable x $ env) tass pass qmap fmls vars
                  AnyT -> Set.singleton ffalse
                  _ -> error $ unwords ["embedding: encountered non-scalar variable", x, "in 0-arity bucket"]
                Just sch -> addBindings env tass pass qmap fmls rest -- TODO: why did this work before?
    allSymbols env = symbolsOfArity 0 env

embedEnv :: Monad s => Environment -> Formula -> Bool -> TCSolver s (Set Formula)
embedEnv env fml consistency = do 
  qmap <- use qualifierMap
  let relevantVars = potentialVars qmap fml
  embedding env relevantVars consistency

embedSynthesisEnv :: Monad s => Environment -> Formula -> Bool -> TCSolver s (Set Formula)
embedSynthesisEnv env fml consistency = do 
  emb <- embedEnv env fml consistency
  unknownEmb <- embedSingletonUnknowns env
  return $ emb `Set.union` unknownEmb

-- | When there is a single possible valuation for a condition unknown, assume it.
embedSingletonUnknowns :: Monad s => Environment -> TCSolver s (Set Formula)
embedSingletonUnknowns env = do
    pass <- use predAssignment
    qmap <- use qualifierMap
    -- Do I need to substitute predicates?
    let ass = Set.map (substitutePredicate pass) (env ^. assumptions)
    let maybeAss = map (assignUnknown qmap) (Set.toList ass)
    return $ Set.fromList $ catMaybes maybeAss
  where 
    assignUnknown qmap fml = do 
      fname <- maybeUnknownName fml
      qspace <- Map.lookup fname qmap
      case _qualifiers qspace of 
        [f] -> Just f
        _   -> Nothing


-- | 'instantiateConsAxioms' @env fml@ : If @fml@ contains constructor applications, return the set of instantiations of constructor axioms for those applications in the environment @env@
instantiateConsAxioms :: Environment -> Maybe Formula -> Formula -> Set Formula
instantiateConsAxioms env mVal fml = let inst = instantiateConsAxioms env mVal in  
  case fml of
    Cons resS@(DataS dtName _) ctor args -> Set.unions $ Set.unions (map (measureAxiom resS ctor args) (Map.assocs $ allMeasuresOf dtName env)) :
                                                          map (instantiateConsAxioms env Nothing) args
    Unary op e -> inst e
    Binary op e1 e2 -> inst e1 `Set.union` inst e2
    Ite e0 e1 e2 -> inst e0 `Set.union` inst e1 `Set.union` inst e2
    SetLit _ elems -> Set.unions (map inst elems)
    Pred _ p args -> Set.unions $ map inst args
    _ -> Set.empty
  where
    measureAxiom resS ctor args (mname, MeasureDef inSort _ defs constantArgs _) =
      let
        MeasureCase _ vars body = head $ filter (\(MeasureCase c _ _) -> c == ctor) defs
        sParams = map varSortName (sortArgsOf inSort) -- sort parameters in the datatype declaration
        sArgs = sortArgsOf resS -- actual sort argument in the constructor application
        body' = noncaptureSortSubstFml sParams sArgs body -- measure definition with actual sorts for all subexpressions
        newValue = fromMaybe (Cons resS ctor args) mVal
        subst = Map.fromList $ (valueVarName, newValue) : zip vars args 
        -- Body of measure with constructor application (newValue) substituted for _v:
        vSubstBody = substitute subst body'
      in if null constantArgs
        then Set.singleton vSubstBody
        else let
          -- For each constant argument in the measure definition,
          --   assemble a list of tuples mapping the formal name to all possible variables in scope of the relevant sort
          varsOfSort = Map.assocs $ symbolsOfArity 0 env -- map (\(_, s) -> {-Map.keys (allScalarsOfSort env s)-}) constantArgs
          constArgList = Map.lookup mname (_measureConstArgs env)
        in 
          case constArgList of 
            Nothing -> Set.empty
            Just constArgs -> 
              let 
                possibleArgs = map Set.toList constArgs
                possibleSubsts = zipWith (\(x, s) vars -> zip (repeat x) vars) constantArgs possibleArgs  
                -- Nondeterministically choose one concrete argument from all lists of possible arguments
                allArgLists = sequence possibleSubsts
              in Set.fromList $ map ((`substitute` vSubstBody) . Map.fromList) allArgLists

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

freshValueVarId :: Monad s => TCSolver s String
freshValueVarId = freshId valueVarName

-- | Replace occurrences of _v with a fresh variable in a given formula 
freshValueVars :: Monad s => Formula -> Sort -> TCSolver s Formula 
freshValueVars fml sort = do 
  newVar <- Var sort <$> freshValueVarId
  return $ substitute (Map.singleton valueVarName newVar) fml

-- | 'somewhatFreshVar' @env prefix sort@ : A variable of sort @sort@ not bound in @env@
-- Exists to generate fresh variables for multi-argument measures without making all of the constructor axiom instantiation code monadic
somewhatFreshVar :: Environment -> String -> Sort -> Formula
somewhatFreshVar env prefix s = Var s name 
  where 
    name = unbound 0 (prefix ++ show 0)
    unbound n v = if Set.member v (universalSyms env)
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