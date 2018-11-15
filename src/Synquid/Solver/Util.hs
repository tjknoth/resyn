{-# LANGUAGE FlexibleContexts #-}

-- Solver utilities
module Synquid.Solver.Util (
    embedEnv,
    embedSynthesisEnv,
    instantiateConsAxioms,
    potentialVars,
    freshId,
    freshVar,
    freshValueVars,
    throwError,
    allMeasureApps,
    nonGhostScalars,
    safeAddGhostVar,
    isResourceVariable,
    writeLog
) where

import Synquid.Logic
import Synquid.Type 
import Synquid.Program
import Synquid.Util
import Synquid.Pretty
import Synquid.Error
import Synquid.Solver.Monad

import Data.List 
import Data.Maybe 
import qualified Data.Set as Set 
import Data.Set (Set)
import qualified Data.Map as Map
import Control.Monad.State (get)
import Control.Monad (when)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (throwE)
import Control.Monad.Reader (asks)
import Control.Monad.Logic (msum)
import Control.Lens hiding (both)
import Debug.Trace

-- | Assumptions encoded in an environment
embedding :: Monad s => Environment -> Set Id -> Bool -> Bool -> TCSolver s (Set Formula)
embedding env vars includeQuantified substituteValueVars = do
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
                    let fml' = if substituteValueVars then substitute (Map.singleton valueVarName (Var IntS x)) fml else fml
                        fmls' = Set.fromList $ map (substitute (Map.singleton valueVarName (Var (toSort baseT) x)) . substitutePredicate pass)
                                          (fml' : allMeasurePostconditions includeQuantified baseT env) 
                        newVars = Set.delete x $ setConcatMap (potentialVars qmap) fmls' in 
                    addBindings env tass pass qmap (fmls `Set.union` fmls') (rest `Set.union` newVars)
                  LetT y tDef tBody -> addBindings (addGhostVariable x tBody . addGhostVariable y tDef . removeVariable x $ env) tass pass qmap fmls vars
                  AnyT -> Set.singleton ffalse
                  _ -> error $ unwords ["embedding: encountered non-scalar variable", x, "in 0-arity bucket"]
                Just sch -> addBindings env tass pass qmap fmls rest -- TODO: why did this work before?
    allSymbols = symbolsOfArity 0 

embedEnv :: Monad s => Environment -> Formula -> Bool -> Bool -> TCSolver s (Set Formula)
embedEnv env fml consistency subst = do 
  qmap <- use qualifierMap
  let relevantVars = potentialVars qmap fml
  embedding env relevantVars consistency subst

embedSynthesisEnv :: MonadHorn s 
                  => Environment 
                  -> Formula 
                  -> Bool 
                  -> Bool
                  -> TCSolver s (Set Formula)
embedSynthesisEnv env fml consistency useMeasures = do 
  let env' = if useMeasures 
      then env
      else env { _measureDefs = Map.empty } -- don't instantiate measures in certain cases
  embedEnv env' fml consistency True


-- | 'instantiateConsAxioms' @env fml@ : If @fml@ contains constructor applications, return the set of instantiations of constructor axioms for those applications in the environment @env@
instantiateConsAxioms :: Environment -> Bool -> Maybe Formula -> Formula -> Set Formula
instantiateConsAxioms env numeric mVal fml = 
  let inst = instantiateConsAxioms env numeric mVal 
      allMeasures dt e = Map.assocs $
        if numeric
          then allIntMeasuresOf dt e
          else allMeasuresOf dt e
  in case fml of
    Cons resS@(DataS dtName _) ctor args -> Set.unions $ Set.unions (map (measureAxiom resS ctor args) (allMeasures dtName env)) :
                                                          map (instantiateConsAxioms env numeric Nothing) args
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
          constArgList = Map.lookup mname (_measureConstArgs env)
        in Set.fromList $ allMeasureApps constArgList constantArgs vSubstBody 

allMeasureApps :: Maybe [Set Formula] -> [(Id, Sort)] -> Formula -> [Formula]
allMeasureApps Nothing _ _ = []
allMeasureApps (Just pArgs) constantArgs body = 
  let possibleArgs = map Set.toList pArgs
      possibleSubsts = zipWith (\(x, _) vars -> zip (repeat x) vars) constantArgs possibleArgs
      allArgLists = sequence possibleSubsts
  in  map ((`substitute` body) . Map.fromList) allArgLists

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
freshValueVars :: Monad s => Formula -> Sort -> TCSolver s (Formula, String)
freshValueVars fml sort = do 
  vnew <- freshValueVarId
  let newVar = Var sort vnew
  return (substitute (Map.singleton valueVarName newVar) fml, vnew)

nonGhostScalars env = Map.filterWithKey (nonGhost env) $ symbolsOfArity 0 env

nonGhost env x _ = Set.notMember x (env^.ghostSymbols)

safeAddGhostVar :: Monad s => String -> RType -> Environment -> TCSolver s Environment
safeAddGhostVar name t@FunctionT{} env = return $ addGhostVariable name t env
safeAddGhostVar name t@AnyT{} env = return $ addGhostVariable name t env
safeAddGhostVar name t env = do 
  tstate <- get 
  adomain <- asks _cegisDomain 
  if isResourceVariable env tstate adomain name t
    then do 
      universalFmls %= Set.insert (Var IntS name)
      return $ addGhostVariable name t env
    else return $ addGhostVariable name t env

isResourceVariable :: Environment 
                   -> TypingState 
                   -> Maybe AnnotationDomain
                   -> String
                   -> RType 
                   -> Bool 
isResourceVariable _ _ Nothing _ _ = False
isResourceVariable env tstate (Just adomain) x t = 
  let varName (Var _ n) = n
      cargs = env ^. measureConstArgs
      rmeasures = tstate ^. resourceMeasures 
      rsorts = map _inSort $ Map.elems rmeasures
      allCArgs = concat $ mapMaybe (`Map.lookup` cargs) (Map.keys rmeasures)  
      resourceCArgs = Set.map varName $ Set.unions allCArgs
      isUnresolved = Map.member x (_unresolvedConstants env)
      isInt t = 
        case baseTypeOf t of 
          IntT -> True 
          _    -> False
  in 
    not isUnresolved && case adomain of 
      Variable -> isInt t
      Measure  -> error "Measures not supported" -- Set.member x resourceCArgs 
      Both     -> error "Measures not supported" -- isInt t || Set.member x resourceCArgs


-- | Signal type error
throwError :: MonadHorn s => Doc -> TCSolver s ()
throwError msg = do
  (pos, ec) <- use errorContext
  lift $ lift $ throwE $ ErrorMessage TypeError pos (msg $+$ ec)

writeLog level msg = do
  maxLevel <- asks _tcSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return () 