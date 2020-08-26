{-# LANGUAGE FlexibleContexts #-}

-- | Resource analysis
module Synquid.Solver.Resource (
  -- checkResources,
  solveResourceConstraints,
  isResourceConstraint,
  processRCs,
  allRMeasures,
  partitionType,
  getAnnotationStyle,
  getPolynomialDomain,
  replaceCons
) where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Solver.Monad
import Synquid.Pretty
import Synquid.Solver.CEGIS
import Synquid.Solver.Types
import Synquid.Synthesis.Util hiding (writeLog)
import Synquid.Solver.Sygus

import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import           Control.Monad.Logic
import           Control.Monad.Reader
import           Control.Lens
import           Debug.Trace
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Semigroup (sconcat)
import           Data.Maybe

import Debug.Pretty.Simple

-- | Process, but do not solve, a set of resource constraints
processRCs :: (MonadHorn s, MonadSMT s, RMonad s)
           => [Constraint]
           -> TCSolver s ()
processRCs [] = return ()
processRCs constraints = do
  rcs <- mapM generateFormula (filter isResourceConstraint constraints)
  persistentState . resourceConstraints %= (++ rcs)

-- | 'solveResourceConstraints' @accConstraints constraints@ : Transform @constraints@ into logical constraints and attempt to solve the complete system by conjoining with @accConstraints@
solveResourceConstraints :: (MonadHorn s, RMonad s)
                         => [ProcessedRFormula]
                         -> [Constraint]
                         -> TCSolver s (Maybe [ProcessedRFormula])
solveResourceConstraints _ [] = return $ Just []
solveResourceConstraints oldConstraints constraints = do
    writeLog 3 $ linebreak <> text "Generating resource constraints:"
    -- Check satisfiability
    constraintList <- mapM generateFormula constraints
    b <- satisfyResources oldConstraints constraintList
    let result = if b then "SAT" else "UNSAT"
    writeLog 7 $ nest 4 $ text "Accumulated resource constraints:"
      $+$ pretty (map bodyFml oldConstraints)
    writeLog 8 $ nest 4 $ text "Solved resource constraint after conjoining formulas:"
      <+> text result $+$ prettyConjuncts (map bodyFml constraintList)
    return $ if b
      then Just constraintList -- $ Just $ if hasUniversals
      else Nothing


-- | 'generateFormula' @c@: convert constraint @c@ into a logical formula
--    If there are no universal quantifiers, we can cache the generated formulas
--    Otherwise, we must re-generate every time
generateFormula :: (MonadHorn s, RMonad s)
                => Constraint
                -> TCSolver s ProcessedRFormula
generateFormula c = do
  checkMults <- view (resourceArgs . checkMultiplicities) 
  generateFormula' checkMults c

generateFormula' :: (MonadHorn s, RMonad s)
                 => Bool
                 -> Constraint
                 -> TCSolver s ProcessedRFormula
generateFormula' checkMults c = do
  writeLog 4 $ indent 2 $ simplePrettyConstraint c <+> operator "~>"
  let mkRForm = RFormula Set.empty Set.empty Set.empty
  let freeParams = take 3 deBrujns  -- TODO: better solution. 3 is arbitrary.
  case c of
    Subtype{} -> error $ show $ text "generateFormula: subtype constraint present:" <+> pretty c
    WellFormed{} -> error $ show $ text "generateFormula: well-formedness constraint present:" <+> pretty c
    WellFormedPotential env p -> do
      let vs = getValueVar env
      let fml = mkRForm vs (p |>=| fzero)
      embedAndProcessConstraint env fml
    RSubtype env pl pr -> do
      op <- subtypeOp 
      vs1 <- getLocals env freeParams pl
      vs2 <- getLocals env freeParams pr
      let vs = Set.union vs1 vs2
      let fml = mkRForm vs $ pl `op` pr
      embedAndProcessConstraint env fml 
    SharedForm env f fl fr -> do
      let sharingFml = f |=| (fl |+| fr)
      let wf = conjunction [f |>=| fzero, fl |>=| fzero, fr |>=| fzero]
      let vs = getValueVar env
      let fml = mkRForm vs (wf |&| sharingFml)
      embedAndProcessConstraint env fml
    ConstantRes env -> do
      f <- assertZeroPotential env 
      let fml = mkRForm Set.empty f
      embedAndProcessConstraint env fml
    Transfer env env' -> do
      f <- redistribute env env' 
      let fml = mkRForm Set.empty f
      embedAndProcessConstraint env fml
    _ -> error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c


-- Constraint pre-processing pipeline
embedAndProcessConstraint :: (MonadHorn s, RMonad s)
                          => Environment
                          -> RawRFormula
                          -> TCSolver s ProcessedRFormula
embedAndProcessConstraint env rfml = do
  domain <- view (resourceArgs . rSolverDomain) 
  let go = embedConstraint env
       >=> replaceAbstractPotentials
       >=> instantiateUnknowns
       >=> filterAssumptions
       >=> getConstructors 
       >=> formatConstructors
       >=> joinAssumptions
  case domain of
    Dependent -> go rfml
    Constant  -> translateAndFinalize rfml

translateAndFinalize :: (MonadHorn s, RMonad s) => RawRFormula -> TCSolver s ProcessedRFormula 
translateAndFinalize rfml = do 
  writeLog 3 $ indent 4 $ pretty (bodyFml rfml)
  -- z3lit <- lift . lift . lift $ translate $ bodyFml rfml
  return $ rfml {
    _knownAssumptions = ftrue,
    _unknownAssumptions = ()
    -- _rconstraints = z3lit
  }


-- Embed context and generate constructor axioms
embedConstraint :: (MonadHorn s, RMonad s)
                => Environment
                -> RawRFormula
                -> TCSolver s RawRFormula
embedConstraint env rfml = do 
  -- Get assumptions related to all non-ghost scalar variables in context
  vars <- use (persistentState . universalVars)
  -- Small hack -- need to ensure we grab the assumptions related to _v
  -- Note that sorts DO NOT matter here -- the embedder will ignore them.
  let vars' = Set.insert (Var AnyS valueVarName) $ Set.map (Var AnyS) vars
  ass <- embedSynthesisEnv env (conjunction vars') True 
  -- Split embedding into known/unknown parts
  let emb = Set.filter (not . isUnknownForm) ass
  let unk = Set.filter isUnknownForm ass
  return $ over knownAssumptions (Set.union emb) 
         $ over unknownAssumptions (Set.union unk) rfml

-- Replace predicate applications with variables
replaceAbstractPotentials :: MonadHorn s => RawRFormula -> TCSolver s RawRFormula
replaceAbstractPotentials rfml = do
  rvs <- use $ persistentState . resourceVars 
  let fml' = replaceAbsPreds rvs $ _rconstraints rfml
  return $ set rconstraints fml' rfml

replaceAbsPreds :: Map String [Formula] -> Formula -> Formula
replaceAbsPreds rvs p@(Pred s x fs) =
  case Map.lookup x rvs of
    Nothing -> p
    Just _  -> Var s x
replaceAbsPreds rvs (WithSubst s e) = WithSubst s $ replaceAbsPreds rvs e
replaceAbsPreds rvs (Unary op f) = Unary op $ replaceAbsPreds rvs f
replaceAbsPreds rvs (Binary op f g) = Binary op (replaceAbsPreds rvs f) (replaceAbsPreds rvs g)
replaceAbsPreds rvs (Ite g t f) = Ite (replaceAbsPreds rvs g) (replaceAbsPreds rvs t) (replaceAbsPreds rvs f)
replaceAbsPreds rvs (All _ _) = error "replaceAbsPreds: found forall you should handle that"
replaceAbsPreds _ f = f

-- Use strongest possible assignment to unknown assumptions
instantiateUnknowns :: MonadHorn s => RawRFormula -> TCSolver s KnownRFormula
instantiateUnknowns rfml = do 
  unknown' <- assignUnknowns (_unknownAssumptions rfml)
  fml' <- assignUnknownsInFml (_rconstraints rfml)
  return $ set unknownAssumptions ()
         $ set rconstraints fml'
         $ over knownAssumptions (Set.union unknown') rfml


replaceCons f@Cons{} = mkFuncVar f
replaceCons f = f

filterAssumptions :: MonadHorn s => KnownRFormula -> TCSolver s KnownRFormula
filterAssumptions rfml = -- do
  return $ over knownAssumptions (Set.filter (not . hasCtor)) rfml
  {-
  shouldFilter <- usesSygus
  let rfml' = 
        if shouldFilter
          then over knownAssumptions (Set.filter (not . hasCtor)) rfml
          else rfml
  return rfml'
  -}

-- apply variable substitutions
getConstructors :: MonadHorn s => KnownRFormula -> TCSolver s KnownRFormula
getConstructors rfml  = do
  cons <- use matchCases
  let format = Set.map (transformFml mkFuncVar)
  return $ set ctors (format cons) rfml

-- Turn predicate / constructor applications into variables 
formatConstructors :: MonadHorn s => KnownRFormula -> TCSolver s KnownRFormula
formatConstructors rfml = do 
  let update = Set.map (transformFml mkFuncVar)
  return $ over knownAssumptions update 
         $ over rconstraints (transformFml mkFuncVar) rfml

-- Produce final formula
joinAssumptions :: MonadHorn s
                 => KnownRFormula
                 -> TCSolver s ProcessedRFormula
joinAssumptions (RFormula known _ preds substs fml) = do
  let ass = conjunction known
  writeLog 3 $ indent 4 $ pretty (ass |=>| fml) -- conjunction (map lcToFml lcs))
  return $ RFormula ass () preds substs fml 


-- | Check the satisfiability of the generated resource constraints, instantiating universally
--     quantified expressions as necessary.
satisfyResources :: RMonad s
                 => [ProcessedRFormula]
                 -> [ProcessedRFormula]
                 -> TCSolver s Bool
satisfyResources oldfmls newfmls = do
  let rfmls = oldfmls ++ newfmls
  let runInSolver = lift . lift . lift
  domain <- view (resourceArgs . rSolverDomain)
  infdRVars <- use $ persistentState . inferredRVars
  let tryInfer = not $ OMap.null infdRVars
  case domain of
    Constant -> do
      if tryInfer
        then do
          let fml = conjunction $ map bodyFml rfmls
          let rvl = OMap.assocs infdRVars
          model <- runInSolver $ optimizeAndGetModel fml rvl
          case model of
            Nothing -> return False
            Just m' -> do
              writeLog 6 $ nest 2 (text "Solved + inferred with model") </> nest 6 (text (modelStr m'))
              vs' <- runInSolver $ modelGetAssignment (fmap fst rvl) m'
              persistentState . inferredRVars %= OMap.unionWithR (\_ l _ -> l) (OMap.fromList . Map.toList . fmap Just . unRSolution $ vs')
              return True
        else do
          let fml = conjunction $ map bodyFml rfmls
          model <- runInSolver $ solveAndGetModel fml
          case model of
            Nothing -> return False
            Just m' -> do
              writeLog 6 $ nest 2 (text "Solved with model") </> nest 6 (text (modelStr m'))
              return True
    Dependent -> do
      if tryInfer
        -- TODO: infer dependent resources
        then error "Can't infer dependent resources"
        else do
          solver <- view (resourceArgs . rsolver)
          deployHigherOrderSolver solver oldfmls newfmls 

deployHigherOrderSolver :: RMonad s
                        => ResourceSolver
                        -> [ProcessedRFormula] 
                        -> [ProcessedRFormula]
                        -> TCSolver s Bool
-- Solve with synthesizer
deployHigherOrderSolver SYGUS oldfmls newfmls = do
  let rfmls = oldfmls ++ newfmls
  let runInSolver = lift . lift . lift
  logfile <- view (resourceArgs . sygusLog)
  ufmls <- map (Var IntS) . Set.toList <$> use (persistentState . universalVars)
  universals <- collectUniversals rfmls ufmls
  rvars <- use $ persistentState . resourceVars
  env <- use initEnv 
  solverCmd <- view (resourceArgs . cvc4)
  runInSolver $ solveWithSygus logfile solverCmd env rvars universals oldfmls newfmls

-- Solve with CEGIS (incremental or not)
deployHigherOrderSolver _ oldfmls newfmls = do
  let rfmls = oldfmls ++ newfmls
  let runInSolver = lift . lift . lift
  ufmls <- map (Var IntS) . Set.toList <$> use (persistentState . universalVars)
  universals <- collectUniversals rfmls ufmls
  cMax <- view (resourceArgs . cegisBound) 
  cstate <- updateCEGISState

  writeLog 3 $ text "Solving resource constraint with CEGIS:"
  writeLog 5 $ pretty $ conjunction $ map completeFml rfmls
  logUniversals
  
  let go = solveWithCEGIS cMax universals rfmls
  (sat, cstate') <- runInSolver $ runCEGIS go cstate
  storeCEGISState cstate'
  return sat


storeCEGISState :: Monad s => CEGISState -> TCSolver s ()
storeCEGISState st = do 
  cegisState .= st
  let isIncremental s = 
        case s of
          Incremental -> True
          _           -> False
  incremental <- isIncremental <$> view (resourceArgs . rsolver) 
  -- For non-incremental solving, don't reset resourceVars
  when incremental $
    persistentState . resourceVars .= Map.empty

-- Given a list of resource constraints, assemble the relevant universally quantified 
--   expressions for the CEGIS solver: renamed variables and constructor apps
--   Allows a list of extra formulas.
collectUniversals :: Monad s => [ProcessedRFormula] -> [Formula] -> TCSolver s Universals
collectUniversals rfmls existing = do 
  -- Do not need to substitute in constructors; substitutions are only for nameless rep (_v, de bruijns)
  let formatCons = Set.map ((\(Var s x) -> UCons s x) . transformFml mkFuncVar)
  ufs <- formatCons <$> use matchCases 
  let newvars = Set.toList $ Set.unions $ map _localUniversals rfmls -- concatMap (Map.elems . _varSubsts) rfmls
  return $ Universals (formatUniversals (existing ++ newvars)) (Set.toList ufs)


-- Nondeterministically redistribute top-level potentials between variables in context
redistribute :: Monad s
             => Environment
             -> Environment
             -> TCSolver s Formula
redistribute envIn envOut =
  let fpIn  = envIn ^. freePotential
      fpOut = envOut ^. freePotential
      cfpIn  = totalConditionalFP envIn
      cfpOut = totalConditionalFP envOut
      -- Sum of top-level potential annotations
      envSum = sumFormulas . allPotentials
      -- Assert that top-level potentials are re-partitioned
      transferAssertions = (envSum envIn |+| fpIn |+| cfpIn) |=| (envSum envOut |+| fpOut |+| cfpOut)
   in return transferAssertions

-- Assert that a context contains zero "free" potential
assertZeroPotential :: Monad s
                    => Environment
                    -- -> TCSolver s (PendingRSubst, Formula)
                    -> TCSolver s Formula
assertZeroPotential env = do
  let envSum = sumFormulas . allPotentials 
  let fml = ((env ^. freePotential) |+| envSum env) |=| fzero
  return fml

-- collect all top level potentials in context, wrapping them in an appropriate pending substitution
allPotentials :: Environment -> Map String Formula 
allPotentials env = Map.mapMaybeWithKey substTopPotential $ toMonotype <$> nonGhostScalars env
  where 
    substTopPotential x t = 
      let sub = Map.singleton valueVarName (Var (toSort (baseTypeOf t)) x) 
       in WithSubst sub . substitute sub <$> topPotentialOf t

-- Generate fresh version of _v
getValueVar :: Environment -> Set Formula
getValueVar env = 
  let sortFrom = toSort . baseTypeOf . toMonotype in
  case Map.lookup valueVarName (symbolsOfArity 0 env) of
    Nothing -> Set.empty
    Just sch -> Set.singleton $ Var (sortFrom sch) valueVarName

-- generate fresh value var if it's present
-- then traverse formula, generating de bruijns as needed (and passing upwards)
getLocals :: Monad s => Environment -> [String] -> Formula -> TCSolver s (Set Formula)
getLocals env fList f = do
  -- subst <- renameValueVar env
  let vs = getValueVar env
  getLocals' fList vs f

getLocals' :: Monad s => [String] -> Set Formula -> Formula -> TCSolver s (Set Formula) -- APs
getLocals' fList subst (Var sort id) 
  | id `elem` fList = -- do
      return $ Set.insert (Var sort id) subst
      -- let var' = Var sort id -- <$> freshVersion id
      -- return $ Map.insertWith (\_ x -> x) id var' subst
  | otherwise = return subst
getLocals' fList subst (Unary _ fml) =
  getLocals' fList subst fml
getLocals' fList subst (Binary _ fml1 fml2) =
  Set.union <$> getLocals' fList subst fml1 <*> getLocals' fList subst fml2
getLocals' fList subst (Ite i t e) =
  Set.union <$> (Set.union <$> getLocals' fList subst i <*> 
    getLocals' fList subst t) <*> getLocals' fList subst e
getLocals' fList subst (Pred _ _ fmls) = 
  Set.unions <$> mapM (getLocals' fList subst) fmls
getLocals' fList subst (Cons _ _ fmls) = 
  Set.unions <$> mapM (getLocals' fList subst) fmls
getLocals' _ subst x = return subst


-- Generate sharing constraints, given a type and the two types
--   into which it is shared
partitionType :: Bool
              -> Environment
              -> (Maybe String, RType)
              -> RType
              -> RType
              -> [Constraint]
partitionType cm env (x, t@(ScalarT b _ f)) (ScalarT bl _ _) (ScalarT br _ _) 
  | f == fzero = partitionBase cm env (x, b) bl br
partitionType cm env (x, t@(ScalarT b _ f)) (ScalarT bl _ fl) (ScalarT br _ fr)
  = let env' = 
          case x of 
            Nothing -> addVariable valueVarName t env  
            Just n  -> addVariable valueVarName (addRefinement t (varRefinement n (toSort b))) env
    in SharedForm env' f fl fr : partitionBase cm env (x, b) bl br

partitionBase cm env (x, DatatypeT _ ts ps) (DatatypeT _ tsl psl) (DatatypeT _ tsr psr)
  = let split p1 p2 p3 = if sortOf p1 == IntS then Just (SharedForm env p1 p2 p3) else Nothing
        bases = concat $ zipWith3 (partitionType cm env) (zip (repeat Nothing) ts) tsl tsr
        aps = catMaybes $ zipWith3 split ps psl psr
     in bases ++ aps
partitionBase cm env (x, b@(TypeVarT _ a m)) (TypeVarT _ _ ml) (TypeVarT _ _ mr)
  = [SharedForm env m ml mr | cm]
partitionBase _ _ _ _ _ = []


-- Is given constraint relevant for resource analysis
isResourceConstraint :: Constraint -> Bool
isResourceConstraint (Subtype _ ScalarT{} ScalarT{} _) = False
isResourceConstraint RSubtype{}    = True
isResourceConstraint WellFormed{}  = False
isResourceConstraint WellFormedPotential{} = True
isResourceConstraint SharedEnv{}   = False -- should never be present by now
isResourceConstraint SharedForm{}  = True
isResourceConstraint ConstantRes{} = True
isResourceConstraint Transfer{}    = True
isResourceConstraint _             = False

getAnnotationStyle :: Map String [Bool] -> [RSchema] -> RDomain
getAnnotationStyle flagMap schemas =
  let get sch = getAnnotationStyle' flagMap (getPredParamsSch sch) (toMonotype sch)
   in case map get schemas of
        [] -> error "getAnnotationSyle: empty list of goal schema"
        (a:as) -> sconcat (a :| as) -- can probably skip the catmaybes? and combine semigroups?

getAnnotationStyle' :: Map String [Bool] -> Set String -> RType -> RDomain 
getAnnotationStyle' flagMap predParams t =
  let rforms = conjunction $ allRFormulas flagMap t
      allVars = getVarNames t
  in case (hasVar allVars rforms, hasMeasure predParams rforms) of
      (_, True)     -> error "Measures in resource annotations not supported"
      (True, _)     -> Dependent
      _             -> Constant 

getPolynomialDomain :: Map String [Bool] -> RSchema -> RDomain
getPolynomialDomain flagMap sch = getPolynomialDomain' flagMap (getPredParamsSch sch) (toMonotype sch)

getPolynomialDomain' :: Map String [Bool] -> Set String -> RType -> RDomain
getPolynomialDomain' flagMap predParams t = 
  let rforms = conjunction $ allRFormulas flagMap t 
      allVars = getVarNames t
  in case (hasVarITE allVars rforms, hasMeasureITE predParams rforms) of 
      (_, True)     -> error "Measures in resource annotations not supported"
      (True, _)     -> Dependent
      _             -> Constant


getPredParamsSch :: RSchema -> Set String
getPredParamsSch (ForallP (PredSig x _ _) s) = Set.insert x (getPredParamsSch s)
getPredParamsSch (ForallT _ s) = getPredParamsSch s 
getPredParamsSch (Monotype _) = Set.empty 

getVarNames :: RType -> Set String
getVarNames (FunctionT x argT resT _) = 
  Set.insert x $ Set.union (getVarNames argT) (getVarNames resT)
getVarNames _ = Set.empty

subtypeOp :: Monad s => TCSolver s (Formula -> Formula -> Formula)
subtypeOp = do
  ct <- view (resourceArgs . constantTime)
  return $ if ct then (|=|) else (|>=|)

usesSygus :: Monad s => TCSolver s Bool
usesSygus = do
  solver <- view (resourceArgs . rsolver)
  return $ case solver of
    SYGUS -> True
    _     -> False

logUniversals :: Monad s => TCSolver s ()
logUniversals = do 
  uvars <- Set.toList <$> use (persistentState . universalVars)
  ufuns <- Set.toList <$> use (persistentState . universalMeasures)
  capps <- Set.toList <$> use matchCases
  writeLog 3 $ indent 2 $ text "Over universally quantified variables:"
    <+> hsep (map pretty uvars) <+> text "and functions:"
    <+> hsep (map pretty (ufuns ++ capps))

writeLog level msg = do
  maxLevel <- asks _tcSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return ()
