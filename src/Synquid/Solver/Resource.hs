{-# LANGUAGE FlexibleContexts, TemplateHaskell #-}

-- | Resource analysis
module Synquid.Solver.Resource (
  checkResources,
  simplifyRCs,
  allRFormulas,
  allRMeasures,
  partitionType,
  getAnnotationStyle,
  replaceCons
) where

import Synquid.Logic 
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Solver.Monad
import Synquid.Pretty
import Synquid.Solver.Util hiding (writeLog)
import Synquid.Solver.CEGIS 

import Data.Maybe
import qualified Data.Set as Set 
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (tails, union)
import Data.Tuple.Extra (first)
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Monad.State
import Control.Lens
import Debug.Trace

-- | Check resource bounds: attempt to find satisfying expressions for multiplicity and potential annotations 
checkResources :: (MonadHorn s, MonadSMT s, RMonad s) 
               => [Constraint] 
               -> TCSolver s ()
checkResources [] = return () 
checkResources constraints = do 
  accConstraints <- use resourceConstraints 
  newC <- solveResourceConstraints accConstraints (filter isResourceConstraint constraints)
  case newC of 
    Nothing -> throwError $ text "Insufficient resources"
    Just f  -> resourceConstraints %= (++ f) 

-- | Process, but do not solve, a set of resource constraints
simplifyRCs :: (MonadHorn s, MonadSMT s, RMonad s)
            => [Constraint]
            -> TCSolver s ()
simplifyRCs [] = return ()
simplifyRCs constraints = do 
  rcs <- mapM generateFormula constraints 
  resourceConstraints %= (++ rcs)
  
-- | 'solveResourceConstraints' @accConstraints constraints@ : Transform @constraints@ into logical constraints and attempt to solve the complete system by conjoining with @accConstraints@
solveResourceConstraints :: (MonadHorn s, RMonad s) 
                         => [ProcessedRFormula] 
                         -> [Constraint] 
                         -> TCSolver s (Maybe [ProcessedRFormula]) 
solveResourceConstraints _ [] = return $ Just [] 
solveResourceConstraints accConstraints constraints = do
    writeLog 3 $ linebreak <> text "Generating resource constraints:"
    -- Check satisfiability
    constraintList <- mapM generateFormula constraints
    universals <- Set.toList <$> use universalFmls
    b <- satisfyResources universals (accConstraints ++ constraintList) 
    let result = if b then "SAT" else "UNSAT"
    writeLog 5 $ nest 4 $ text "Accumulated resource constraints:" 
      $+$ prettyConjuncts (map rformula accConstraints)
    writeLog 3 $ nest 4 $ text "Solved resource constraint after conjoining formulas:" 
      <+> text result $+$ prettyConjuncts (map rformula constraintList)
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
  checkMults <- asks _checkMultiplicities
  generateFormula' checkMults c

generateFormula' :: (MonadHorn s, RMonad s)
                 => Bool 
                 -> Constraint 
                 -> TCSolver s ProcessedRFormula
generateFormula' checkMults c = 
  let mkRForm = RFormula Set.empty Set.empty 
  in case c of 
    Subtype{} -> error $ show $ text "generateFormula: subtype constraint present:" <+> pretty c
    RSubtype env pl pr label -> do 
      op <- subtypeOp 
      let fml = mkRForm Map.empty $ pl `op` pr
      embedAndProcessConstraint env Nothing fml
    WellFormed env t label -> do
      let fml = mkRForm Map.empty $ conjunction $ map (|>=| fzero) $ allRFormulas checkMults t
      embedAndProcessConstraint env (Just (refinementOf t)) fml
    SharedForm env f fl fr label -> do 
      let sharingFml = f |=| (fl |+| fr)  
      let wf = conjunction [f |>=| fzero, fl |>=| fzero, fr |>=| fzero]
      let fml = mkRForm Map.empty (wf |&| sharingFml)
      embedAndProcessConstraint env Nothing fml
    ConstantRes env label -> do 
      (substs, f) <- assertZeroPotential env
      let fml = mkRForm substs f 
      embedAndProcessConstraint env Nothing fml
    Transfer env env' label -> do 
      (fmls, substs) <- redistribute env env' 
      let fml = mkRForm substs $ conjunction fmls
      embedAndProcessConstraint env Nothing fml
    _ -> error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c


-- Constraint pre-processing pipeline
embedAndProcessConstraint :: (MonadHorn s, RMonad s)
                          => Environment
                          -> Maybe Formula 
                          -> RawRFormula
                          -> TCSolver s ProcessedRFormula
embedAndProcessConstraint env extra rfml = do
  hasUnivs <- isJust <$> asks _cegisDomain
  let go = insertAssumption extra 
       >=> embedConstraint env 
       >=> updateVariables 
       >=> instantiateAssumptions
       >=> applyAssumptions
  if hasUnivs
    then go rfml 
    else return $ rfml { 
      knownAssumptions = (), 
      unknownAssumptions = ()
    }

-- Embed context and generate constructor axioms
embedConstraint :: (MonadHorn s, RMonad s)
                => Environment 
                -> RawRFormula 
                -> TCSolver s RawRFormula
embedConstraint env rfml = do 
  useMeasures <- maybe False shouldUseMeasures <$> asks _cegisDomain
  emb <- Set.filter (not . isUnknownForm) <$> embedSynthesisEnv env (conjunction (varsOf (rformula rfml))) True useMeasures
  let axioms = if useMeasures 
      then instantiateConsAxioms env True Nothing (conjunction emb)
      else Set.empty
  return $ rfml { knownAssumptions = Set.union emb axioms } 

-- Insert extra assumption, if necessary
insertAssumption :: Monad s => Maybe Formula -> RawRFormula -> TCSolver s RawRFormula
insertAssumption Nothing f = return f
insertAssumption (Just extra) (RFormula known unknown substs fml) = return $
  case extra of 
    u@Unknown{} -> RFormula known (Set.insert u unknown) substs fml 
    f           -> RFormula (Set.insert f known) unknown substs fml


replaceCons f@Cons{} = mkFuncVar f
replaceCons f = f

-- | 'updateVariables' : replace constructor applications with variables, 
--    generate fresh _v's
updateVariables :: MonadHorn s => RawRFormula -> TCSolver s RawRFormula 
updateVariables (RFormula known unknown substs body) = do 
  -- TODO: the original _v needs to get into the list of universals
  --   For some reason, the substitutions aren't really happening after the first round
  let adjust = transformFml replaceCons
  let body'  = adjust body
  let known' = Set.map adjust known
  return $ RFormula known' unknown substs body'

-- Instantiate universally quantified expressions
-- Generate congruence axioms
instantiateAssumptions :: MonadHorn s => RawRFormula -> TCSolver s RawRFormula
instantiateAssumptions (RFormula known unknown substs body) = do 
  -- Instantiate universals
  res <- mapM instantiateForall $ Set.toList known
  let instantiatedEmb = map fst res 
  -- Generate variables for predicate applications
  let (body', bodyPreds) = adjustAndGatherPreds body
  -- Generate congruence axioms
  let allPreds = Set.unions $ bodyPreds : map snd res
  let congruenceAxioms = generateCongAxioms allPreds
  let completeEmb = Set.fromList $ congruenceAxioms ++ concat instantiatedEmb
  -- Instantiate unknown assumptions
  -- TODO: maybe move this up so that we can replace function apps when 
  --   it's done for known/body?
  unknown' <- Set.map (transformFml mkFuncVar) <$> assignUnknowns unknown
  -- Update set of measure applications
  universalMeasures %= Set.union (Set.map mkFuncVar allPreds)
  return $ RFormula completeEmb unknown' substs body'

applyAssumptions :: MonadHorn s 
                 => RawRFormula 
                 -> TCSolver s ProcessedRFormula
applyAssumptions (RFormula known unknown substs fml) = do 
  aDomain <- asks _cegisDomain
  let ass = Set.union known unknown

  let finalFml = if isNothing aDomain 
      then fml
      else conjunction ass |=>| fml

  return $ RFormula () () substs finalFml 


-- | Check the satisfiability of the generated resource constraints, instantiating universally 
--     quantified expressions as necessary.
satisfyResources :: RMonad s 
                 => [Formula] 
                 -> [ProcessedRFormula]
                 -> TCSolver s Bool
satisfyResources universals rfmls = do 
  noUnivs <- isNothing <$> asks _cegisDomain
  if noUnivs 
    then do 
      let fml = conjunction $ map rformula rfmls
      model <- lift . lift . lift $ solveAndGetModel fml
      case model of
        Nothing -> return False
        Just m' -> do 
          writeLog 6 $ nest 2 (text "Solved with model") </> nest 6 (text (snd m'))
          return True 
    else do
      env <- use initEnv
      cMax <- asks _cegisMax
      aDomain <- fromJust <$> asks _cegisDomain
      rVars <- use resourceVars
      mApps <- Set.toList <$> use universalMeasures 
      cApps <- Set.toList <$> use matchCases

      -- Construct list of universally quantified expressions, storing the formula with a string representation
      let universalsWithVars = formatUniversals universals 
      let uMeasures = Map.assocs $ allRMeasures env
      let possiblePredArgs = filter (not . isValueVar) universals
      -- Initialize polynomials for each resource variable
      let init name info = initializePolynomial env aDomain uMeasures (name, possiblePredArgs) --(name, info) 
      let allPolynomials = Map.mapWithKey init rVars
      -- List of all coefficients in the list of all polynomials
      let allCoefficients = concat $ Map.elems $ fmap coefficientsOf allPolynomials
      -- Initialize all coefficient values -- the starting value should not matter
      let initialProgram = Map.fromList $ zip allCoefficients initialCoefficients 
      let formatPred (Var s x) = (x, Var s x)
      let formatCons c@Cons{}  = (mkFuncString c, mkFuncVar c)   
      let allUniversals = Universals universalsWithVars (map formatPred mApps ++ map formatCons cApps)

      writeLog 3 $ text "Solving resource constraint with CEGIS:" 
      writeLog 5 $ pretty $ conjunction $ map rformula rfmls
      writeLog 3 $ indent 2 $ text "Over universally quantified expressions:" <+> hsep (map (pretty . snd) universalsWithVars)

      solveWithCEGIS cMax rfmls allUniversals [] allPolynomials initialProgram 

shouldUseMeasures :: AnnotationDomain -> Bool
shouldUseMeasures ad = case ad of 
    Variable -> False 
    _ -> True 

-- Nondeterministically redistribute top-level potentials between variables in context
redistribute :: Monad s 
             => Environment 
             -> Environment 
             -> TCSolver s ([Formula], Map Formula Substitution)
redistribute envIn envOut = do
  let fpIn  = _freePotential envIn 
  let fpOut = _freePotential envOut 
  -- All (non-ghost) scalar types 
  let scalarsOf env = toMonotype <$> nonGhostScalars env
  -- All top-level potential annotations of a map of scalar types
  let topPotentials = Map.mapMaybe topPotentialOf
  -- Generate pending substitutions 
  -- TODO: generalize this to potentials that aren't just free variables!
  let substitutions e = Map.foldlWithKey generateSubst Map.empty (scalarsOf e)
  -- Sum of all top-level potentials of scalar types in context
  let envSum env = sumFormulas $ topPotentials $ Map.mapWithKey applySubst $ scalarsOf env
  -- Assert that all potentials are well-formed
  let wellFormed smap = map (|>=| fzero) ((Map.elems . topPotentials) smap) 
  -- Assert (fresh) potentials in output context are well-formed
  let wellFormedAssertions = (fpIn |>=| fzero) : (fpOut |>=| fzero) : wellFormed (scalarsOf envOut) 
  --Assert that top-level potentials are re-partitioned
  let transferAssertions = (envSum envIn |+| fpIn) |=| (envSum envOut |+| fpOut)
  return (transferAssertions : wellFormedAssertions, Map.union (substitutions envIn) (substitutions envOut))

-- Substitute for _v in potential annotation
generateSubst :: PendingRSubst -> String -> RType -> PendingRSubst
generateSubst subs x t = 
  case topPotentialOf t of 
    Nothing -> subs 
    Just (Ite g p q) -> 
      let value' = Var (toSort (baseTypeOf t)) x
          subs' = Map.insert p (Map.singleton valueVarName value') subs
      in Map.insert q (Map.singleton valueVarName value') subs
    Just p ->
      let value' = Var (toSort (baseTypeOf t)) x 
      in Map.insert p (Map.singleton valueVarName value') subs

applySubst :: String -> RType -> RType 
applySubst x (ScalarT b r p) = 
  let value' = Var (toSort b) x 
  in ScalarT b r $ substitute (Map.singleton valueVarName value') p

-- Generate sharing constraints, given a type and the two types 
--   into which it is shared 
partitionType :: Bool 
              -> String 
              -> Environment 
              -> (String, RType)
              -> RType
              -> RType
              -> [Constraint]
partitionType cm l env (x, t@(ScalarT b _ f)) (ScalarT bl _ fl) (ScalarT br _ fr)
  = let env'  = addAssumption (Var (toSort b) valueVarName |=| Var (toSort b) x) $ 
                  addVariable valueVarName t env
    in SharedForm env' f fl fr (x ++ " : " ++ l) : partitionBase cm l env (x, b) bl br

partitionBase cm l env (x, DatatypeT _ ts _) (DatatypeT _ tsl _) (DatatypeT _ tsr _)
  = concat $ zipWith3 (partitionType cm l env) (zip (repeat x) ts) tsl tsr
partitionBase cm l env (x, b@(TypeVarT _ _ m)) (TypeVarT _ _ ml) (TypeVarT _ _ mr) 
  = [SharedForm env m ml mr (x ++ " : " ++ l) | cm]
partitionBase _ _ _ _ _ _ = []


-- Assert that a context contains zero "free" potential
assertZeroPotential :: Monad s 
                    => Environment 
                    -> TCSolver s (PendingRSubst, Formula) 
assertZeroPotential env = do 
  let scalars = toMonotype <$> nonGhostScalars env 
  let topPotentials = Map.mapMaybe topPotentialOf
  let substitutions = Map.foldlWithKey generateSubst Map.empty scalars
  let fml = ((env ^. freePotential) |+| sumFormulas (topPotentials scalars)) |=| fzero
  return (substitutions, fml)

-- Is given constraint relevant for resource analysis
isResourceConstraint :: Constraint -> Bool
isResourceConstraint (Subtype _ ScalarT{} ScalarT{} _ _) = False-- True
isResourceConstraint RSubtype{}    = True
isResourceConstraint WellFormed{}  = True
isResourceConstraint SharedEnv{}   = False -- should never be present by now
isResourceConstraint SharedForm{}  = True
isResourceConstraint ConstantRes{} = True
isResourceConstraint Transfer{}    = True
isResourceConstraint _             = False

-- Return refinement of scalar type
refinementOf :: RType -> Formula 
refinementOf (ScalarT _ fml _) = fml
refinementOf _                 = error "error: Encountered non-scalar type when generating resource constraints"

-- Instantiate universally quantified expression with all possible arguments in the 
--   quantified position. Also generate congruence axioms.
-- POSSIBLE PROBLEM: this doesn't really recurse looking for arbitrary foralls
--   It will find them if top-level or nested below a single operation. This SHOULD
--   be ok for our current scenario...
-- The function returns a pair, the first element of which is a list of all formulas,
--   including new predicate applications, the second is a set of just the instantiated apps 
instantiateForall :: Monad s => Formula -> TCSolver s ([Formula], Set Formula)
instantiateForall f@All{} = instantiateForall' f
instantiateForall f       = return ([f], Set.empty)

instantiateForall' (All f g) = instantiateForall' g
instantiateForall' f         = instantiatePred f

instantiatePred :: Monad s => Formula -> TCSolver s ([Formula], Set Formula)
instantiatePred fml@(Binary op p@(Pred s x args) axiom) = do 
  env <- use initEnv
  case Map.lookup x (allRMeasures env) of 
    Nothing -> error $ show $ text "instantiatePred: measure definition not found" <+> pretty p
    Just mdef -> do
      let substs = allValidCArgs env mdef p
      let allPreds = map (`substitute` p) substs
      let allFmls = map (`substitute` fml) substs
      return (map (transformFml mkFuncVar) allFmls, Set.fromList allPreds)

-- Replace predicate applications in formula f with appropriate variables,
--   collecting all such predicate applications present in f
adjustAndGatherPreds :: Formula -> (Formula, Set Formula)
adjustAndGatherPreds (Unary op f) = 
  let (f', ps) = adjustAndGatherPreds f
  in (Unary op f', ps)
adjustAndGatherPreds (Binary op f g) = 
  let (f', fps) = adjustAndGatherPreds f
      (g', gps) = adjustAndGatherPreds g
  in (Binary op f' g', fps `Set.union` gps) 
adjustAndGatherPreds (Ite g t f) = 
  let (g', gps) = adjustAndGatherPreds g
      (t', tps) = adjustAndGatherPreds t
      (f', fps) = adjustAndGatherPreds f
  in (Ite g' t' f', gps `Set.union` tps `Set.union` fps)
adjustAndGatherPreds (All f g) = adjustAndGatherPreds g -- maybe should handle quantified fmls...
adjustAndGatherPreds (SetLit s fs) = 
  let (fs', fps) = unzip $ map adjustAndGatherPreds fs
  in (SetLit s fs', Set.unions fps)
adjustAndGatherPreds f@Pred{} = (mkFuncVar f, Set.singleton f)
adjustAndGatherPreds f = (f, Set.empty)

-- Generate all congruence axioms, given all instantiations of universally quantified
--   measure applications
generateCongAxioms :: Set Formula -> [Formula]
generateCongAxioms preds = concatMap assertCongruence $ Map.elems (groupPreds preds) 
  where 
    groupPreds = foldl (\pmap p@(Pred _ x _) -> Map.insertWith (++) x [p] pmap) Map.empty 

-- Generate all congruence relations given a list of possible applications of 
--   some measure
assertCongruence :: [Formula] -> [Formula]
assertCongruence allApps = map assertCongruence' (pairs allApps)
  where 
    -- All pairs from a list
    pairs xs = [(x, y) | (x:ys) <- tails xs, y <- ys]

assertCongruence' (pl@(Pred _ ml largs), pr@(Pred _ mr rargs)) =
  conjunction (zipWith (|=|) largs rargs) |=>| (mkFuncVar pl |=| mkFuncVar pr) 
assertCongruence' ms = error $ show $ text "assertCongruence: called with non-measure formulas:"
  <+> pretty ms 

isValueVar (Var _ ('_':'v':_)) = True
isValueVar _                   = False

getAnnotationStyle = getAnnotationStyle' . toMonotype 

getAnnotationStyle' t = 
  let rforms = conjunction $ allRFormulas True t
  in case (varsOnly rforms, predsOnly rforms) of 
      (True, True)  -> Just Both 
      (False, True) -> Just Measure
      (True, _)     -> Just Variable
      _             -> Nothing

subtypeOp :: Monad s => TCSolver s (Formula -> Formula -> Formula)
subtypeOp = do 
  ct <- asks _constantRes 
  return $ if ct then (|=|) else (|>=|)

writeLog level msg = do 
  maxLevel <- asks _tcSolverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) $ return ()