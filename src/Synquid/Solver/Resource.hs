{-# LANGUAGE FlexibleContexts #-}

-- | Resource analysis
module Synquid.Solver.Resource (
  checkResources,
  simplifyRCs,
  allUniversals,
  allRFormulas,
  allRMeasures,
  partitionType,
  getAnnotationStyle
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
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Lens
import Debug.Trace


{- Implementation -}

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

simplifyRCs :: (MonadHorn s, MonadSMT s, RMonad s)
                 => [Constraint]
                 -> TCSolver s ()
simplifyRCs [] = return ()
simplifyRCs constraints = do 
  rcs <- mapM process constraints 
  resourceConstraints %= (++ rcs)
  
-- | 'solveResourceConstraints' @accConstraints constraints@ : Transform @constraints@ into logical constraints and attempt to solve the complete system by conjoining with @accConstraints@
solveResourceConstraints :: (MonadHorn s, RMonad s) => [ProcessedRFormula] -> [Constraint] -> TCSolver s (Maybe [ProcessedRFormula]) 
solveResourceConstraints _ [] = return $ Just [] 
solveResourceConstraints accConstraints constraints = do
    writeLog 3 $ linebreak <> text "Generating resource constraints:"

    -- Need environment to determine which annotation formulas are universally quantified
    let tempEnv = envFrom $ head constraints
    constraintList <- mapM process constraints

    -- Check satisfiability
    universals <- Set.toList <$> use universalFmls
    b <- satisfyResources tempEnv universals (accConstraints ++ constraintList) 

    let result = if b then "SAT" else "UNSAT"
    writeLog 5 $ nest 4 $ text "Accumulated resource constraints:" 
      $+$ prettyConjuncts (map rformula accConstraints)
    writeLog 3 $ nest 4 $ text "Solved resource constraint after conjoining formulas:" 
      <+> text result $+$ prettyConjuncts (map rformula constraintList)
    return $ if b 
      then Just constraintList -- $ Just $ if hasUniversals
      else Nothing

process :: (MonadHorn s, RMonad s) => Constraint -> TCSolver s ProcessedRFormula 
process c = do 
  pf <- (generateFormula >=> applyAssumptions) c 
  writeLog 3 $ indent 2 $ nest 4 $ simplePrettyConstraint c <+> text "~>" $+$ pretty pf 
  return pf
  
applyAssumptions :: MonadHorn s 
                 => RawRFormula 
                 -> TCSolver s ProcessedRFormula
applyAssumptions (RFormula known unknown substs fml) = do 
  emb <- assignUnknowns unknown
  univs <- use universalFmls
  aDomain <- asks _cegisDomain
  rms <- Map.assocs <$> use resourceMeasures

  let useMeasures = maybe False shouldUseMeasures aDomain 

  let emb' = Set.filter (isRelevantAssumption useMeasures (map fst rms) univs) emb
  let known' = Set.filter (isRelevantAssumption useMeasures (map fst rms) univs) known

  -- Not sure why I once needed this?
  --env <- use initEnv
  --let wfMeasures = if useMeasures
  --    then conjunction $ map (|>=| fzero) (possibleMeasureApps env (Set.toList univs) rms)
  --    else ftrue

  let finalFml = if isNothing aDomain 
      then fml
      else (conjunction known' |&| conjunction emb' {-|&| wfMeasures-}) |=>| fml

  return $ RFormula () () substs finalFml 

-- | 'generateFormula' @c@: convert constraint @c@ into a logical formula
--    If there are no universal quantifiers, we can cache the generated formulas 
--    Otherwise, we must re-generate every time
generateFormula :: (MonadHorn s, RMonad s) => Constraint -> TCSolver s RawRFormula 
generateFormula c = do 
  checkMults <- asks _checkMultiplicities
  generateFormula' checkMults c

generateFormula' :: (MonadHorn s, RMonad s)
                 => Bool 
                 -> Constraint 
                 -> TCSolver s RawRFormula 
generateFormula' checkMults c = 
  let mkRForm = RFormula Set.empty Set.empty in
  case c of 
    Subtype{} -> error $ show $ text "generateFormula: subtype constraint present:" <+> pretty c
    RSubtype env pl pr label -> do 
      op <- subtypeOp 
      let fml = mkRForm Map.empty $ pl `op` pr
      embedAndProcessConstraint env c fml Nothing
    WellFormed env t label -> do
      let fmls = mkRForm Map.empty $ conjunction $ map (|>=| fzero) $ allRFormulas checkMults t
      embedAndProcessConstraint env c fmls (Just (refinementOf t))
    SharedForm env f fl fr label -> do 
      let sharingFml = f |=| (fl |+| fr)  
      let wf = conjunction [f |>=| fzero, fl |>=| fzero, fr |>=| fzero]
      let fmls = mkRForm Map.empty (wf |&| sharingFml)
      embedAndProcessConstraint env c fmls Nothing
    ConstantRes env label -> do 
      (substs, f) <- assertZeroPotential env
      let fmls = mkRForm substs f 
      embedAndProcessConstraint env c fmls Nothing
    Transfer env env' label -> do 
      (fmls, substs) <- redistribute env env' 
      let rfml = mkRForm substs $ conjunction fmls
      embedAndProcessConstraint env c rfml Nothing 
    _ -> error $ show $ text "Constraint not relevant for resource analysis:" <+> pretty c

-- | Embed the environment assumptions and preproess the constraint for solving 
embedAndProcessConstraint :: (MonadHorn s, RMonad s)
                          => Environment 
                          -> Constraint 
                          -> RawRFormula 
                          -> Maybe Formula
                          -> TCSolver s RawRFormula
embedAndProcessConstraint env c rfml extra = do 
  let fml = rformula rfml
  let substs = pendingSubsts rfml
  aDomain <- asks _cegisDomain
  -- If the top-level annotations do not contain measures,
  --   do not consider any assumptions over measures or any post conditions
  let useMeasures = maybe False shouldUseMeasures aDomain 
  univs <- use universalFmls
  let possibleVars = varsOf fml
  emb <- Set.filter (not . isUnknownForm) <$> embedSynthesisEnv env (conjunction possibleVars) True useMeasures
  let axioms = if useMeasures
      then instantiateConsAxioms env True Nothing (conjunction emb)
      else Set.empty
  noUnivs <- isNothing <$> asks _cegisDomain
  let (finalEmb, unknownEmb) = 
        if noUnivs 
          then (Set.empty, Set.empty)
          else (Set.union emb axioms, allUnknowns env)
  let (finalEmb', unknownEmb') = case extra of 
        Nothing -> (finalEmb, unknownEmb)
        Just u@Unknown{} -> (finalEmb, Set.insert u unknownEmb)
        Just f -> (Set.insert f finalEmb, unknownEmb)
  -- Next: instantiate universals
  --   How to instantiate: basically a 1-depth synthesis problem! just enumerate...

  -- todo: think of a nice way to encode the "pipline" of adjusting assumptions
  --       known:   union  -> 
  --       unknown: allUnk -> 
  return $ RFormula finalEmb' unknownEmb' substs fml

-- | Given a list of resource variables and a set of possible measures,
--     determine whether or not a given formula is relevant to the resource analysis
isRelevantAssumption :: Bool -> [String] -> Set Formula -> Formula -> Bool 
isRelevantAssumption _ _ rvs v@Var{} 
  = True --Set.member v rvs
isRelevantAssumption useM rms _ (Pred _ x _) 
  = useM && x `elem` rms
isRelevantAssumption _ _ _ Unknown{} 
  = False -- TODO: fix once i start assuming unknowns
isRelevantAssumption useM rms rvs (Unary _ f) 
  = isRelevantAssumption useM rms rvs f
isRelevantAssumption useM rms rvs (Binary _ f g) 
  = isRelevantAssumption useM rms rvs f && isRelevantAssumption useM rms rvs g
isRelevantAssumption useM rms rvs (Ite f g h) 
  = isRelevantAssumption useM rms rvs f && isRelevantAssumption useM rms rvs g && isRelevantAssumption useM rms rvs h
isRelevantAssumption useM _ _ Cons{} 
  = useM
isRelevantAssumption useM rms rvs (All f g) 
  = isRelevantAssumption useM rms rvs g -- trace "Warning: universally quantified assumption" True
isRelevantAssumption _ _ _ _ 
  = True

-- | Check the satisfiability of the generated resource constraints, instantiating universally 
--     quantified expressions as necessary.
satisfyResources :: RMonad s 
                 => Environment 
                 -> [Formula] 
                 -> [ProcessedRFormula]
                 -> TCSolver s Bool
satisfyResources env universals rfmls = do 
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
      cMax <- asks _cegisMax
      -- Unsafe, but should be OK since we already checked that universals are non-null
      aDomain <- fromJust <$> asks _cegisDomain
      rVars <- use resourceVars
      -- Construct list of universally quantified expressions, storing the formula with a string representation
      let universalsWithVars = formatUniversals universals 
      uMeasures <- Map.assocs <$> use resourceMeasures
      -- Initialize polynomials for each resource variable
      let init name info = initializePolynomial env aDomain uMeasures (name, info) 
      let allPolynomials = Map.mapWithKey init rVars
      -- List of all coefficients in the list of all polynomials
      let allCoefficients = concat $ Map.elems $ fmap coefficientsOf allPolynomials
      -- Initialize all coefficient values -- the starting value should not matter
      let initialProgram = Map.fromList $ zip allCoefficients initialCoefficients 

      let allUniversals = Universals universalsWithVars uMeasures 
      writeLog 3 $ text "Solving resource constraint with CEGIS:" 
      writeLog 5 $ pretty $ conjunction $ map rformula rfmls
      writeLog 3 $ indent 2 $ text "Over universally quantified expressions:" <+> hsep (map (pretty . snd) universalsWithVars)
      solveWithCEGIS cMax rfmls allUniversals [] allPolynomials initialProgram 

shouldUseMeasures  ad = case ad of 
    Variable -> False 
    _ -> True 

allRMeasures :: RSchema -> Map String MeasureDef -> Map String MeasureDef
allRMeasures sch = allRMeasures' (toMonotype sch) 

allRMeasures' typ measures = 
  let rforms = allRFormulas True typ
      allPreds = Set.unions $ map getAllPreds rforms
  in  Map.filterWithKey (\x _ -> x `Set.member` allPreds) measures

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

applySubst x (ScalarT b r p) = 
  let value' = Var (toSort b) x 
  in ScalarT b r $ substitute (Map.singleton valueVarName value') p

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


assertZeroPotential :: Monad s 
                    => Environment 
                    -> TCSolver s (PendingRSubst, Formula) 
assertZeroPotential env = do 
  let scalars = toMonotype <$> nonGhostScalars env 
  let topPotentials = Map.mapMaybe topPotentialOf
  let substitutions = Map.foldlWithKey generateSubst Map.empty scalars
  let fml = ((env ^. freePotential) |+| sumFormulas (topPotentials scalars)) |=| fzero
  return (substitutions, fml)

totalTopLevelPotential :: RType -> Formula
totalTopLevelPotential (ScalarT base _ p) = p 
totalTopLevelPotential _                  = fzero

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

-- | 'allUniversals' @env sch@ : set of all universally quantified resource formulas in the potential
--    annotations of the type @sch@
allUniversals :: Environment -> RSchema -> Set Formula
allUniversals env sch = getUniversals univSyms $ conjunction $ allRFormulas True $ toMonotype sch 
  where
    -- Include function argument variable names in set of possible universally quantified expressions
    univSyms = varsOfType (toMonotype sch) `Set.union` universalSyms env
    varsOfType ScalarT{}                 = Set.empty
    varsOfType (FunctionT x argT resT _) = Set.insert x (varsOfType argT `Set.union` varsOfType resT)

-- | 'getUniversals' @env f@ : return the set of universally quantified terms in formula @f@ given set of universally quantified symbols @syms@ 
getUniversals :: Set String -> Formula -> Set Formula
getUniversals syms (SetLit s fs)  = Set.unions $ map (getUniversals syms) fs
getUniversals syms v@(Var s x)    = Set.fromList [v | Set.member x syms || isValueVar x] 
  where 
    isValueVar ('_':'v':_) = True
    isValueVar _           = False
getUniversals syms (Unary _ f)    = getUniversals syms f
getUniversals syms (Binary _ f g) = getUniversals syms f `Set.union` getUniversals syms g
getUniversals syms (Ite f g h)    = getUniversals syms f `Set.union` getUniversals syms g `Set.union` getUniversals syms h
getUniversals syms (Pred _ _ fs)  = Set.unions $ map (getUniversals syms) fs 
getUniversals syms (Cons _ _ fs)  = Set.unions $ map (getUniversals syms) fs
getUniversals syms (All f g)      = getUniversals syms g
getUniversals _ _                 = Set.empty 

instantiateForall :: Environment -> [Formula] -> Formula -> [Formula]
instantiateForall env univs (All f g) = instantiateForall env univs g
instantiateForall env univs f = instantiatePred env univs f

instantiatePred env univs p@(Pred s x args) = 
  case Map.lookup x (env ^. measureDefs) of 
    Nothing -> [p]
    Just mdef -> possibleMeasureApps env univs (x, mdef) 
instantiatePred env univs (Unary op f) = Unary op <$> instantiateForall env univs f
instantiatePred env univs (Binary op f g) = [Binary op f' g' | f' <- instantiateForall env univs f, g' <- instantiateForall env univs g]
instantiatePred env _ f = [f]

-- TODO: will the below include _v if relevant? No... make sure it does (will it need to?)
{-
-- Given an environment, a predicate application, a list of arguments, and all 
--   formal arguments, determine all valid applications of said predicate -- 
--   ie all applilcations to variables in context that unify with the argument sort
allValidApplications :: Environment 
                     -> Formula 
                     -> [(String, Sort)] 
                     -> [(String, Sort)] 
                     -> Sort 
                     -> [Formula]
allValidApplications env (Pred s x _) args constArgs targetSort = 
  let sortAssignment = foldl assignSorts (Just Map.empty) (zip (map snd args) (map snd constArgs))
      makePred (_, Nothing)      = Nothing 
      makePred (arg, Just subst) = Just $ Pred s x (map (uncurry (flip Var)) constArgs ++ [sortSubstituteFml subst (mkVar arg)])
      possibleVars = fmap (toSort . baseTypeOf . toMonotype) (symbolsOfArity 0 env) 
      mkVar x = Var (possibleVars Map.! x) x
      attemptToAssign ass s = assignSorts ass (s, targetSort)
  in mapMaybe makePred $ Map.assocs $ fmap (attemptToAssign sortAssignment) possibleVars

        -- TODO fix this: Might be easier to branch on the formal sort
        --   then, branch on the argsort and be methodical
-}

-- Filter away "uninteresting" constraints for logging. Specifically, well-formednes
-- Definitely not complete, just "pretty good"
isInteresting :: Formula -> Bool
isInteresting (Binary Ge (IntLit _) (IntLit 0)) 
  = False
isInteresting (Binary Ge (Var _ _) (IntLit 0)) 
  = False
isInteresting (Binary Implies _ f) 
  = isInteresting f 
isInteresting (BoolLit True) 
  = False
isInteresting (Binary And f g) 
  = isInteresting f || isInteresting g 
isInteresting _ 
  = True

getAnnotationStyle = getAnnotationStyle' . toMonotype 

getAnnotationStyle' t = 
  let rforms = conjunction $ allRFormulas True t
  in 
    case (varsOnly rforms, predsOnly rforms) of 
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