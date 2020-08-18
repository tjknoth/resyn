{-# LANGUAGE TupleSections, FlexibleContexts, TemplateHaskell #-}

-- | Functions for processing the AST created by the Parser (eg filling in unknown types, verifying that refinement formulas evaluate to a boolean, etc.)
module Synquid.Resolver (
  resolveDecls, 
  resolveRefinement, 
  resolveRefinedType, 
  addAllVariables, 
  ResolverState (..), 
  instantiateSorts
) where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.Util

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Lens
import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Set (Set)
import           Data.Maybe
import           Data.List
import qualified Data.Foldable as Foldable
import           Control.Arrow (first)

import Debug.Pretty.Simple

{- Interface -}

data ResolverState = ResolverState {
  _environment :: Environment,
  _goals :: [(Id, (UProgram, SourcePos))],
  _checkingGoals :: [(Id, (UProgram, SourcePos))],
  _condQualifiers :: [Formula],
  _typeQualifiers :: [Formula],
  _mutuals :: Map Id [Id],
  _inlines :: Map Id ([Id], Formula),
  _sortConstraints :: [SortConstraint],
  _currentPosition :: SourcePos,
  _idCount :: Int,
  _pvarCount :: Int,
  _potentialVars :: Set Id,
  _infer :: Bool, -- ^ whether we should attempt to infer fn arg pot'ls
  _inferredPotlVars :: Map Id [Id]  -- ^ maps fn name to associated inferred pot'ls, in order of priority
}

makeLenses ''ResolverState

initResolverState :: Bool -> ResolverState
initResolverState infer = ResolverState {
  _environment = emptyEnv,
  _goals = [],
  _checkingGoals = [],
  _condQualifiers = [],
  _typeQualifiers = [],
  _mutuals = Map.empty,
  _inlines = Map.empty,
  _sortConstraints = [],
  _currentPosition = noPos,
  _idCount = 0,
  _pvarCount = 0,
  _potentialVars = Set.empty,
  _infer = infer,
  _inferredPotlVars = Map.empty
}

-- | Convert a parsed program AST into a list of synthesis goals and qualifier maps
-- | The first argument determines if we should infer potentials for all fn args
resolveDecls :: Bool -> [Declaration] -> Either ErrorMessage ([Goal], [Formula], [Formula])
resolveDecls tryInfer declarations =
  case runExcept (execStateT go (initResolverState tryInfer)) of
    Left msg -> Left msg
    Right st ->
      Right (typecheckingGoals st ++ synthesisGoals st, st ^. condQualifiers, st ^. typeQualifiers)
  where
    go = do
      -- Pass 1: collect all declarations and resolve sorts, but do not resolve refinement types yet
      mapM_ (extractPos resolveDeclaration) declarations'
      -- Pass 2: resolve refinement types in signatures
      mapM_ (extractPos resolveSignatures) declarations'
    declarations' = setDecl : declarations
    setDecl = Pos noPos defaultSetType
    makeGoal inferSolve synth env allNames allMutuals inferredPVars (name, (impl, pos)) =
      let
        spec = allSymbols env Map.! name
        myMutuals = Map.findWithDefault [] name allMutuals
        toRemove = drop (fromJust $ elemIndex name allNames) allNames \\ myMutuals -- All goals after and including @name@, except mutuals
        flagMap = fmap _resourcePreds (env ^. datatypes)
        env' = (foldr removeVariable env toRemove) { _resourceMeasures = rMeasuresFromSch flagMap spec }

        -- We have to order our potential vars in order of which ones we want minimized first,
        -- since Z3 will minimize in this order
        --
        -- Counter-intuitively, we minimize the variables at the end first. This is because
        -- we don't want potential values on our return results and we prefer having our
        -- potentials on our first arguments
        pVars = uncurry (++)
              $ partition (\(x:_) -> x /= 'F')
              $ Map.findWithDefault [] name inferredPVars
      in Goal name env' spec impl 0 pos pVars inferSolve synth
    extractPos pass (Pos pos decl) = do
      currentPosition .= pos
      pass decl
    synthesisGoals st = fmap (makeGoal False True (st ^. environment) (map fst ((st ^. goals) ++ (st ^. checkingGoals))) (st ^. mutuals) (st ^. inferredPotlVars)) (st ^. goals)
    typecheckingGoals st = fmap (makeGoal False False (st ^. environment) (map fst ((st ^. goals) ++ (st ^. checkingGoals))) (st ^. mutuals) (st ^. inferredPotlVars)) (st ^. checkingGoals)

resolveRefinement :: Environment -> Formula -> Either ErrorMessage Formula
resolveRefinement env fml = runExcept (evalStateT (resolveTypeRefinement AnyS fml) ((initResolverState False) {_environment = env}))

resolveRefinedType :: Environment -> RType -> Set String -> Either ErrorMessage RType
resolveRefinedType env t extraSyms = runExcept (evalStateT (resolveType t) ((initResolverState False) {_environment = env, _potentialVars = extraSyms }))

instantiateSorts :: [Sort] -> [Sort]
instantiateSorts sorts = fromRight $ runExcept (evalStateT (instantiate sorts) (initResolverState False))

addAllVariables :: [Formula] -> Environment -> Environment
addAllVariables = flip (foldr (\(Var s x) -> addVariable x (fromSort s)))

{- Implementation -}

type Resolver a = StateT ResolverState (Except ErrorMessage) a

throwResError descr = do
  pos <- use currentPosition
  throwError $ ErrorMessage ResolutionError pos descr

resolveDeclaration :: BareDeclaration -> Resolver ()
resolveDeclaration (TypeDecl typeName typeVars typeBody) = do
  typeBody' <- resolveType typeBody
  let extraTypeVars = typeVarsOf typeBody' Set.\\ Set.fromList typeVars
  if Set.null extraTypeVars
    then environment %= addTypeSynonym typeName typeVars typeBody'
    else throwResError (text "Type variable(s)" <+> hsep (map text $ Set.toList extraTypeVars) <+>
              text "in the definition of type synonym" <+> text typeName <+> text "are undefined")
resolveDeclaration (FuncDecl funcName typeSchema) = do 
  tryInfer <- use infer
  if tryInfer
    then go typeSchema >>= addNewSignature funcName
    else addNewSignature funcName typeSchema
  where
    go :: RSchema -> Resolver RSchema
    go (ForallT i s) = go s >>= return . ForallT i
    go (ForallP i s) = go s >>= return . ForallP i
    go (Monotype b) = gt b >>= return . Monotype

    -- TODO: Maybe if the potential != 0, don't change it to an inferred?
    gt :: RType -> Resolver RType
    gt (ScalarT (DatatypeT di tyargs absps) ref _) = do
      tyargs' <- mapM gt tyargs
      pVar <- freshInferredPotl funcName "I"
      return $ ScalarT (DatatypeT di tyargs' absps) ref (Var IntS pVar)
    gt (ScalarT dt ref _) = do
      pVar <- freshInferredPotl funcName "I"
      return $ ScalarT dt ref (Var IntS pVar)
    gt (FunctionT i d c cs) = do
      dom <- gt d
      cod <- gt c
      return $ FunctionT i dom cod cs
    gt (LetT i def body) = do
      def' <- gt def
      body' <- gt body
      return $ LetT i def' body'
    gt AnyT = return AnyT
    
resolveDeclaration d@(DataDecl dtName tParams pVarParams ctors) = do
  let
    (pParams, pVariances) = unzip pVarParams
    resParams = extractResourceParams d
    datatype = DatatypeDef {
      _typeParams = tParams,
      _predParams = pParams,
      _predVariances = pVariances,
      _constructors = map constructorName ctors,
      _wfMetric = Nothing,
      _resourcePreds = resParams
    }
  environment %= addDatatype dtName datatype
  let addPreds typ = foldl (flip ForallP) (Monotype typ) pParams
  mapM_ (\(ConstructorSig name typ) -> addNewSignature name $ addPreds typ) ctors
resolveDeclaration (MeasureDecl measureName inSort outSort post defCases args isTermination) = do
  env <- use environment
  let allInSorts = fmap snd args ++ [inSort]
  let varSortPairs = fmap (first Just) args ++ [(Nothing, inSort)]
  addNewSignature measureName (generateSchema env measureName varSortPairs outSort post)
  -- Resolve measure signature:
  mapM_ (resolveSort . snd) args 
  resolveSort inSort
  resolveSort outSort
  case inSort of
    DataS dtName sArgs -> do
      -- Check that the input sort of the measure is D a_i, where a_i are the type parameters in the declaration of D:
      datatype <- uses (environment . datatypes) (Map.! dtName)
      let tParams = datatype ^. typeParams
      let declDtSort = DataS dtName (map VarS tParams)
      if inSort /= declDtSort
        then throwResError (text "Type parameters of measure" <+> text measureName <+> text "must be the same as in the datatype declaration")
        else do
          environment %= addGlobalPredicate measureName outSort allInSorts 
          -- Possibly add as termination metric:
          when isTermination $ 
            if isJust $ datatype ^. wfMetric
              then throwResError (text "Multiple termination metrics defined for datatype" <+> text dtName)
              else if outSort == IntS
                   then environment %= addDatatype dtName datatype { _wfMetric = Just measureName }
                   else throwResError (text "Output sort of termination measure" <+> text measureName <+> text "must be Int")
    _ -> throwResError (text "Input sort of measure" <+> text measureName <+> text "must be a datatype")
resolveDeclaration (PredDecl (PredSig name argSorts resSort)) = do
  ifM (Map.member name <$> use (environment . globalPredicates)) (throwResError (text "Duplicate declaration of predicate" <+> text name)) (return ())
  mapM_ resolveSort (resSort : argSorts)
  env <- use environment
  let argSorts' = fmap (\x -> (Nothing, x)) argSorts
  addNewSignature name (generateSchema env name argSorts' resSort ftrue) 
  environment %= addGlobalPredicate name resSort argSorts
resolveDeclaration (SynthesisGoal name impl) = do
  syms <- uses environment allSymbols
  pos <- use currentPosition
  if Map.member name syms
    then goals %= (++ [(name, (normalizeProgram impl, pos))])
    else throwResError (text "No specification found for synthesis goal" <+> text name)
resolveDeclaration (QualifierDecl quals) = mapM_ resolveQualifier quals
  where
    resolveQualifier q = if Set.member valueVarName (Set.map varName $ varsOf q)
      then typeQualifiers %= (q:)
      else condQualifiers %= (q:)
resolveDeclaration (MutualDecl names) = mapM_ addMutuals names
  where
    addMutuals name = do
      goalMb <- uses goals (lookup name)
      case goalMb of
        Just _ -> mutuals %= Map.insert name (delete name names)
        Nothing -> throwResError (text "Synthesis goal" <+> text name <+> text "in a mutual clause is undefined")
resolveDeclaration (InlineDecl name args body) =
  ifM (uses inlines (Map.member name))
    (throwResError (text "Duplicate definition of inline" <+> text name))
    (do
      let extraVars = Set.map varName (varsOf body) `Set.difference` Set.fromList args
      if not $ Set.null extraVars
        then throwResError (text "Variables" <+> hsep (map text $ Set.toList extraVars) <+> text "undefined in the body of inline" <+> text name)
        else inlines %= Map.insert name (args, body))

resolveSignatures :: BareDeclaration -> Resolver ()
resolveSignatures (FuncDecl name _)  = do
  sch <- uses environment ((Map.! name) . allSymbols)
  sch' <- inferAbstractPotls >=> resolveSchema $ sch
  environment %= addPolyConstant name sch'
  environment %= addUnresolvedConstant name sch'
  where
    inferAbstractPotls (ForallT name ss) = inferAbstractPotls ss >>= return . ForallT name
    inferAbstractPotls (ForallP name ss) = inferAbstractPotls ss >>= return . ForallP name
    inferAbstractPotls (Monotype t) = go t >>= return . Monotype

    go og@(ScalarT (DatatypeT dtName tArgs pArgs) ref pred) = do
      tArgs' <- mapM go tArgs
      ds <- use $ environment . datatypes
      case Map.lookup dtName ds of
        Just (DatatypeDef _ preds _ _ _ _) -> do
          tryInfer <- use infer
          pArgs' <- zipWithM (maybeFreshPotl tryInfer) pArgs (fmap isResParam preds)
          return (ScalarT (DatatypeT dtName tArgs' pArgs') ref pred)
        Nothing -> return og
    go og@(ScalarT _ _ _) = return og
    go (FunctionT name dom cod cost) = do
      dom' <- go dom
      cod' <- go cod
      return $ FunctionT name dom' cod' cost
    go (LetT name def body) = do
      def' <- go def
      body' <- go body
      return $ LetT name def' body'
    go AnyT = return AnyT

    maybeFreshPotl tryInfer arg isPred
      | isPred && tryInfer = fmap (Var IntS) $ freshInferredPotl name "F"
      | otherwise          = return arg

    -- Checks if an abstract arg is a predicate or a resource
    -- This is different than what extractResourceParams generates because we only
    -- check whether the return type of the abstract argument is an Int or not
    isResParam p = predSigResSort p == IntS
      
resolveSignatures (DataDecl dtName tParams pParams ctors) = mapM_ resolveConstructorSignature ctors
  where
    resolveConstructorSignature (ConstructorSig name _) = do
      sch <- uses environment ((Map.! name) . allSymbols)
      sch' <- resolveSchema sch
      let nominalType = ScalarT (DatatypeT dtName (map vartAll tParams) (map (nominalPredApp  . fst) pParams)) ftrue defPotential
      let returnType = lastType (toMonotype sch')
      if shape nominalType == shape returnType
        then do
          let nominalSort = toSort $ baseTypeOf nominalType
          let sch'' = addRefinementToLastSch (Var nominalSort valueVarName |=| Cons nominalSort name (allArgs (toMonotype sch'))) sch'
          environment %= addPolyConstant name sch''
        else throwResError (commaSep [text "Constructor" <+> text name <+> text "must return type" <+> pretty nominalType, text "got" <+> pretty returnType])
resolveSignatures (MeasureDecl measureName _ _ post defCases args _) = do
  sorts <- uses (environment . globalPredicates) (Map.! measureName)
  let (outSort : mArgs) = sorts
  case last mArgs of 
    inSort@(DataS dtName sArgs) -> do
      datatype <- uses (environment . datatypes) (Map.! dtName)
      post' <- resolveTypeRefinement outSort post
      pos <- use currentPosition
      let ctors = datatype ^. constructors
      if length defCases /= length ctors
        then throwResError $ text "Definition of measure" <+> text measureName <+> text "must include one case per constructor of" <+> text dtName
        else do
          freshConsts <- mapM (uncurry freshId) args
          let constSubst = zip (fmap fst args) freshConsts
          defs' <- mapM (resolveMeasureDef ctors constSubst) defCases
          mapM_ (\(MeasureCase _ _ impl) -> checkMeasureCase measureName args impl) defCases
          sch <- uses environment ((Map.! measureName) . allSymbols)
          sch' <- resolveSchema sch
          environment %= addPolyConstant measureName sch'
          defCases' <- mapM (\(MeasureCase n args body) -> do
            body' <- resolveMeasureFormula body
            return (MeasureCase n args body')) defCases
          let args' = fmap (\(Var s x) -> (x, s)) freshConsts
          environment %= addMeasure measureName (MeasureDef inSort outSort defs' args' post')
          checkingGoals %= (++ [(measureName, (impl (MeasureDef inSort outSort defCases' args post'), pos))])
    _ -> throwResError $ text "Last input of measure" <+> text measureName <+> text "must be a datatype"
  where
    impl def = normalizeProgram $ measureProg measureName def
    resolveMeasureDef allCtors cSub (MeasureCase ctorName binders body) =
      if ctorName `notElem` allCtors
        then throwResError $ text "Not in scope: data constructor" <+> text ctorName <+> text "used in definition of measure" <+> text measureName
        else do
          consSch <- uses environment ((Map.! ctorName) . allSymbols)
          let consT = toMonotype consSch
          let n = arity consT
          if n /= length binders
            then throwResError $ text "Data constructor" <+> text ctorName <+> text "expected" <+> pretty n <+> text "binders and got" <+> pretty (length binders) <+> text "in definition of measure" <+> text measureName
            else do
              let ctorParams = allArgs consT
              let subst = Map.fromList $ cSub ++ zip binders ctorParams
              let fml = Pred AnyS measureName (fmap snd cSub ++ [Var AnyS valueVarName]) |=| substitute subst body
              fml' <- withLocalEnv $ do
                environment . boundTypeVars .= boundVarsOf consSch
                environment %= addAllVariables ctorParams
                environment %= addAllVariables (fmap snd cSub) 
                resolveTypeRefinement (toSort $ baseTypeOf $ lastType consT) fml
              return $ MeasureCase ctorName (map varName ctorParams) fml'
resolveSignatures (SynthesisGoal name impl) = do
  resolveHole impl
  return ()
resolveSignatures _ = return ()

-- 'resolveMeasureCase' @measure constArgs mCase@ : ensure that measure @name@ is called recursively with the same argumenst @constArgs@
checkMeasureCase :: Id -> [(Id, Sort)] -> Formula -> Resolver () 
checkMeasureCase measure [] _ = return () 
checkMeasureCase measure constArgs (Unary _ f) = checkMeasureCase measure constArgs f
checkMeasureCase measure constArgs (Binary _ f g) = do 
  checkMeasureCase measure constArgs f 
  checkMeasureCase measure constArgs g
checkMeasureCase measure constArgs (Ite f g h) = do 
  checkMeasureCase measure constArgs f 
  checkMeasureCase measure constArgs g
  checkMeasureCase measure constArgs h
checkMeasureCase measure constArgs (Cons _ _ fs) = 
  mapM_ (checkMeasureCase measure constArgs) fs
checkMeasureCase measure constArgs p@(Pred s x args) =
  if x == measure
    then do 
      let args' = take numArgs args
      let cArgs' = fmap (\(x, _) -> Var AnyS x) constArgs
      when (args' /= cArgs') $ throwResError $ text "Constant arguments to measure" <+> text measure <+> text "must not change in recursive call" <+> pretty p 
    else mapM_ (checkMeasureCase measure constArgs) args 
  where
    numArgs = length constArgs
checkMeasureCase _ _ _ = return ()


resolveHole :: Program RType -> Resolver RType
resolveHole Program{content = (PApp p1 p2)} = do
  resolveHole p1
  resolveHole p2
resolveHole Program{content = (PFun _ p)} = resolveHole p
resolveHole Program{content = (PIf p1 p2 p3)} = do
  resolveHole p1
  resolveHole p2
  resolveHole p3
resolveHole Program{content = (PMatch p _)} = resolveHole p
resolveHole Program{content = (PFix _ p)} = resolveHole p
resolveHole Program{content = (PLet _ p1 p2)} = do
  resolveHole p1
  resolveHole p2
-- Resolve type if hole, symbol, or err:
resolveHole Program{content = _, typeOf = t} = resolveType t

{- Types and sorts -}

resolveSchema :: RSchema -> Resolver RSchema
resolveSchema sch = do
  let tvs = Set.toList $ typeVarsOf (toMonotype sch)
  sch' <- withLocalEnv $ do
    environment . boundTypeVars %= (tvs ++)
    resolveSchema' sch
  return $ Foldable.foldl (flip ForallT) sch' tvs
  where
    resolveSchema' (ForallP sig@(PredSig predName argSorts resSort) sch) = do
      ifM (elem predName <$> uses (environment . boundPredicates) (map predSigName))
        (throwResError $ text "Duplicate predicate variables" <+> text predName)
        (return ())
      mapM_ resolveSort argSorts
   -- when (resSort /= BoolS) $ -- APs: removed to allow for APs
     -- throwResError (text "Bound predicate variable" <+> text predName <+> text "must return Bool")
      sch' <- withLocalEnv $ do
        environment %= addBoundPredicate sig
        resolveSchema' sch
      let extraTypeVars = (Set.unions (map typeVarsOfSort argSorts)) Set.\\ typeVarsOf (toMonotype sch')
      when (not $ Set.null extraTypeVars) $
        (throwResError $ text "Unbound variables" <+> (commaSep $ map pretty $ Set.toList extraTypeVars) <+> text "in sort of bound predicate" <+> text predName)
      return $ ForallP sig sch'
    resolveSchema' (Monotype t) = Monotype <$> resolveType t

resolveType :: RType -> Resolver RType
resolveType s@(ScalarT (DatatypeT name tArgs pArgs) fml pot) = do
  ds <- use $ environment . datatypes
  case Map.lookup name ds of
    Nothing -> do
      t' <- substituteTypeSynonym name tArgs >>= resolveType
      fml' <- resolveTypeRefinement (toSort $ baseTypeOf t') fml
      return $ addRefinement t' fml'
    Just (DatatypeDef tParams pParams _ _ _ _) -> do
      when (length tArgs /= length tParams) $
        throwResError $ text "Datatype" <+> text name <+> text "expected" <+> pretty (length tParams) <+> text "type arguments and got" <+> pretty (length tArgs) <+> pretty tParams
      when (length pArgs /= length pParams) $
        throwResError $ text "Datatype" <+> text name <+> text "expected" <+> pretty (length pParams) <+> text "predicate arguments and got" <+> pretty (length pArgs)
      -- Resolve type arguments:
      tArgs' <- mapM resolveType tArgs
      -- Resolve predicate arguments:
      let subst = noncaptureSortSubst tParams (map (toSort . baseTypeOf) tArgs')
      pArgs' <- zipWithM (resolvePredArg subst) pParams pArgs
      let baseT' = DatatypeT name tArgs' pArgs'
      -- Resolve refinementL
      fml' <- resolveTypeRefinement (toSort baseT') fml
      pot' <- resolveTypePotential (toSort baseT') pot
      return $ ScalarT baseT' fml' pot'
  where
    resolvePredArg :: (Sort -> Sort) -> PredSig -> Formula -> Resolver Formula
{-  resolvePredArg subst (PredSig _ argSorts BoolS) fml = withLocalEnv $ do -- APs: changed to allow resolution of non predicate APs
      let argSorts' = map subst argSorts
      let vars = zipWith Var argSorts' deBrujns
      environment %= addAllVariables vars
      case fml of
        Pred _ p [] -> resolveTypeRefinement AnyS (Pred BoolS p vars)
        _ -> resolveTypeRefinement AnyS fml
-}
    resolvePredArg subst (PredSig _ argSorts resSort) fml = withLocalEnv $ do
      let argSorts' = map subst argSorts
      let vars = zipWith Var argSorts' deBrujns
      environment %= addAllVariables vars
      case fml of
        Pred _ p [] -> resolveTypeAnnotation resSort AnyS (Pred resSort p vars)
        _ -> resolveTypeAnnotation resSort AnyS fml

resolveType (ScalarT baseT fml pot) = ScalarT <$> resolveBaseType baseT <*> resolveTypeRefinement (toSort baseT) fml <*> resolveTypePotential (toSort baseT) pot 

resolveType (FunctionT x tArg tRes c)  
  | c < 0 = throwResError $ text "resolveType: functions must incur non-negative cost"
  | x == valueVarName =
    throwResError $ text valueVarName <+> text "is a reserved variable name"
  | x == dontCare =
    error $ unwords ["resolveType: blank in function type", show (FunctionT x tArg tRes c)] -- Should never happen
  | otherwise = do
      tArg' <- resolveType tArg
      tRes' <- withLocalEnv $ do
        unless (isFunctionType tArg') (environment %= addVariable x tArg')
        resolveType tRes 
      return $ FunctionT x tArg' tRes' c
resolveType AnyT = return AnyT


resolveBaseType :: RBase -> Resolver RBase
resolveBaseType (TypeVarT subs name mult) = do
  mult' <- resolveTypePotential (VarS name) mult
  return $ TypeVarT subs name mult'
resolveBaseType t = return t


-- | Check that sort has no unknown datatypes
resolveSort :: Sort -> Resolver ()
resolveSort (SetS elSort) = resolveSort elSort
resolveSort s@(DataS name sArgs) = do
  ds <- use $ environment . datatypes
  case Map.lookup name ds of
    Nothing -> throwResError $ text "Datatype" <+> text name <+> text "is undefined in sort" <+> pretty s
    Just (DatatypeDef tParams _ _ _ _ _) -> do
      let n = length tParams
      when (length sArgs /= n) $ throwResError $ text "Datatype" <+> text name <+> text "expected" <+> pretty n <+> text "type arguments and got" <+> pretty (length sArgs)
      mapM_ resolveSort sArgs
resolveSort s = return ()

{- Formulas -}

-- | 'resolveTypeAnnotation' @valueSort fml@ : resolve @fml@ as a refinement with _v of sort @valueSort@;
-- when @valueSort@ is @AnyS@, _v must not occur
resolveTypeAnnotation :: Sort -> Sort -> Formula -> Resolver Formula
resolveTypeAnnotation _ _ (BoolLit True) = return $ BoolLit True -- Special case to allow undefined value sort for function types
resolveTypeAnnotation targetSort valueSort fml = do
  fml' <- withLocalEnv $ do -- Resolve fml with _v : valueSort
    case valueSort of
      AnyS -> return ()
      _ -> environment %= addVariable valueVarName (fromSort valueSort)
    resolveFormula fml
  enforceSame (sortOf fml') targetSort  -- Check sort of refinements 
  sortAssignment <- solveSortConstraints -- Solve sort constraints and substitute
  let fml'' = sortSubstituteFml sortAssignment fml'
  boundTvs <- use $ environment . boundTypeVars
  let freeTvs = typeVarsOfSort (sortOf fml'') Set.\\ Set.fromList boundTvs -- Remaining free type variables
  let resolvedFml = if Set.null freeTvs then fml'' else sortSubstituteFml (constMap freeTvs IntS) fml''

  -- boundPreds <- uses (environment . boundPredicates) (Set.fromList . map predSigName)
  -- let invalidPreds = negPreds resolvedFml `Set.intersection` boundPreds
  -- when (not $ Set.null invalidPreds) $
    -- throwResError $ text "Bound predicate(s)" <+> commaSep (map text $ Set.toList invalidPreds)<+> text "occur negatively in a refinement" <+> pretty resolvedFml
  return resolvedFml

resolveTypeRefinement = resolveTypeAnnotation BoolS 

resolveTypePotential = resolveTypeAnnotation IntS 

-- Partially resolve formula describing measure case (just replace inline predicates)
resolveMeasureFormula :: Formula -> Resolver Formula
resolveMeasureFormula (SetLit s fs) = do
  fs' <- mapM resolveMeasureFormula fs
  return $ SetLit s fs'
resolveMeasureFormula (Unary op f) = do
  f' <- resolveMeasureFormula f
  return $ Unary op f'
resolveMeasureFormula (Binary op f1 f2) = do
  f1' <- resolveMeasureFormula f1
  f2' <- resolveMeasureFormula f2
  return $ Binary op f1' f2'
resolveMeasureFormula (Ite f1 f2 f3) = do
  f1' <- resolveMeasureFormula f1
  f2' <- resolveMeasureFormula f2
  f3' <- resolveMeasureFormula f3
  return $ Ite f1' f2' f3'
resolveMeasureFormula (Pred s name f) = do
  inlineMb <- uses inlines (Map.lookup name)
  case inlineMb of
    Just (args, body) ->  
      resolveMeasureFormula (substitute (Map.fromList $ zip args f) body)
    Nothing -> do
      f' <- mapM resolveMeasureFormula f
      return $ Pred s name f'
resolveMeasureFormula (Cons s x f) = do
  f' <- mapM resolveMeasureFormula f
  return $ Cons s x f'
resolveMeasureFormula (All f1 f2) = do
  f1' <- resolveMeasureFormula f1
  f2' <- resolveMeasureFormula f2
  return $ All f1' f2'
resolveMeasureFormula f = return f


resolveFormula :: Formula -> Resolver Formula
resolveFormula (Var _ x) = do
  env <- use environment
  pSyms <- use potentialVars
  ipSyms <- use inferredPotlVars
  if Set.member x pSyms || Set.member x (Set.fromList (concat (foldr (:) [] ipSyms)))
    then return $ Var IntS x
    else case Map.lookup x (symbolsOfArity 0 env) of
      Just sch ->
        case sch of
          Monotype (ScalarT baseType _ _) -> do
            let s' = toSort baseType
            return $ Var s' x
          _ -> error $ unwords ["resolveFormula: encountered non-scalar variable", x, "in a formula"]
      Nothing -> resolveFormula (Pred AnyS x []) `catchError` -- Maybe it's a zero-argument predicate?
                const (throwResError $ text "Variable" <+> text x <+> text "is not in scope")      -- but if not, throw this error to avoid confusionn

resolveFormula (SetLit _ elems) = do
  elemSort <- freshSort
  elems' <- mapM resolveFormula elems
  zipWithM_ enforceSame (map sortOf elems') (repeat elemSort)
  return $ SetLit elemSort elems'

resolveFormula (Unary op fml) = fmap (Unary op) $ do
  fml' <- resolveFormula fml
  enforceSame (sortOf fml') (operandSort op)
  return fml'
  where
    operandSort Not = BoolS
    operandSort Neg = IntS

resolveFormula (Binary op l r) = do
  l' <- resolveFormula l
  r' <- resolveFormula r
  op' <- addConstraints op (sortOf l') (sortOf r')
  return $ Binary op' l' r'
  where
    addConstraints op sl sr
      | op == Eq  || op == Neq
        = enforceSame sl sr >> return op
      | op == And || op == Or || op == Implies || op == Iff
        = enforceSame sl BoolS >> enforceSame sr BoolS >> return op
      | op == Member
        = enforceSame (SetS sl) sr >> return op
      | op == Union || op == Intersect || op == Diff || op == Subset
        = do
            elemSort <- freshSort
            enforceSame sl (SetS elemSort)
            enforceSame sr (SetS elemSort)
            return op
      | op == Times || op == Plus || op == Minus
        = if isSetS sl
            then do
              elemSort <- freshSort
              enforceSame sl (SetS elemSort)
              enforceSame sr (SetS elemSort)
              return $ toSetOp op
            else enforceSame sl IntS >> enforceSame sr IntS >> return op
      | op == Le
        = if isSetS sl
            then do
              elemSort <- freshSort
              enforceSame sl (SetS elemSort)
              enforceSame sr (SetS elemSort)
              return $ toSetOp op
            else enforceSame sl sr >> sortConstraints %= (++ [IsOrd sl]) >> return op
      | op == Lt || op == Gt || op == Ge
        = enforceSame sl sr >> sortConstraints %= (++ [IsOrd sl]) >> return op

    toSetOp Times = Intersect
    toSetOp Plus = Union
    toSetOp Minus = Diff
    toSetOp Le = Subset

resolveFormula (Ite cond l r) = do
  cond' <- resolveFormula cond
  l' <- resolveFormula l
  r' <- resolveFormula r
  enforceSame (sortOf cond') BoolS
  enforceSame (sortOf l') (sortOf r')
  return $ Ite cond' l' r'

resolveFormula (Pred _ name argFmls) = do
  inlineMb <- uses inlines (Map.lookup name)
  case inlineMb of
    Just (args, body) -> resolveFormula (substitute (Map.fromList $ zip args argFmls) body)
    Nothing -> do
      ps <- uses environment allPredicates
      sorts <- case Map.lookup name ps of
                  Nothing -> throwResError $ text "Predicate or measure" <+> text name <+> text "is undefined"
                  Just sorts -> ifM (Map.member name <$> use (environment . globalPredicates))
                                  (instantiate sorts) -- if global, treat type variables as free
                                  (return sorts) -- otherwise, treat type variables as bound
      let (resSort : argSorts) = sorts
      if length argFmls /= length argSorts
          then throwResError $ text "Expected" <+> pretty (length argSorts) <+> text "arguments for predicate or measure" <+> text name <+> text "and got" <+> pretty (length argFmls)
          else do
            argFmls' <- mapM resolveFormula argFmls
            zipWithM_ enforceSame (map sortOf argFmls') argSorts
            return $ Pred resSort name argFmls'

resolveFormula (Cons _ name argFmls) = do
  syms <- uses environment allSymbols
  case Map.lookup name syms of
    Nothing -> throwResError $ text "Data constructor" <+> text name <+> text "is undefined"
    Just consSch -> do
      let consT = toMonotype consSch
      sorts <- instantiate $ map (toSort . baseTypeOf) $ lastType consT : allArgTypes consT
      let (resSort : argSorts) = sorts
      if length argSorts /= length argFmls
        then throwResError $ text "Constructor" <+> text name <+> text "expected" <+> pretty (length argSorts) <+> text "arguments and got" <+> pretty (length argFmls)
        else do
            argFmls' <- mapM resolveFormula argFmls
            zipWithM_ enforceSame (map sortOf argFmls') argSorts
            return $ Cons resSort name argFmls'

resolveFormula fml = return fml

{- Misc -}

-- Normalize program form for typechecking:
-- Move conditional and match statements to top level of untyped program
normalizeProgram :: UProgram -> UProgram
normalizeProgram p@Program{content = (PSymbol name)} = p
normalizeProgram p@Program{content = (PTick c prog)} = Program (PTick c (normalizeProgram prog)) AnyT
-- Ensure no conditionals inside application
normalizeProgram p@Program{content = (PApp fun arg)} =
  untypedProg $ case (isCond fun', isCond arg') of
    -- Both sides are conditionals, can transform either side.
    (True, True) -> transformLCond fun' arg'
    -- Transform left side of application
    (True, _)    -> transformLCond fun' arg'
    -- Transform right side of application
    (_, True)    -> transformRCond fun' arg'
    -- Do not transform
    _            -> PApp (normalizeProgram fun) (normalizeProgram arg)
  where
    fun' = normalizeProgram fun
    arg' = normalizeProgram arg

    untypedProg p = Program p AnyT

    isCond Program{content = (PIf _ _ _)}  = True
    isCond Program{content = (PMatch _ _)} = True
    isCond _                               = False

    transformCase prog (Case con args ex) = Case con args (untypedProg (prog (normalizeProgram ex)))

    -- Conditional is on left side of application
    transformLCond p@Program{content = (PIf guard t f)} p2    =
      PIf guard (untypedProg (PApp t p2)) (untypedProg (PApp f p2))
    transformLCond p@Program{content = (PMatch scr cases)} p2 =
      PMatch scr (fmap (transformCase (`PApp` p2)) cases)
    transformLCond l r = PApp l r

    -- Conditional is on right side of application
    transformRCond p2 p@Program{content = (PIf guard t f)}     =
      PIf guard (untypedProg (PApp p2 t)) (untypedProg (PApp p2 f))
    transformRCond p2 p@Program{content = (PMatch scr cases)}  =
      PMatch scr (fmap (transformCase (PApp p2)) cases)
    transformRCond l r = PApp l r

normalizeProgram p@Program{content = (PFun name body)} =
  Program (PFun name (normalizeProgram body)) AnyT
normalizeProgram p@Program{content = (PIf guard p1 p2)} =
  Program (PIf (normalizeProgram guard) (normalizeProgram p1) (normalizeProgram p2)) AnyT
normalizeProgram p@Program{content = (PMatch arg cases)} =
  Program (PMatch (normalizeProgram arg) (fmap normalizeCase cases)) AnyT
  where
    normalizeCase (Case con args expr) = Case con args (normalizeProgram expr)
normalizeProgram p@Program{content = (PFix fs body)} =
  Program (PFix fs (normalizeProgram body)) AnyT
normalizeProgram p@Program{content = (PLet var val body)} =
  Program (PLet var (normalizeProgram val) (normalizeProgram body)) AnyT
normalizeProgram p = p


nominalPredApp (PredSig pName argSorts resSort) = Pred resSort pName (zipWith Var argSorts deBrujns)

solveSortConstraints :: Resolver SortSubstitution
solveSortConstraints = do
  (unificationCs, typeClassCs) <- uses sortConstraints (partition isSameSortConstraint)
  tvs <- uses (environment . boundTypeVars) Set.fromList
  sortConstraints .= []
  idCount .= 0
  let (sls, srs) = unzip $ map (\(SameSort s1 s2) -> (s1, s2)) unificationCs
  subst <- case unifySorts tvs sls srs of
    Left (x, y) -> throwResError $ text "Cannot unify sorts" <+> pretty x <+> text "and" <+> pretty y
    Right subst -> return subst
  mapM_ (checkTypeClass subst) typeClassCs
  return subst
  where
    isSameSortConstraint (SameSort _ _) = True
    isSameSortConstraint _ = False

    checkTypeClass subst (IsOrd s) = let s' = sortSubstitute subst s in
      case s' of
        IntS -> return ()
        VarS _ -> return ()
        _ -> throwResError $ text "Sort" <+> pretty s' <+> text "is not ordered"

addNewSignature name sch = do
  ifM (Set.member name <$> use (environment . constants)) (throwResError $ text "Duplicate declaration of function" <+> text name) (return ())
  environment %= addPolyConstant name sch
  environment %= addUnresolvedConstant name sch

substituteTypeSynonym name tArgs = do
  tss <- use $ environment . typeSynonyms
  case Map.lookup name tss of
    Nothing -> throwResError $ text "Datatype or synonym" <+> text name <+> text "is undefined"
    Just (tVars, t) -> do
      when (length tArgs /= length tVars) $ throwResError $ text "Type synonym" <+> text name <+> text "expected" <+> pretty (length tVars) <+> text "type arguments and got" <+> pretty (length tArgs)
      return $ noncaptureTypeSubst tVars tArgs t

-- | 'freshSort' : fresh variable sort 
freshSort :: Resolver Sort
freshSort = do
  i <- use idCount
  idCount %= ( + 1)
  return $ VarS ("S" ++ show i)

-- | 'freshId' @p s@ : fresh var with prefix @p@ of sort @s@
freshId :: String -> Sort -> Resolver Formula
freshId p s = do 
  i <- use idCount 
  idCount %= (+ 1)
  return $ Var s (p ++ show i) 

-- | 'freshInferredPotl' @prefix@ : create a name for a fresh potential variable name
-- | corresponding to the pot'l of a fn argument which will be inferred
freshInferredPotl :: Id -> String -> Resolver Id
freshInferredPotl fname prefix = do
  i <- use pvarCount 
  pvarCount %= (+ 1)
  let x = prefix ++ show i
  syms <- uses environment allSymbols
  if Map.member x syms -- to avoid name collisions with existing vars
    then freshInferredPotl fname prefix
    else do
      inferredPotlVars %= Map.insertWith (flip (++)) fname [x]
      return x

-- | 'instantiate' @sorts@: replace all sort variables in @sorts@ with fresh sort variables
instantiate :: [Sort] -> Resolver [Sort]
instantiate sorts = do
  let tvs = Set.toList $ Set.unions (map typeVarsOfSort sorts)
  freshTvs <- replicateM (length tvs) freshSort
  return $ map (sortSubstitute $ Map.fromList $ zip tvs freshTvs) sorts

enforceSame :: Sort -> Sort -> Resolver ()
enforceSame sl sr
  | sl == sr    = return ()
  | otherwise   = sortConstraints %= (++ [SameSort sl sr])

-- | Perform an action and restore the initial environment
withLocalEnv :: Resolver a -> Resolver a
withLocalEnv c = do
  oldEnv <- use environment
  res <- c
  environment .= oldEnv
  return res
