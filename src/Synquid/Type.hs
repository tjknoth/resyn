{-# LANGUAGE DeriveFunctor #-}

-- | Refinement Types
module Synquid.Type where

import Synquid.Logic
import Synquid.Util

import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Map as Map
import           Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import           Data.Map (Map)
import           Data.Bifunctor
import           Data.Bifoldable
import           Data.Maybe (catMaybes)

{- Type skeletons -}

data BaseType r p = 
  BoolT | 
  IntT | 
  DatatypeT !Id ![TypeSkeleton r p] ![r] | 
  TypeVarT !Substitution !Id !p
  deriving (Show, Eq, Ord)

-- | Type skeletons (parametrized by refinements, potentials)
data TypeSkeleton r p =
  ScalarT !(BaseType r p) !r !p |
  FunctionT !Id !(TypeSkeleton r p) !(TypeSkeleton r p) !Int |
  LetT !Id !(TypeSkeleton r p) !(TypeSkeleton r p) |
  AnyT
  deriving (Show, Eq, Ord)

instance Bifunctor TypeSkeleton where 
  bimap f g (ScalarT b r p) = ScalarT (bimap f g b) (f r) (g p)
  bimap f g (FunctionT x argT resT c) = FunctionT x (bimap f g argT) (bimap f g resT) c
  bimap f g (LetT x t bodyT) = LetT x (bimap f g t) (bimap f g bodyT)
  bimap _ _ AnyT = AnyT

instance Bifunctor BaseType where 
  bimap f g (DatatypeT x ts ps) = DatatypeT x (map (bimap f g) ts) (map f ps)
  bimap _ g (TypeVarT subs x m) = TypeVarT subs x (g m)
  bimap _ _ BoolT = BoolT
  bimap _ _ IntT = IntT

instance Bifoldable TypeSkeleton where 
  bifoldMap f g (ScalarT b r p) = f r `mappend` g p `mappend` bifoldMap f g b
  bifoldMap f g (FunctionT x argT resT c) = bifoldMap f g argT `mappend` bifoldMap f g resT
  bifoldMap f g (LetT x t bodyT) = bifoldMap f g bodyT 
  bifoldMap _ _ AnyT = mempty

instance Bifoldable BaseType where 
  -- Ignore predicates
  bifoldMap f g (DatatypeT x ts ps) = foldMap (bifoldMap f g) ts
  bifoldMap _ g (TypeVarT subs x m) = g m 
  bifoldMap _ _ BoolT = mempty
  bifoldMap _ _ IntT = mempty

-- | Unrefined typed
type SType = TypeSkeleton () Formula

-- | Refined types
type RType = TypeSkeleton Formula Formula

-- | Unrefined schemas
type SSchema = SchemaSkeleton SType 

-- | Refined schemas
type RSchema = SchemaSkeleton RType 

-- | Refinement base type
type RBase = BaseType Formula Formula

-- Ignore multiplicity and potential when comparing baseTypes
equalShape :: RBase -> RBase -> Bool
equalShape (TypeVarT s name _) (TypeVarT s' name' m') = (TypeVarT s name defMultiplicity :: RBase ) == (TypeVarT s' name' defMultiplicity :: RBase)
equalShape (DatatypeT name ts ps) (DatatypeT name' ts' ps') = (name == name') && (fmap shape ts == fmap shape ts') && (ps == ps')
equalShape t t' = t == t'

defPotential = IntLit 0
defMultiplicity = IntLit 1 
defCost = 0 :: Int

potentialPrefix = "p"
multiplicityPrefix = "m"

contextual x tDef (FunctionT y tArg tRes cost) = FunctionT y (contextual x tDef tArg) (contextual x tDef tRes) cost
contextual _ _ AnyT = AnyT
contextual x tDef t = LetT x tDef t

isScalarType ScalarT{} = True
-- isScalarType (LetT _ _ t) = isScalarType t
isScalarType LetT{} = True
isScalarType _ = False
baseTypeOf (ScalarT baseT _ _) = baseT
baseTypeOf (LetT _ _ t) = baseTypeOf t
baseTypeOf t = error "baseTypeOf: applied to a function type"
isFunctionType FunctionT{} = True
-- isFunctionType (LetT _ _ t) = isFunctionType t
isFunctionType _ = False
argType (FunctionT _ t _ _) = t
resType (FunctionT _ _ t _) = t

hasAny AnyT = True
hasAny (ScalarT baseT _ _) = baseHasAny baseT
  where
    baseHasAny (DatatypeT _ tArgs _) = any hasAny tArgs
    baseHasAny _ = False
hasAny (FunctionT _ tArg tRes _) = hasAny tArg || hasAny tRes
hasAny (LetT _ tDef tBody) = hasAny tDef || hasAny tBody

-- | Convention to indicate "any datatype" (for synthesizing match scrtuinees)
anyDatatype = ScalarT (DatatypeT dontCare [] []) ftrue defPotential

toSort :: BaseType r p -> Sort
toSort BoolT = BoolS
toSort IntT = IntS
toSort (DatatypeT name tArgs _) = DataS name (map (toSort . baseTypeOf) tArgs)
toSort (TypeVarT _ name _) = VarS name

fromSort :: Sort -> RType
fromSort = flip refineSort ftrue

refineSort :: Sort -> Formula -> RType
refineSort BoolS f = ScalarT BoolT f defPotential
refineSort IntS f = ScalarT IntT f defPotential
refineSort (VarS name) f = ScalarT (TypeVarT Map.empty name defMultiplicity) f defPotential
refineSort (DataS name sArgs) f = ScalarT (DatatypeT name (map fromSort sArgs) []) f defPotential
refineSort (SetS s) f = ScalarT dt f defPotential
  where
    dt = DatatypeT setTypeName [fromSort s] []
refineSort AnyS _ = AnyT

typeIsData :: TypeSkeleton r p -> Bool
typeIsData (ScalarT DatatypeT{} _ _) = True
typeIsData _ = False

arity :: TypeSkeleton r p -> Int
arity (FunctionT _ _ t _) = 1 + arity t
arity (LetT _ _ t) = arity t
arity _ = 0

-- TODO: make sure the AnyT case is OK
hasSet :: TypeSkeleton r p -> Bool
hasSet (ScalarT (DatatypeT name _ _) _ _) = name == setTypeName
hasSet (FunctionT _ t1 t2 _) = hasSet t1 || hasSet t2
hasSet (LetT _ t1 t2) = hasSet t1 || hasSet t2
hasSet _ = False

lastType (FunctionT _ _ tRes _) = lastType tRes
lastType (LetT _ _ t) = lastType t
lastType t = t

allArgTypes (FunctionT x tArg tRes _) = tArg : allArgTypes tRes
allArgTypes (LetT _ _ t) = allArgTypes t
allArgTypes _ = []

allArgs (ScalarT _ _ _) = []
allArgs (FunctionT x (ScalarT baseT _ _) tRes _) = Var (toSort baseT) x : allArgs tRes
allArgs (FunctionT _ _ tRes _) = allArgs tRes
allArgs (LetT _ _ t) = allArgs t

-- | Free variables of a type
varsOfType :: RType -> Set Id
varsOfType (ScalarT baseT fml _) = varsOfBase baseT `Set.union` Set.map varName (varsOf fml) --`Set.union` Set.map varName (varsOf pot)
  where
    varsOfBase (DatatypeT _ tArgs pArgs) = Set.unions (map varsOfType tArgs) `Set.union` Set.map varName (Set.unions (map varsOf pArgs))
    varsOfBase _ = Set.empty
varsOfType (FunctionT x tArg tRes _) = varsOfType tArg `Set.union` Set.delete x (varsOfType tRes)
varsOfType (LetT x tDef tBody) = varsOfType tDef `Set.union` Set.delete x (varsOfType tBody)
varsOfType AnyT = Set.empty

-- | Predicates mentioned in a type
predsOfType :: RType -> Set Id
predsOfType (ScalarT baseT fml _) = predsOfBase baseT `Set.union` predsOf fml --`Set.union` predsOf pot
  where
    predsOfBase (DatatypeT _ tArgs pArgs) = Set.unions (map predsOfType tArgs) `Set.union` Set.unions (map predsOf pArgs)
    predsOfBase _ = Set.empty
predsOfType (FunctionT _ tArg tRes _) = predsOfType tArg `Set.union` predsOfType tRes
predsOfType (LetT _ tDef tBody) = predsOfType tDef `Set.union` predsOfType tBody
predsOfType AnyT = Set.empty

-- | Predicates mentioned in an integer-sorted predicate argument position, 
--     or in a potential annotation 
predsOfPotential :: [Bool] -> RType -> Set Id
predsOfPotential isInt t = 
  let go = predsOfPotential isInt
      predsFromBase (DatatypeT dt tArgs pArgs) = 
        Set.unions (map go tArgs) `Set.union` Set.unions (map (\(_, p) -> predsOf p) (filter fst (zip isInt pArgs)))
      predsFromBase _ = Set.empty in
  case t of
    (ScalarT baseT _ pfml)    -> predsFromBase baseT `Set.union` predsOf pfml 
    (FunctionT _ tArg tRes _) -> go tArg `Set.union` go tRes
    (LetT _ tDef tBody)       -> go tDef `Set.union`  go tBody
    AnyT                      -> Set.empty


varRefinement x s = Var s valueVarName |=| Var s x
isVarRefinement (Binary Eq (Var _ v) (Var _ _)) = v == valueVarName
isVarRefinement _ = False


-- | Polymorphic type skeletons (parametrized by refinements)
data SchemaSkeleton t =
  Monotype !t |
  ForallT !Id !(SchemaSkeleton t) |       -- Type-polymorphic
  ForallP !PredSig !(SchemaSkeleton t)    -- Predicate-polymorphic
  deriving (Functor, Show, Eq, Ord)

{-instance Bifunctor SchemaSkeleton where 
  bimap f g (Monotype t) = Monotype $ bimap f g t
  bimap f g (ForallT ts sch) = ForallT ts (bimap f g sch)
  bimap f g (ForallP ps sch) = ForallP ps (bimap f g sch)
-}
toMonotype :: SchemaSkeleton t -> t 
toMonotype (Monotype t) = t
toMonotype (ForallT _ t) = toMonotype t 
toMonotype (ForallP _ t) = toMonotype t

boundVarsOf :: SchemaSkeleton t -> [Id]
boundVarsOf (ForallT a sch) = a : boundVarsOf sch
boundVarsOf _ = []

-- | Building types
bool r = ScalarT BoolT r defPotential
bool_ = bool () 
boolAll = bool ftrue 

int r = ScalarT IntT r defPotential
int_ = int () 
intAll = int ftrue 
intPot = ScalarT IntT ftrue
nat = int (valInt |>=| IntLit 0) 
pos = int (valInt |>| IntLit 0) 

vart n f = ScalarT (TypeVarT Map.empty n defMultiplicity) f defPotential
vart_ n = vart n () 
vartAll n = vart n ftrue
--vartSafe n f = ScalarT (TypeVarT Map.empty n (IntLit 1)) f defPotential
vartSafe = vart

set n f = ScalarT (DatatypeT setTypeName [tvar] []) f defPotential
  where
    tvar = ScalarT (TypeVarT Map.empty n defMultiplicity) ftrue defPotential
setAll n = set n ftrue

-- | Mapping from type variables to types
type TypeSubstitution = Map Id RType

-- | Mapping from (inferred) potential variables to (possible) formulas
type PotlSubstitution = OMap Id (Maybe Formula)

asSortSubst :: TypeSubstitution -> SortSubstitution
asSortSubst = Map.map (toSort . baseTypeOf)

-- | 'typeSubstitute' @subst t@ : apply substitution @subst@ to free type variables in @t@ 
typeSubstitute :: TypeSubstitution -> RType -> RType
typeSubstitute subst (ScalarT baseT r p) = addRefinement substituteBase (sortSubstituteFml (asSortSubst subst) r)
  where
    substituteBase = case baseT of
      (TypeVarT varSubst a m) -> case Map.lookup a subst of
        Just t -> substituteInType (not . (`Map.member` subst)) varSubst $ typeSubstitute subst (updateAnnotations t m p)
        Nothing -> ScalarT (TypeVarT varSubst a m) ftrue p
      DatatypeT name tArgs pArgs ->
        let
          tArgs' = map (typeSubstitute subst) tArgs
          pArgs' = map (sortSubstituteFml (asSortSubst subst)) pArgs
        in ScalarT (DatatypeT name tArgs' pArgs') ftrue p
      _ -> ScalarT baseT ftrue p
typeSubstitute subst (FunctionT x tArg tRes cost) = FunctionT x (typeSubstitute subst tArg) (typeSubstitute subst tRes) cost
typeSubstitute subst (LetT x tDef tBody) = LetT x (typeSubstitute subst tDef) (typeSubstitute subst tBody)
typeSubstitute _ AnyT = AnyT

noncaptureTypeSubst :: [Id] -> [RType] -> RType -> RType
noncaptureTypeSubst tVars tArgs t =
  let tFresh = typeSubstitute (Map.fromList $ zip tVars (map vartAll distinctTypeVars)) t
  in typeSubstitute (Map.fromList $ zip distinctTypeVars tArgs) tFresh

schemaSubstitute :: TypeSubstitution -> RSchema -> RSchema
schemaSubstitute tass (Monotype t) = Monotype $ typeSubstitute tass t
schemaSubstitute tass (ForallT a sch) = ForallT a $ schemaSubstitute (Map.delete a tass) sch
schemaSubstitute tass (ForallP sig sch) = ForallP sig $ schemaSubstitute tass sch

typeSubstitutePred :: Substitution -> RType -> RType
typeSubstitutePred pSubst t = 
  let tsp = typeSubstitutePred pSubst
  in case t of
    ScalarT (DatatypeT name tArgs pArgs) fml pot 
      -> ScalarT (DatatypeT name (map tsp tArgs) (map (substitutePredicate pSubst) pArgs)) (substitutePredicate pSubst fml) (substitutePredicate pSubst pot)
    ScalarT baseT fml pot 
      -> ScalarT baseT (substitutePredicate pSubst fml) (substitutePredicate pSubst pot)
    FunctionT x tArg tRes c 
      -> FunctionT x (tsp tArg) (tsp tRes) c
    LetT x tDef tBody 
      -> LetT x (tsp tDef) (tsp tBody)
    AnyT -> AnyT

schemaSubstitutePotl :: PotlSubstitution -> RSchema -> RSchema
schemaSubstitutePotl ts (ForallT i s) = ForallT i $ schemaSubstitutePotl ts s
schemaSubstitutePotl ts (ForallP i s) = ForallP i $ schemaSubstitutePotl ts s
schemaSubstitutePotl ts (Monotype b) = Monotype $ substitutePotl ts b

-- TODO: this assumes inferred potls can only be vars
substitutePotl :: PotlSubstitution -> RType -> RType
substitutePotl ts (ScalarT (DatatypeT di ta abs) ref v) =
  ScalarT (DatatypeT di (fmap (substitutePotl ts) ta) (fmap (lookupIPotl ts) abs)) ref (lookupIPotl ts v)
substitutePotl ts (ScalarT dt ref v) =
  ScalarT dt ref (lookupIPotl ts v)
substitutePotl ts (FunctionT i d c cs) = FunctionT i (substitutePotl ts d) (substitutePotl ts c) cs
substitutePotl ts (LetT i def body) = LetT i (substitutePotl ts def) (substitutePotl ts body)
substitutePotl _ AnyT = AnyT

-- TODO: This only works if the formula is only an inference var and nothing else
--       If the formula isn't only an inference var but contains one, this
--       doesn't replace it
lookupIPotl :: PotlSubstitution -> Formula -> Formula
lookupIPotl ts v@(Var IntS pVar) = case OMap.lookup pVar ts of
    Just (Just x)  -> x
    _              -> v
lookupIPotl _ x = x


-- | 'typeVarsOf' @t@ : all type variables in @t@
typeVarsOf :: TypeSkeleton r p -> Set Id
typeVarsOf t@(ScalarT baseT _ _) = case baseT of
  TypeVarT _ name _ -> Set.singleton name
  DatatypeT _ tArgs _ -> Set.unions (map typeVarsOf tArgs)
  _ -> Set.empty
typeVarsOf (FunctionT _ tArg tRes _) = typeVarsOf tArg `Set.union` typeVarsOf tRes
typeVarsOf (LetT _ tDef tBody) = typeVarsOf tDef `Set.union` typeVarsOf tBody
typeVarsOf _ = Set.empty

-- | 'updateAnnotations' @t m p@ : "multiply" @t@ by multiplicity @m@, then add on surplus potential @p@
updateAnnotations :: RType -> Formula -> Formula -> RType
updateAnnotations t@ScalarT{} mult = safeAddPotential (typeMultiply mult t)

schemaMultiply p = fmap (typeMultiply p)

typeMultiply :: Formula -> RType -> RType
typeMultiply fml (ScalarT t ref pot) = ScalarT (baseTypeMultiply fml t) ref (multiplyFormulas fml pot)
typeMultiply fml t = t

baseTypeMultiply :: Formula -> RBase -> RBase
baseTypeMultiply fml (TypeVarT subs name mul) = TypeVarT subs name (multiplyFormulas mul fml)
baseTypeMultiply fml (DatatypeT name tArgs pArgs) = DatatypeT name (map (typeMultiply fml) tArgs) pArgs
baseTypeMultiply fml t = t

safeAddPotential :: RType -> Formula -> RType 
safeAddPotential (ScalarT base ref pot) f = ScalarT base ref (safeAddFormulas pot f)
safeAddPotential (LetT x tDef tBody) f    = LetT x tDef (safeAddPotential tBody f)
safeAddPotential t _ = t

-- safeAddFormulas f g : Adds f to g -- if g is a conditional, it pushes f into the conditional structure
--  used as a hack to make conditional solver work w polynomials
safeAddFormulas :: Formula -> Formula -> Formula
safeAddFormulas f (Ite f1 f2 f3) = Ite f1 (addFormulas f f2) (addFormulas f f3)
safeAddFormulas f g = addFormulas f g


addPotential :: RType -> Formula -> RType 
addPotential (ScalarT base ref pot) f = ScalarT base ref (addFormulas pot f)
addPotential (LetT x tDef tBody) f    = LetT x tDef (addPotential tBody f)
addPotential t _ = t

subtractPotential :: RType -> Formula -> RType
subtractPotential (ScalarT base ref pot) f = ScalarT base ref (addFormulas pot (fneg f)) -- (negateFml f))
subtractPotential (LetT x tDef tBody) f = LetT x tDef (subtractPotential tBody f)
subtractPotential t _ = t

-- Extract top-level potential from a scalar type 
topPotentialOf :: RType -> Maybe Formula 
topPotentialOf (ScalarT _ _ p) = Just p
topPotentialOf _               = Nothing

{- Refinement types -}

-- | Forget refinements of a type
shape :: RType -> SType
shape (ScalarT (DatatypeT name tArgs pArgs) _ _) = ScalarT (DatatypeT name (map shape tArgs) (replicate (length pArgs) ())) () defPotential
shape (ScalarT IntT _ _) = ScalarT IntT () defPotential
shape (ScalarT BoolT _ _) = ScalarT BoolT () defPotential
shape (ScalarT (TypeVarT _ a _) _ _) = ScalarT (TypeVarT Map.empty a defMultiplicity) () defPotential
shape (FunctionT x tArg tFun _) = FunctionT x (shape tArg) (shape tFun) 0 
shape (LetT _ _ t) = shape t
shape AnyT = AnyT

-- | Conjoin refinement to a type
addRefinement :: RType -> Formula -> RType
addRefinement (ScalarT base fml pot) fml' = if isVarRefinement fml'
  then ScalarT base fml' pot -- the type of a polymorphic variable does not require any other refinements
  else ScalarT base (fml `andClean` fml') pot
addRefinement (LetT x tDef tBody) fml = LetT x tDef (addRefinement tBody fml)
addRefinement t (BoolLit True) = t
addRefinement AnyT _ = AnyT
addRefinement t _ = error $ "addRefinement: applied to function type: " ++ show t

-- | Conjoin refinement to the return type
addRefinementToLast fml t@ScalarT{} = addRefinement t fml
addRefinementToLast fml (FunctionT x tArg tRes c) = FunctionT x tArg (addRefinementToLast fml tRes) c
addRefinementToLast fml (LetT x tDef tBody) = LetT x tDef (addRefinementToLast fml tBody)

-- | Conjoin refinement to the return type inside a schema
addRefinementToLastSch :: Formula -> RSchema -> RSchema
addRefinementToLastSch fml = fmap (addRefinementToLast fml)

-- | Apply variable substitution in all formulas inside a type
substituteInType :: (Id -> Bool) -> Substitution -> RType -> RType
substituteInType isBound subst (ScalarT baseT fml pot) = ScalarT (substituteBase subst baseT) (substitute subst fml) (substitute subst pot)
  where
    -- TODO: does this make sense?
    substituteBase subst (TypeVarT oldSubst a m) = TypeVarT oldSubst a (substitute subst m)
      -- Looks like pending substitutions on types are not actually needed, since renamed variables are always out of scope
       -- if isBound a
          -- then TypeVarT oldSubst a
          -- else TypeVarT (oldSubst `composeSubstitutions` subst) a
    substituteBase subst (DatatypeT name tArgs pArgs) = DatatypeT name (map (substituteInType isBound subst) tArgs) (map (substitute subst) pArgs)
    substituteBase _ baseT = baseT
substituteInType isBound subst (FunctionT x tArg tRes c) =
  if Map.member x subst
    then error $ unwords ["Attempt to substitute variable", x, "bound in a function type"]
    else FunctionT x (substituteInType isBound subst tArg) (substituteInType isBound subst tRes) c
substituteInType isBound subst (LetT x tDef tBody) =
  if Map.member x subst
    then error $ unwords ["Attempt to substitute variable", x, "bound in a contextual type"]
    else LetT x (substituteInType isBound subst tDef) (substituteInType isBound subst tBody)
substituteInType isBound _ AnyT = AnyT

-- | 'renameVar' @old new t typ@: rename all occurrences of @old@ in @typ@ into @new@ of type @t@
renameVar :: (Id -> Bool) -> Id -> Id -> RType -> RType -> RType
renameVar isBound old new (ScalarT b _ _) t            = substituteInType isBound (Map.singleton old (Var (toSort b) new)) t
renameVar isBound old new (LetT _ _ tBody) t           = renameVar isBound old new tBody t
renameVar _ _ _ _ t = t -- function arguments cannot occur in types (and AnyT is assumed to be function)

-- | Intersection of two types (assuming the types were already checked for consistency) 
intersection _ t AnyT = t
intersection _ AnyT t = t
intersection isBound (ScalarT baseT fml pot) (ScalarT baseT' fml' pot') = case baseT of
  DatatypeT name tArgs pArgs -> let DatatypeT _ tArgs' pArgs' = baseT' in
                                  ScalarT (DatatypeT name (zipWith (intersection isBound) tArgs tArgs') (zipWith andClean pArgs pArgs')) (fml `andClean` fml') (fmax pot pot') 
  _ -> ScalarT baseT (fml `andClean` fml') (fmax pot pot')
intersection isBound (FunctionT x tArg tRes c) (FunctionT y tArg' tRes' c') = FunctionT x tArg (intersection isBound tRes (renameVar isBound y x tArg tRes')) (max c c')

-- Move cost annotations to next arrow or to scalar argument type before applying function
shiftCost :: RType -> RType
shiftCost (FunctionT x argT resT c) = FunctionT x (addPotential argT (IntLit c)) resT 0
  --if isScalarType resT
  --  then FunctionT x (addPotential argT (IntLit c)) resT 0 
  --  else FunctionT x argT (addCostToArrow resT) 0
  --where 
  --  addCostToArrow (FunctionT y a r cost) = FunctionT y a r (cost + c)

-- | Instantiate unknowns in a type
-- TODO: eventually will need to instantiate potential variables as well
typeApplySolution :: Solution -> RType -> RType
typeApplySolution sol = first (applySolution sol)

allRefinementsOf :: RSchema -> [Formula]
allRefinementsOf sch = allRefinementsOf' $ toMonotype sch

allRefinementsOf' (ScalarT _ ref _) = [ref]
allRefinementsOf' (FunctionT _ argT resT _) = allRefinementsOf' argT ++ allRefinementsOf' resT
allRefinementsOf' _ = error "allRefinementsOf called on contextual or any type"

-- | 'allRFormulas' @t@ : return all resource-related formulas (potentials and multiplicities) from a refinement type @t@
allRFormulas :: Map Id [Bool] -> RType -> [Formula]
allRFormulas flagMap t = 
  let concretePotentials = bifoldMap (const []) (: []) t
      abstractPotentials = allAbstractPotentials flagMap t 
  in concretePotentials ++ abstractPotentials
 -- collect potential annotations
 -- collect resource preds

allAbstractPotentials :: Map Id [Bool] -> RType -> [Formula]
allAbstractPotentials flagMap (ScalarT b _ pot) = allAbstractPotentialsBase flagMap b
allAbstractPotentials flagMap (FunctionT _ argT resT _) = allAbstractPotentials flagMap argT ++ allAbstractPotentials flagMap resT
allAbstractPotentials flagMap (LetT _ tDef tBody) = allAbstractPotentials flagMap tDef ++ allAbstractPotentials flagMap tBody
allAbstractPotentials _ AnyT = []

allAbstractPotentialsBase :: Map Id [Bool] -> RBase -> [Formula]
allAbstractPotentialsBase flagMap (DatatypeT dt ts preds) = 
  case Map.lookup dt flagMap of
    Nothing     -> error $ "allAbstractPotentialsBase: datatype " ++ dt ++ " not found"
    Just rflags -> catMaybes $ zipWith (\isRes pred -> if isRes then Just pred else Nothing) rflags preds
allAbstractPotentialsBase _ _ = []

allArgSorts :: RType -> [Sort]
allArgSorts (FunctionT _ (ScalarT b _ _) resT _) = toSort b : allArgSorts resT
allArgSorts FunctionT{} = error "allArgSorts: Non-scalar type in argument position"
allArgSorts ScalarT{} = []
allArgSorts LetT{} = error "allArgSorts: contextual type"

resultSort :: RType -> Sort
resultSort (FunctionT _ _ resT _) = resultSort resT
resultSort (ScalarT b _ _) = toSort b

isDataType DatatypeT{} = True 
isDataType _           = False

getConditional :: RType -> Maybe Formula
getConditional (ScalarT _ _ f@(Ite g _ _)) = Just f
getConditional _ = Nothing

removePotentialSch :: RSchema -> RSchema
removePotentialSch = fmap removePotential 

removePotential (ScalarT b r _) = ScalarT (removePotentialBase b) r fzero
removePotential (FunctionT x arg res c) = FunctionT x (removePotential arg) (removePotential res) 0
removePotential t = t

removePotentialBase (DatatypeT x ts ps) = DatatypeT x (map removePotential ts) ps
removePotentialBase b = b

-- Set strings: used for "fake" set type for typechecking measures
emptySetCtor = "Emptyset"
singletonCtor = "Singleton"
insertSetCtor = "Insert"
setTypeName = "DSet"
setTypeVar = "setTypeVar"
