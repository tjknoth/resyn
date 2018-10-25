-- | Refinement Types
module Synquid.Type where

import Synquid.Logic
import Synquid.Util

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

{- Type skeletons -}

data BaseType r = BoolT | 
  IntT | 
  DatatypeT !Id ![TypeSkeleton r] ![r] | 
  TypeVarT !Substitution !Id !Potential 
  deriving (Show, Eq, Ord)

-- | Type skeletons (parametrized by refinements)
data TypeSkeleton r =
  ScalarT !(BaseType r) !r !Potential |
  FunctionT !Id !(TypeSkeleton r) !(TypeSkeleton r) !Integer |
  LetT !Id !(TypeSkeleton r) !(TypeSkeleton r) |
  AnyT
  deriving (Show, Eq, Ord)


-- Ignore multiplicity and potential when comparing baseTypes
equalShape :: BaseType Formula -> BaseType Formula -> Bool
equalShape (TypeVarT s name _) (TypeVarT s' name' m') = (TypeVarT s name defMultiplicity :: BaseType Formula) == (TypeVarT s' name' defMultiplicity :: BaseType Formula)
equalShape (DatatypeT name ts ps) (DatatypeT name' ts' ps') = (name == name') && (fmap shape ts == fmap shape ts') && (ps == ps')
equalShape t t' = t == t'

defPotential = Fml $ IntLit 0
defMultiplicity = Fml $ IntLit 1 
defCost = 0

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
baseTypeOf _ = error "baseTypeOf: applied to a function type"
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

toSort :: BaseType t -> Sort
toSort BoolT = BoolS
toSort IntT = IntS
toSort (DatatypeT name tArgs _) = DataS name (map (toSort . baseTypeOf) tArgs)
toSort (TypeVarT _ name _) = VarS name

fromSort :: Sort -> TypeSkeleton Formula
fromSort = flip refineSort ftrue

refineSort :: Sort -> Formula -> TypeSkeleton Formula
refineSort BoolS f = ScalarT BoolT f defPotential
refineSort IntS f = ScalarT IntT f defPotential
refineSort (VarS name) f = ScalarT (TypeVarT Map.empty name defMultiplicity) f defPotential
refineSort (DataS name sArgs) f = ScalarT (DatatypeT name (map fromSort sArgs) []) f defPotential
refineSort (SetS s) f = ScalarT dt f defPotential
  where
    dt = DatatypeT setTypeName [fromSort s] []
refineSort AnyS _ = AnyT


typeIsData :: TypeSkeleton r -> Bool
typeIsData (ScalarT DatatypeT{} _ _) = True
typeIsData _ = False

arity :: TypeSkeleton r -> Int
arity (FunctionT _ _ t _) = 1 + arity t
arity (LetT _ _ t) = arity t
arity _ = 0

-- TODO: make sure the AnyT case is OK
hasSet :: TypeSkeleton r -> Bool
hasSet (ScalarT (DatatypeT name _ _) _ _) = name == setTypeName
hasSet (FunctionT _ t1 t2 _) = hasSet t1 || hasSet t2
hasSet (LetT _ t1 t2) = hasSet t1 || hasSet t2
hasSet _ = False

lastType (FunctionT _ _ tRes _) = lastType tRes
lastType (LetT _ _ t) = lastType t
lastType t = t

allArgTypes (FunctionT x tArg tRes _) = tArg : (allArgTypes tRes)
allArgTypes (LetT _ _ t) = allArgTypes t
allArgTypes _ = []

allArgs (ScalarT _ _ _) = []
allArgs (FunctionT x (ScalarT baseT _ _) tRes _) = (Var (toSort baseT) x) : (allArgs tRes)
allArgs (FunctionT _ _ tRes _) = (allArgs tRes)
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

-- | Free variables of a type
predsOfType :: RType -> Set Id
predsOfType (ScalarT baseT fml _) = predsOfBase baseT `Set.union` predsOf fml --`Set.union` predsOf pot
  where
    predsOfBase (DatatypeT _ tArgs pArgs) = Set.unions (map predsOfType tArgs) `Set.union` Set.unions (map predsOf pArgs)
    predsOfBase _ = Set.empty
predsOfType (FunctionT _ tArg tRes _) = predsOfType tArg `Set.union` predsOfType tRes
predsOfType (LetT _ tDef tBody) = predsOfType tDef `Set.union` predsOfType tBody
predsOfType AnyT = Set.empty

varRefinement x s = Var s valueVarName |=| Var s x
isVarRefinemnt (Binary Eq (Var _ v) (Var _ _)) = v == valueVarName
isVarRefinemnt _ = False


-- | Polymorphic type skeletons (parametrized by refinements)
data SchemaSkeleton r =
  Monotype !(TypeSkeleton r) |
  ForallT !Id !(SchemaSkeleton r) |       -- Type-polymorphic
  ForallP !PredSig !(SchemaSkeleton r)    -- Predicate-polymorphic
  deriving (Show, Eq, Ord)


toMonotype :: SchemaSkeleton r -> TypeSkeleton r
toMonotype (Monotype t) = t
toMonotype (ForallT _ t) = toMonotype t 
toMonotype (ForallP _ t) = toMonotype t

boundVarsOf :: SchemaSkeleton r -> [Id]
boundVarsOf (ForallT a sch) = a : boundVarsOf sch
boundVarsOf _ = []

-- | Building types
bool r = ScalarT BoolT r defPotential
bool_ = bool () 
boolAll = bool ftrue 

int r = ScalarT IntT r defPotential
int_ = int () 
intAll = int ftrue 
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
typeSubstitutePred pSubst t = let tsp = typeSubstitutePred pSubst
  in case t of
    ScalarT (DatatypeT name tArgs pArgs) fml pot 
      -> ScalarT (DatatypeT name (map tsp tArgs) (map (substitutePredicate pSubst) pArgs)) (substitutePredicate pSubst fml) (liftFmlOp (substitutePredicate pSubst) pot)
    ScalarT baseT fml pot 
      -> ScalarT baseT (substitutePredicate pSubst fml) (liftFmlOp (substitutePredicate pSubst) pot)
    FunctionT x tArg tRes c 
      -> FunctionT x (tsp tArg) (tsp tRes) c
    LetT x tDef tBody 
      -> LetT x (tsp tDef) (tsp tBody)
    AnyT -> AnyT

-- | 'typeVarsOf' @t@ : all type variables in @t@
typeVarsOf :: TypeSkeleton r -> Set Id
typeVarsOf t@(ScalarT baseT _ _) = case baseT of
  TypeVarT _ name _ -> Set.singleton name
  DatatypeT _ tArgs _ -> Set.unions (map typeVarsOf tArgs)
  _ -> Set.empty
typeVarsOf (FunctionT _ tArg tRes _) = typeVarsOf tArg `Set.union` typeVarsOf tRes
typeVarsOf (LetT _ tDef tBody) = typeVarsOf tDef `Set.union` typeVarsOf tBody
typeVarsOf _ = Set.empty

-- | 'updateAnnotations' @t m p@ : "multiply" @t@ by multiplicity @m@, then add on surplus potential @p@
updateAnnotations :: RType -> Potential -> Potential -> RType
updateAnnotations t@ScalarT{} mult = addPotential (typeMultiply mult t)

schemaMultiply :: Potential -> RSchema -> RSchema
schemaMultiply p (ForallP x s) = ForallP x (schemaMultiply p s)
schemaMultiply p (ForallT x s) = ForallT x (schemaMultiply p s)
schemaMultiply p (Monotype t) = Monotype $ typeMultiply p t

typeMultiply :: Potential -> RType -> RType
typeMultiply fml (ScalarT t ref pot) = ScalarT (baseTypeMultiply fml t) ref (multiplyPotentials fml pot)
typeMultiply fml t = t

baseTypeMultiply :: Potential -> BaseType Formula -> BaseType Formula
baseTypeMultiply fml (TypeVarT subs name mul) = TypeVarT subs name (multiplyPotentials mul fml)
baseTypeMultiply fml (DatatypeT name tArgs pArgs) = DatatypeT name (map (typeMultiply fml) tArgs) pArgs
baseTypeMultiply fml t = t

-- Currently only used on the argument in function types, shouldn't need more cases. Also not adding potential recursively to the basetypes.
addPotential :: RType -> Potential -> RType 
--addPotential t@(ScalarT base ref pot) f = ScalarT (addPotentialBase base f) ref (addFormulas pot f)
addPotential t@(ScalarT base ref pot) f = ScalarT base ref (sumPotentials pot f)
-- Should only be called when tBody is a scalar (hopefully)
addPotential (LetT x tDef tBody) f = LetT x tDef (addPotential tBody f)

addPotentialBase :: BaseType Formula -> Potential -> BaseType Formula 
addPotentialBase (DatatypeT x ts ps) f = DatatypeT x (fmap (`addPotential` f) ts) ps
addPotentialBase b _ = b

-- | 'removePotential' @t@ : removes all non-default potential and multiplicity annotations, used to strip constructor annotations
removePotential :: RType -> RType
removePotential (ScalarT b r _) = ScalarT (removePotentialBase b) r pzero 
removePotential (FunctionT x arg res c) = FunctionT x (removePotential arg) (removePotential res) c
removePotential (LetT x t body) = LetT x (removePotential t) (removePotential body)
removePotential t = t

removePotentialBase :: BaseType Formula -> BaseType Formula
removePotentialBase (DatatypeT x ts ps) = DatatypeT x (fmap removePotential ts) ps
--removePotentialBase (TypeVarT subs x _) = TypeVarT subs x (IntLit 1)
removePotentialBase b = b

-- Extract top-level potential from a scalar type (after performing appropriate substitution)
topPotentialOf :: RType -> Maybe Potential
topPotentialOf (ScalarT _ _ p) = Just p
topPotentialOf _               = Nothing

topPotentialFml (ScalarT _ _ (Fml f)) = Just f
topPotentialFml _                     = Nothing

{- Refinement types -}

-- | Unrefined typed
type SType = TypeSkeleton ()

-- | Refined types
type RType = TypeSkeleton Formula

-- | Unrefined schemas
type SSchema = SchemaSkeleton ()

-- | Refined schemas
type RSchema = SchemaSkeleton Formula


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
addRefinement :: TypeSkeleton Formula -> Formula -> TypeSkeleton Formula
addRefinement (ScalarT base fml pot) fml' = if isVarRefinemnt fml'
  then ScalarT base fml' pot -- the type of a polymorphic variable does not require any other refinements
  else ScalarT base (fml `andClean` fml') pot
addRefinement (LetT x tDef tBody) fml = LetT x tDef (addRefinement tBody fml)
addRefinement t (BoolLit True) = t
addRefinement AnyT _ = AnyT
addRefinement t _ = error "addRefinement: applied to function type"

-- | Conjoin refinement to the return type
addRefinementToLast t@ScalarT{} fml = addRefinement t fml
addRefinementToLast (FunctionT x tArg tRes c) fml = FunctionT x tArg (addRefinementToLast tRes fml) c
addRefinementToLast (LetT x tDef tBody) fml = LetT x tDef (addRefinementToLast tBody fml)

-- | Conjoin refinement to the return type inside a schema
addRefinementToLastSch (Monotype t) fml = Monotype $ addRefinementToLast t fml
addRefinementToLastSch (ForallT a sch) fml = ForallT a $ addRefinementToLastSch sch fml
addRefinementToLastSch (ForallP sig sch) fml = ForallP sig $ addRefinementToLastSch sch fml


-- | Apply variable substitution in all formulas inside a type
substituteInType :: (Id -> Bool) -> Substitution -> RType -> RType
substituteInType isBound subst (ScalarT baseT fml pot) = ScalarT (substituteBase subst baseT) (substitute subst fml) (liftFmlOp (substitute subst) pot)
  where
    -- TODO: does this make sense?
    substituteBase subst (TypeVarT oldSubst a m) = TypeVarT oldSubst a (liftFmlOp (substitute subst) m)
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
-- TODO: should this be max or min?
intersection isBound (ScalarT baseT fml pot) (ScalarT baseT' fml' pot') = case baseT of
  DatatypeT name tArgs pArgs -> let DatatypeT _ tArgs' pArgs' = baseT' in
                                  ScalarT (DatatypeT name (zipWith (intersection isBound) tArgs tArgs') (zipWith andClean pArgs pArgs')) (fml `andClean` fml') (liftFmlBOp fmax pot pot') 
  _ -> ScalarT baseT (fml `andClean` fml') (liftFmlBOp fmax pot pot')
intersection isBound (FunctionT x tArg tRes c) (FunctionT y tArg' tRes' c') = FunctionT x tArg (intersection isBound tRes (renameVar isBound y x tArg tRes')) (max c c')

typeFromSchema :: RSchema -> RType
typeFromSchema (Monotype t) = t
typeFromSchema (ForallT _ t) = typeFromSchema t
typeFromSchema (ForallP _ t) = typeFromSchema t

-- Move cost annotations to next arrow or to scalar argument type before applying function
shiftCost :: RType -> RType
shiftCost (FunctionT x argT resT c) = 
  if isScalarType resT
    then FunctionT x (addPotential argT (intFml c)) resT 0 
    else FunctionT x argT (addCostToArrow resT) 0
  where 
    addCostToArrow (FunctionT y a r cost) = FunctionT y a r (cost + c)


-- | Instantiate unknowns in a type
-- TODO: eventually will need to instantiate potential variables as well
typeApplySolution :: Solution -> RType -> RType
typeApplySolution sol (ScalarT (DatatypeT name tArgs pArgs) fml pot) = ScalarT (DatatypeT name (map (typeApplySolution sol) tArgs) (map (applySolution sol) pArgs)) (applySolution sol fml) pot
typeApplySolution sol (ScalarT base fml pot) = ScalarT base (applySolution sol fml) pot
typeApplySolution sol (FunctionT x tArg tRes c) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes) c
typeApplySolution sol (LetT x tDef tBody) = LetT x (typeApplySolution sol tDef) (typeApplySolution sol tBody)
typeApplySolution _ AnyT = AnyT

allRefinementsOf :: RSchema -> [Formula]
allRefinementsOf sch = allRefinementsOf' $ typeFromSchema sch

allRefinementsOf' (ScalarT _ ref _) = [ref]
allRefinementsOf' (FunctionT _ argT resT _) = allRefinementsOf' argT ++ allRefinementsOf' resT
allRefinementsOf' _ = error "allRefinementsOf called on contextual or any type"

-- Set strings: used for "fake" set type for typechecking measures
emptySetCtor = "Emptyset"
singletonCtor = "Singleton"
insertSetCtor = "Insert"
setTypeName = "DSet"
setTypeVar = "setTypeVar"
