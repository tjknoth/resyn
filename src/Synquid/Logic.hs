{-# LANGUAGE TemplateHaskell, Rank2Types, DeriveFunctor, DeriveFoldable, DeriveTraversable, TypeFamilies #-}

-- | Formulas of the refinement logic
module Synquid.Logic where

import Synquid.Util

import Data.Tuple
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Functor.Foldable (Recursive(..), Corecursive(..), Base(..))
import Data.Functor.Foldable.TH

import Control.Lens hiding (both, para)
import Control.Monad
import qualified Z3.Monad as Z3 

{- Sorts -}

-- | Sorts
data Sort = BoolS | IntS | VarS !Id | DataS !Id ![Sort] | SetS !Sort | AnyS
  deriving (Show, Eq, Ord)

isSetS (SetS _) = True
isSetS _ = False
elemSort (SetS s) = s
isData (DataS _ _) = True
isData _ = False
sortArgsOf (DataS _ sArgs) = sArgs
varSortName (VarS name) = name

sortShape BoolS    = BoolS 
sortShape IntS     = IntS 
sortShape (VarS _) = VarS ""
sortShape DataS{}  = DataS "" []
sortShape (SetS _) = SetS BoolS -- Instantiate with an arbitrary sort
sortShape AnyS     = AnyS

-- | 'typeVarsOfSort' @s@ : all type variables in @s@
typeVarsOfSort :: Sort -> Set Id
typeVarsOfSort (VarS name) = Set.singleton name
typeVarsOfSort (DataS _ sArgs) = Set.unions (map typeVarsOfSort sArgs)
typeVarsOfSort (SetS s) = typeVarsOfSort s
typeVarsOfSort _ = Set.empty

-- Mapping from type variables to sorts
type SortSubstitution = Map Id Sort

sortSubstitute :: SortSubstitution -> Sort -> Sort
sortSubstitute subst s@(VarS a) = case Map.lookup a subst of
  Just s' -> sortSubstitute subst s'
  Nothing -> s
sortSubstitute subst (DataS name args) = DataS name (map (sortSubstitute subst) args)
sortSubstitute subst (SetS el) = SetS (sortSubstitute subst el)
sortSubstitute _ s = s

distinctTypeVars = map (\i -> "A" ++ show i) [0..]

noncaptureSortSubst :: [Id] -> [Sort] -> Sort -> Sort
noncaptureSortSubst sVars sArgs s =
  let sFresh = sortSubstitute (Map.fromList $ zip sVars (map VarS distinctTypeVars)) s
  in sortSubstitute (Map.fromList $ zip distinctTypeVars sArgs) sFresh

unifySorts :: Set Id -> [Sort] -> [Sort] -> Either (Sort, Sort) SortSubstitution
unifySorts boundTvs = unifySorts' Map.empty
  where
    unifySorts' subst [] []
      = Right subst
    unifySorts' subst (x : xs) (y : ys) | x == y
      = unifySorts' subst xs ys
    unifySorts' subst (SetS x : xs) (SetS y : ys)
      = unifySorts' subst (x:xs) (y:ys)
    unifySorts' subst (DataS name args : xs) (DataS name' args' :ys)
      = if name == name'
          then unifySorts' subst (args ++ xs) (args' ++ ys)
          else Left (DataS name [], DataS name' [])
    unifySorts' subst (AnyS : xs) (_ : ys) = unifySorts' subst xs ys
    unifySorts' subst (_ : xs) (AnyS : ys) = unifySorts' subst xs ys
    unifySorts' subst (VarS x : xs) (y : ys)
      | not (Set.member x boundTvs)
      = case Map.lookup x subst of
            Just s -> unifySorts' subst (s : xs) (y : ys)
            Nothing -> if x `Set.member` typeVarsOfSort y
              then Left (VarS x, y)
              else unifySorts' (Map.insert x y subst) xs ys
    unifySorts' subst (x : xs) (VarS y : ys)
      | not (Set.member y boundTvs)
      = unifySorts' subst (VarS y : ys) (x:xs)
    unifySorts' _ (x: _) (y: _)
      = Left (x, y)

-- | Constraints generated during formula resolution
data SortConstraint = SameSort Sort Sort  -- Two sorts must be the same
  | IsOrd Sort                            -- Sort must have comparisons

-- | Predicate signature: name and argument sorts
data PredSig = PredSig {
  predSigName :: !Id,
  predSigArgSorts :: ![Sort],
  predSigResSort :: !Sort
} deriving (Show, Eq, Ord)

{- Formulas of the refinement logic -}

-- | Unary operators
data UnOp = Neg | Not
  deriving (Show, Eq, Ord)

-- | Binary operators
data BinOp =
    Times | Plus | Minus |          -- ^ Int -> Int -> Int
    Eq | Neq |                      -- ^ a -> a -> Bool
    Lt | Le | Gt | Ge |             -- ^ Int -> Int -> Bool
    And | Or | Implies | Iff |      -- ^ Bool -> Bool -> Bool
    Union | Intersect | Diff |      -- ^ Set -> Set -> Set
    Member | Subset                 -- ^ Int/Set -> Set -> Bool
  deriving (Show, Eq, Ord)

-- | Variable substitution
type Substitution = Map Id Formula

-- | Formulas of the refinement logic
data Formula =
  BoolLit !Bool |                      -- ^ Boolean literal
  IntLit !Int |                    -- ^ Integer literal
  SetLit !Sort ![Formula] |            -- ^ Set literal ([1, 2, 3])
  Var !Sort !Id |                      -- ^ Input variable (universally quantified first-order variable)
  Unknown !Substitution !Id |          -- ^ Predicate unknown (with a pending substitution)
  Unary !UnOp !Formula |               -- ^ Unary expression
  Binary !BinOp !Formula !Formula |    -- ^ Binary expression
  Ite !Formula !Formula !Formula |     -- ^ If-then-else expression
  Pred !Sort !Id ![Formula] |          -- ^ Logic function application
  Cons !Sort !Id ![Formula] |          -- ^ Constructor application
  All !Formula !Formula |              -- ^ Universal quantification
  Z3Lit !Sort !Z3.AST !String          -- ^ Z3 AST literal (only used to solve resource constraints), and its string version
  deriving (Show, Eq, Ord)

makeBaseFunctor ''Formula

embedLit :: String -> FormulaF a -> Formula
embedLit _ (BoolLitF b)     = BoolLit b
embedLit _ (IntLitF b)      = IntLit b
embedLit _ (Z3LitF s x str) = Z3Lit s x str
embedLit err _              = error $ unwords ["embedLit: non-literal base functor in context", err]


dontCare = "_"
valueVarName = "_v" --need to modify for dependent polys
unknownName (Unknown _ name) = name
varName (Var _ name) = name
varType (Var t _) = t

maybeUnknownName (Unknown _ name) = Just name
maybeUnknownName _                = Nothing

isVar (Var _ _) = True
isVar _ = False
isCons (Cons _ _ _) = True
isCons _ = False

ftrue :: Formula
ftrue = BoolLit True
ffalse = BoolLit False
boolVar = Var BoolS
valBool = boolVar valueVarName
intVar = Var IntS
valInt = intVar valueVarName
vartVar n = Var (VarS n)
valVart n = vartVar n valueVarName
setVar s = Var (SetS (VarS s))
valSet s = setVar s valueVarName
fneg = Unary Neg
fnot = Unary Not
fzero = IntLit 0
fone = IntLit 1
(|*|) = Binary Times
(|+|) = Binary Plus
(|-|) = Binary Minus
(|=|) = Binary Eq
(|/=|) = Binary Neq
(|<|) = Binary Lt
(|<=|) = Binary Le
(|>|) = Binary Gt
(|>=|) = Binary Ge
(|&|) = Binary And
(|||) = Binary Or
(|=>|) = Binary Implies
(|<=>|) = Binary Iff

-- top/bot potential annotations
ptop = IntLit 0
pbot = IntLit 9999 -- lol


andClean :: Formula -> Formula -> Formula
andClean l r = if l == ftrue then r else (if r == ftrue then l else (if l == ffalse || r == ffalse then ffalse else l |&| r))
orClean l r = if l == ffalse then r else (if r == ffalse then l else (if l == ftrue || r == ftrue then ftrue else l ||| r))
conjunction :: Foldable t => t Formula -> Formula
conjunction = foldl andClean ftrue
disjunction :: Foldable t => t Formula -> Formula
disjunction = foldl orClean ffalse

(/+/) = Binary Union
(/*/) = Binary Intersect
(/-/) = Binary Diff
fin = Binary Member
(/<=/) = Binary Subset

infixl 9 |*|
infixl 8 |+|, |-|, /+/, /-/, /*/
infixl 7 |=|, |/=|, |<|, |<=|, |>|, |>=|, /<=/
infixl 6 |&|, |||
infixr 5 |=>|
infix 4 |<=>|

fmax f g = Ite (f |>=| g) f g
fmin f g = Ite (f |<=| g) f g

varsOf :: Formula -> Set Formula 
varsOf = 
  let combine = Set.unions . map snd 
      vSetRAlg (VarF s x)      = Set.singleton $ Var s x     
      vSetRAlg (SetLitF _ xs)  = combine xs 
      vSetRAlg (UnaryF _ x)    = snd x
      vSetRAlg (BinaryF _ x y) = snd x `Set.union` snd y
      vSetRAlg (IteF x y z)    = combine [x, y, z] 
      vSetRAlg (PredF _ _ xs)  = combine xs 
      vSetRAlg (ConsF _ _ xs)  = combine xs 
      vSetRAlg (AllF x e)      = Set.delete (fst x) (snd e)
      vSetRAlg f               = Set.empty
  in para vSetRAlg 


unknownsOf :: Formula -> Set Formula 
unknownsOf = 
  let uSetAlg (UnknownF s x)  = Set.singleton $ Unknown s x
      uSetAlg (SetLitF _ xs)  = Set.unions xs 
      uSetAlg (UnaryF _ x)    = x
      uSetAlg (BinaryF _ x y) = x `Set.union` y
      uSetAlg (IteF x y z)    = Set.unions [x, y, z] 
      uSetAlg (PredF _ _ xs)  = Set.unions xs 
      uSetAlg (ConsF _ _ xs)  = Set.unions xs 
      uSetAlg (AllF _ e)      = e 
      uSetAlg f               = Set.empty
  in cata uSetAlg


-- | 'posNegUnknowns' @fml@: sets of positive and negative predicate unknowns in @fml@
posNegUnknowns :: Formula -> (Set Id, Set Id)
posNegUnknowns (Unknown _ u) = (Set.singleton u, Set.empty)
posNegUnknowns (Unary Not e) = swap $ posNegUnknowns e
posNegUnknowns (Binary Implies e1 e2) = both2 Set.union (swap $ posNegUnknowns e1) (posNegUnknowns e2)
posNegUnknowns (Binary Iff e1 e2) = both2 Set.union (posNegUnknowns $ e1 |=>| e2) (posNegUnknowns $ e2 |=>| e1)
posNegUnknowns (Binary _ e1 e2) = both2 Set.union (posNegUnknowns e1) (posNegUnknowns e2)
posNegUnknowns (Ite e e1 e2) = both2 Set.union (posNegUnknowns $ e |=>| e1) (posNegUnknowns $ fnot e |=>| e2)
posNegUnknowns _ = (Set.empty, Set.empty)

posUnknowns = fst . posNegUnknowns
negUnknowns = snd . posNegUnknowns

posNegPreds :: Formula -> (Set Id, Set Id)
posNegPreds (Pred BoolS p _) = (Set.singleton p, Set.empty)
posNegPreds (Unary Not e) = swap $ posNegPreds e
posNegPreds (Binary Implies e1 e2) = both2 Set.union (swap $ posNegPreds e1) (posNegPreds e2)
posNegPreds (Binary Iff e1 e2) = both2 Set.union (posNegPreds $ e1 |=>| e2) (posNegPreds $ e2 |=>| e1)
posNegPreds (Binary _ e1 e2) = both2 Set.union (posNegPreds e1) (posNegPreds e2)
posNegPreds (Ite e e1 e2) = both2 Set.union (posNegPreds $ e |=>| e1) (posNegPreds $ fnot e |=>| e2)
posNegPreds _ = (Set.empty, Set.empty)

posPreds = fst . posNegPreds
negPreds = snd . posNegPreds

predsOf :: Formula -> Set String
predsOf = 
  let pSetAlg (PredF _ p xs)  = Set.insert p $ Set.unions xs  
      pSetAlg (SetLitF _ xs)  = Set.unions xs 
      pSetAlg (UnaryF _ x)    = x
      pSetAlg (BinaryF _ x y) = x `Set.union` y
      pSetAlg (IteF x y z)    = Set.unions [x, y, z] 
      pSetAlg (AllF _ e)      = e 
      pSetAlg f               = Set.empty
  in cata pSetAlg 

hasPred :: Formula -> Bool 
hasPred = 
  let pAlg PredF{}           = True
      pAlg (SetLitF _ xs)    = or xs 
      pAlg (UnaryF _ e)      = e 
      pAlg (BinaryF _ e1 e2) = e1 || e2
      pAlg (IteF e1 e2 e3)   = e1 || e2 || e3
      pAlg (AllF _ e)        = e
      pAlg _                 = False
  in cata pAlg

hasPredITE :: Formula -> Bool 
hasPredITE = 
  let pAlg PredF{}           = True
      pAlg (SetLitF _ xs)    = or xs 
      pAlg (UnaryF _ e)      = e 
      pAlg (BinaryF _ e1 e2) = e1 || e2
      pAlg (IteF e1 e2 e3)   = e2 || e3
      pAlg (AllF _ e)        = e
      pAlg _                 = False
  in cata pAlg

hasVar :: Formula -> Bool
hasVar = 
  let vAlg VarF{}            = True
      vAlg PredF{}           = False
      vAlg (SetLitF _ xs)    = or xs 
      vAlg (UnaryF _ e)      = e 
      vAlg (BinaryF _ e1 e2) = e1 || e2
      vAlg (IteF e1 e2 e3)   = e1 || e2 || e3
      vAlg (AllF _ e)        = e
      vAlg _                 = False
  in cata vAlg

hasVarITE :: Formula -> Bool
hasVarITE = 
  let vAlg VarF{}            = True
      vAlg PredF{}           = False
      vAlg (SetLitF _ xs)    = or xs 
      vAlg (UnaryF _ e)      = e 
      vAlg (BinaryF _ e1 e2) = e1 || e2
      vAlg (IteF e1 e2 e3)   = e2 || e3
      vAlg (AllF _ e)        = e
      vAlg _                 = False
  in cata vAlg

isNumeric :: Formula -> Bool
isNumeric = 
  let vAlg VarF{}            = True
      vAlg (PredF IntS _ _)  = True
      vAlg (PredF _ _ _)     = False
      vAlg (SetLitF _ xs)    = and xs 
      vAlg (UnaryF _ e)      = e 
      vAlg (BinaryF _ e1 e2) = e1 && e2
      vAlg (IteF e1 e2 e3)   = e1 && e2 && e3
      vAlg (AllF _ e)        = e
      vAlg _                 = True
  in cata vAlg


-- | 'leftHandSide' @fml@ : left-hand side of a binary expression
leftHandSide (Binary _ l _) = l
-- | 'rightHandSide' @fml@ : right-hand side of a binary expression
rightHandSide (Binary _ _ r) = r

conjunctsOf (Binary And l r) = conjunctsOf l `Set.union` conjunctsOf r
conjunctsOf f = Set.singleton f

-- | Base type of a term in the refinement logic
sortOf :: Formula -> Sort
sortOf (BoolLit _)                               = BoolS
sortOf (IntLit _)                                = IntS
sortOf (SetLit s _)                              = SetS s
sortOf (Var s _ )                                = s
sortOf (Unknown _ _)                             = BoolS
sortOf (Unary op _)
  | op == Neg                                    = IntS
  | otherwise                                    = BoolS
sortOf (Binary op e1 _)
  | op == Times || op == Plus || op == Minus     = IntS
  | op == Union || op == Intersect || op == Diff = sortOf e1
  | otherwise                                    = BoolS
sortOf (Ite _ e1 _)                              = sortOf e1
sortOf (Pred s _ _)                              = s
sortOf (Cons s _ _)                              = s
sortOf (All _ _)                                 = BoolS
sortOf (Z3Lit s _ _)                             = s

isExecutable :: Formula -> Bool
isExecutable = 
  let exAlg SetLitF{}       = False
      exAlg IteF{}          = False
      exAlg PredF{}         = False
      exAlg AllF{}          = False
      exAlg (UnaryF _ x)    = x
      exAlg (BinaryF _ x y) = x && y
      exAlg _               = True
  in cata exAlg

-- Removes non-resource predicates from a large conjunction
removePreds :: [String] -> Formula -> Formula
removePreds valid (Binary And f g) = Binary And (removePreds valid f) (removePreds valid g)
removePreds valid f = if hasInvalid valid f then ftrue else f

hasInvalid :: [String] -> Formula -> Bool
hasInvalid valid = 
  let alg (PredF _ x _)   = not (x `elem` valid)
      alg (UnaryF _ f)    = f 
      alg (BinaryF _ f g) = f || g
      alg (IteF f g h)    = f || g || h
      alg _              = False
  in  cata alg

-- | 'substitute' @subst fml@: Replace first-order variables in @fml@ according to @subst@
substitute :: Substitution -> Formula -> Formula
substitute subst = 
  let sAlg (SetLitF s xs)   = SetLit s $ map snd xs
      sAlg (VarF s name)    = 
        case Map.lookup name subst of 
          Just f           -> f 
          Nothing          -> Var s name
      sAlg (UnknownF s x)   = Unknown (s `composeSubstitutions` subst) x
      sAlg (UnaryF op x)    = Unary op (snd x)
      sAlg (BinaryF op x y) = Binary op (snd x) (snd y)
      sAlg (IteF x y z)     = Ite (snd x) (snd y) (snd z)
      sAlg (PredF s x xs)   = Pred s x $ map snd xs
      sAlg (ConsF s x xs)   = Cons s x $ map snd xs
      sAlg (AllF (v, v') e) = 
        case v of 
          (Var s x) -> 
            if x `Map.member` subst 
              then error $ unwords ["Scoped variable clashes with substitution variable", x]
              else All v (snd e) 
          _     -> All v' (snd e)
      sAlg f = embedLit "substitute" f
  in para sAlg

-- | Compose substitutions
composeSubstitutions old new =
  let new' = removeId new
  in Map.map (substitute new') old `Map.union` new'
  where
    -- | Remove identity substitutions
    removeId = Map.filterWithKey (\x fml -> not $ isVar fml && varName fml == x)

deBrujns = map (\i -> dontCare ++ show i) [0..]

sortSubstituteFml :: SortSubstitution -> Formula -> Formula
sortSubstituteFml subst = 
  let sub = sortSubstitute subst 
      sAlg (SetLitF s xs)    = SetLit (sub s) xs
      sAlg (VarF s name)     = Var (sub s) name
      sAlg (UnknownF s name) = Unknown (fmap (sortSubstituteFml subst) s) name 
      sAlg (PredF s name es) = Pred (sub s) name es
      sAlg (ConsF s name es) = Cons (sub s) name es 
      sAlg base              = embed base
  in cata sAlg


noncaptureSortSubstFml :: [Id] -> [Sort] -> Formula -> Formula
noncaptureSortSubstFml sVars sArgs fml =
  let fmlFresh = sortSubstituteFml (Map.fromList $ zip sVars (map VarS distinctTypeVars)) fml
  in sortSubstituteFml (Map.fromList $ zip distinctTypeVars sArgs) fmlFresh


substitutePredicate :: Substitution -> Formula -> Formula
substitutePredicate subs = 
  let sAlg (PredF s name args) = 
        case Map.lookup name subs of 
          Nothing -> Pred s name args
          Just val -> substitute (Map.fromList (zip deBrujns args)) (substitutePredicate subs val)
      sAlg f                   = embed f 
  in cata sAlg

-- | Negation normal form of a formula:
-- no negation above boolean connectives, no boolean connectives except @&&@ and @||@
negationNF :: Formula -> Formula
negationNF fml = case fml of
  Unary Not e -> case e of
    Unary Not e' -> negationNF e'
    Binary And e1 e2 -> negationNF (fnot e1) ||| negationNF (fnot e2)
    Binary Or e1 e2 -> negationNF (fnot e1) |&| negationNF (fnot e2)
    Binary Implies e1 e2 -> negationNF e1 |&| negationNF (fnot e2)
    Binary Iff e1 e2 -> (negationNF e1 |&| negationNF (fnot e2)) ||| (negationNF (fnot e1) |&| negationNF e2)
    _ -> fml
  Binary Implies e1 e2 -> negationNF (fnot e1) ||| negationNF e2
  Binary Iff e1 e2 -> (negationNF e1 |&| negationNF e2) ||| (negationNF (fnot e1) |&| negationNF (fnot e2))
  Binary op e1 e2
    | op == And || op == Or -> Binary op (negationNF e1) (negationNF e2)
    | otherwise -> fml
  Ite cond e1 e2 -> (negationNF cond |&| negationNF e1) ||| (negationNF (fnot cond) |&| negationNF e2)
  _ -> fml

-- | Disjunctive normal form for unknowns (known predicates treated as atoms)
uDNF :: Formula -> [Formula]
uDNF = dnf' . negationNF
  where
    dnf' e@(Binary Or e1 e2) = if (Set.null $ unknownsOf e1) && (Set.null $ unknownsOf e2)
                                then return e
                                else dnf' e1 ++ dnf' e2
    dnf' (Binary And e1 e2) = do
                                lClause <- dnf' e1
                                rClause <- dnf' e2
                                return $ lClause |&| rClause
    dnf' fml = [fml]

atomsOf fml = atomsOf' (negationNF fml)
  where
    atomsOf' (Binary And l r) = atomsOf' l `Set.union` atomsOf' r
    -- atomsOf' fml@(Binary Or l r) = Set.insert fml (atomsOf' l `Set.union` atomsOf' r)
    atomsOf' (Binary Or l r) = atomsOf' l `Set.union` atomsOf' r
    atomsOf' fml = Set.singleton fml

splitByPredicate :: Set Id -> Formula -> [Formula] -> Maybe (Map Id (Set Formula))
splitByPredicate preds arg fmls = foldM (\m fml -> checkFml fml m fml) Map.empty fmls
  where
    checkFml _ _ fml | fml == arg   = Nothing
    checkFml whole m fml = case fml of
      Pred _ name args ->
        if name `Set.member` preds && length args == 1 && head args == arg
          then return $ Map.insertWith Set.union name (Set.singleton whole) m
          else foldM (checkFml whole) m args
      SetLit _ args -> foldM (checkFml whole) m args
      Unary _ f -> checkFml whole m f
      Binary _ l r -> foldM (checkFml whole) m [l, r]
      Ite c t e -> foldM (checkFml whole) m [c, t, e]
      Cons _ _ args -> foldM (checkFml whole) m args
      _ -> return m


{- Qualifiers -}

-- | Search space for valuations of a single unknown
data QSpace = QSpace {
    _qualifiers :: ![Formula],         -- ^ Qualifiers
    _maxCount :: !Int                  -- ^ Maximum number of qualifiers in a valuation
  } deriving (Show, Eq, Ord)

makeLenses ''QSpace

emptyQSpace = QSpace [] 0

toSpace mbN quals = let quals' = nub quals in
  case mbN of
    Nothing -> QSpace quals' (length quals')
    Just n -> QSpace quals' n

-- | Mapping from unknowns to their search spaces
type QMap = Map Id QSpace

-- | 'lookupQuals' @qmap g u@: get @g@ component of the search space for unknown @u@ in @qmap@
lookupQuals :: QMap -> Getter QSpace a -> Formula -> a
lookupQuals qmap g (Unknown _ u) = case Map.lookup u qmap of
  Just qs -> view g qs
  Nothing -> error $ unwords ["lookupQuals: missing qualifiers for unknown", u]

lookupQualsSubst :: QMap -> Formula -> [Formula]
lookupQualsSubst qmap u@(Unknown s _) = concatMap go $ map (substitute s) (lookupQuals qmap qualifiers u)
  where
    go u@(Unknown _ _) = lookupQualsSubst qmap u
    go fml = [fml]

type ExtractAssumptions = Formula -> Set Formula

{- Solutions -}

-- | Valuation of a predicate unknown as a set of qualifiers
type Valuation = Set Formula

-- | Mapping from predicate unknowns to their valuations
type Solution = Map Id Valuation

-- | 'topSolution' @qmap@ : top of the solution lattice (maps every unknown in the domain of @qmap@ to the empty set of qualifiers)
topSolution :: QMap -> Solution
topSolution qmap = constMap (Map.keysSet qmap) Set.empty

-- | 'botSolution' @qmap@ : bottom of the solution lattice (maps every unknown in the domain of @qmap@ to all its qualifiers)
botSolution :: QMap -> Solution
botSolution qmap = Map.map (\(QSpace quals _) -> Set.fromList quals) qmap

-- | 'valuation' @sol u@ : valuation of @u@ in @sol@
valuation :: Solution -> Formula -> Valuation 
valuation sol (Unknown s u) = case Map.lookup u sol of
  Just quals -> Set.map (substitute s) quals
  Nothing -> error $ unwords ["valuation: no value for unknown", u]

-- | 'applySolution' @sol fml@ : Substitute solutions from sol for all predicate variables in fml
applySolution :: Solution -> Formula -> Formula
applySolution sol = 
  let solAlg (UnknownF s name) = 
        case Map.lookup name sol of 
          Just qs -> substitute s $ conjunction qs
          Nothing -> Unknown s name
      solAlg base = embed base
  in cata solAlg

-- | 'merge' @sol sol'@ : element-wise conjunction of @sol@ and @sol'@
merge :: Solution -> Solution -> Solution
merge sol sol' = Map.unionWith Set.union sol sol'

{- Solution Candidates -}

-- | Solution candidate
data Candidate = Candidate {
    solution :: !Solution,
    validConstraints :: !(Set Formula),
    invalidConstraints :: !(Set Formula),
    label :: !String
  } deriving (Show)

initialCandidate = Candidate Map.empty Set.empty Set.empty "0"

instance Eq Candidate where
  (==) c1 c2 = Map.filter (not . Set.null) (solution c1) == Map.filter (not . Set.null) (solution c2) &&
               validConstraints c1 == validConstraints c2 &&
               invalidConstraints c1 == invalidConstraints c2

instance Ord Candidate where
  (<=) c1 c2 = Map.filter (not . Set.null) (solution c1) <= Map.filter (not . Set.null) (solution c2) &&
               validConstraints c1 <= validConstraints c2 &&
               invalidConstraints c1 <= invalidConstraints c2

---------------------------------------
---------------------------------------
-- Utilities and potential-related code
---------------------------------------
---------------------------------------

negateFml :: Formula -> Formula
negateFml x@IntLit{}        = Unary Neg x
negateFml x@Var{}           = Unary Neg x
negateFml (Ite g t f)       = Ite g (negateFml t) (negateFml f)
negateFml (Binary Plus f g) = Binary Plus (negateFml f) (negateFml g)
negateFml f                 = error $ "negateFml: Unexpected expression " ++ show f

-- 'transformFml' @transform f@ : apply some transformation @transform@ to each 
--    node in the Formula AST
transformFml :: (Formula -> Formula) -> Formula -> Formula 
transformFml transform = cata (transform . embed)
  

isUnknownForm :: Formula -> Bool
isUnknownForm (Unknown _ _) = True
isUnknownForm _             = False

-- | 'simpleFormulaBOp' @op isId f g@ : return @f@ `@op@` @g@, unless either @f@ or @g@ is an identity element under @op@, in which case we simplify
simpleFormulaBOp :: (Formula -> Formula -> Formula) -> (Formula -> Bool) -> Formula -> Formula -> Formula 
simpleFormulaBOp op isId f g = case (isId f, isId g) of 
  (True, _) -> g
  (_, True) -> f
  _         -> f `op` g

-- Simplify multiplication when multiplying by zero (again for readability)
simpleMultiply :: Formula -> Formula -> Formula 
simpleMultiply f g = 
  if isZero f || isZero g 
    then IntLit 0
    else f |*| g

isZero (IntLit 0) = True 
isZero _          = False

multiplyFormulas = simpleFormulaBOp simpleMultiply isMultiplicativeId
addFormulas = simpleFormulaBOp (|+|) isAdditiveId
subtractFormulas = simpleFormulaBOp (|-|) isAdditiveId
sumFormulas :: Foldable t => t Formula -> Formula
sumFormulas = foldl addFormulas fzero

isMultiplicativeId (IntLit 1) = True
isMultiplicativeId _          = False

isAdditiveId (IntLit 0) = True 
isAdditiveId _          = False

fmlGe (IntLit f) (IntLit g) = f >= g
fmlGe _ _ = False

