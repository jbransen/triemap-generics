-- Section 4 of the paper

{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- this is not nice
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module TrieMap2 where

import GHC.Generics
import GHC.TypeLits

import Data.Kind ( Type )
import Data.Map ( Map )
import qualified Data.Map as Map

-- De Bruijn indexing from the paper

type DBNum = Int
data DBEnv = DBE {dbe_next :: DBNum, dbe_env :: Map String DBNum}

emptyDBE :: DBEnv
emptyDBE = DBE {dbe_next = 1, dbe_env = Map.empty }

extendDBE :: String -> DBEnv -> DBEnv
extendDBE v (DBE {dbe_next = n, dbe_env = dbe }) = DBE {dbe_next = n + 1, dbe_env = Map.insert v n dbe }

lookupDBE :: String -> DBEnv -> Maybe DBNum
lookupDBE v (DBE {dbe_env = dbe }) = Map.lookup v dbe

-- The generic instances

type TF v = Maybe v -> Maybe v

-- | The HasTrieMap' class defines functionality over the generic representation of data types
--   The constructor names of the binder and variable cases are passed on the type-level
--   to distinguish between them in implementation.
class HasTrieMap' (binder :: Maybe Symbol) (var :: Maybe Symbol) (f :: Type -> Type) where
  data TrieMap' binder var f :: Type -> Type

  emptyTM' :: TrieMap' binder var f v
  alterTM' :: DBEnv -> f x ->  TF v -> TrieMap' binder var f v -> TrieMap' binder var f v
  lookupTM' :: DBEnv -> f x -> TrieMap' binder var f v -> Maybe v
  foldTM' :: (v -> r -> r) -> r -> TrieMap' binder var f v -> r
  unionWithTM' :: (v -> v -> v) -> TrieMap' binder var f v -> TrieMap' binder var f v -> TrieMap' binder var f v

instance HasTrieMap' binder var f => HasTrieMap' binder var (M1 D meta f) where
  data TrieMap' binder var (M1 D meta f) v = Empty | NonEmpty (TrieMap' binder var f v)
  emptyTM' = Empty
  alterTM' env (M1 v) f Empty = case f Nothing of
    Nothing -> Empty
    Just _  -> NonEmpty (alterTM' env v f emptyTM')
  alterTM' env (M1 v) f (NonEmpty tm) = NonEmpty (alterTM' env v f tm)
  lookupTM' _ _ Empty = Nothing
  lookupTM' env (M1 v) (NonEmpty tm) = lookupTM' env v tm
  foldTM' _ z Empty = z
  foldTM' k z (NonEmpty tm) = foldTM' k z tm
  unionWithTM' _ Empty r = r
  unionWithTM' _ r Empty = r
  unionWithTM' f (NonEmpty tm1) (NonEmpty tm2) = NonEmpty (unionWithTM' f tm1 tm2)

-- | Kind to distinguish, on the type level, between different types of constructors.
data ConstructorTp = CBinder | CVar | CRegular

-- | Type-level function to find out what kind of constructor the constructor with a given name is.
type family IsConstructorTp (binder :: Maybe Symbol) (var :: Maybe Symbol) (cnm :: Symbol) :: ConstructorTp where
  IsConstructorTp (Just b) _ b = 'CBinder
  IsConstructorTp _ (Just v) v = 'CVar
  IsConstructorTp _ _ _ = 'CRegular

-- | Special class for constructors, to distinguish between different types of constructors
class HasTrieMapC' (binder :: Maybe Symbol) (var :: Maybe Symbol) (ctp :: ConstructorTp) (f :: Type -> Type) where
  data TrieMapC' binder var ctp f :: Type -> Type
  emptyTMC' :: TrieMapC' binder var ctp f v
  alterTMC' :: DBEnv -> f x ->  TF v -> TrieMapC' binder var ctp f v -> TrieMapC' binder var ctp f v
  lookupTMC' :: DBEnv -> f x -> TrieMapC' binder var ctp f v -> Maybe v
  foldTMC' :: (v -> r -> r) -> r -> TrieMapC' binder var ctp f v -> r
  unionWithTMC' :: (v -> v -> v) -> TrieMapC' binder var ctp f v -> TrieMapC' binder var ctp f v -> TrieMapC' binder var ctp f v

-- | Regular constructors
instance HasTrieMap' binder var f => HasTrieMapC' binder var 'CRegular f where
  data TrieMapC' binder var 'CRegular f v = TMCRegular (TrieMap' binder var f v)
  emptyTMC' = TMCRegular emptyTM'
  alterTMC' env v f (TMCRegular tm) = TMCRegular (alterTM' env v f tm)
  lookupTMC' env v (TMCRegular tm) = lookupTM' env v tm
  foldTMC' k z (TMCRegular tm) = foldTM' k z tm
  unionWithTMC' f (TMCRegular tm1) (TMCRegular tm2) = TMCRegular (unionWithTM' f tm1 tm2)

-- | Binder, the constructor must have a String as first argument
instance HasTrieMap' binder var f => HasTrieMapC' binder var 'CBinder (S1 meta (Rec0 String) :*: f) where
  data TrieMapC' binder var 'CBinder (S1 meta (Rec0 String) :*: f) v = TMCBinder (TrieMap' binder var f v)
  emptyTMC' = TMCBinder emptyTM'
  alterTMC' env (M1 (K1 v) :*: e) f (TMCBinder tm) = TMCBinder (alterTM' (extendDBE v env) e f tm)
  lookupTMC' env (M1 (K1 v) :*: e) (TMCBinder tm) = lookupTM' (extendDBE v env) e tm
  foldTMC' k z (TMCBinder tm) = foldTM' k z tm
  unionWithTMC' f (TMCBinder tm1) (TMCBinder tm2) = TMCBinder (unionWithTM' f tm1 tm2)

-- | Variables, the constructor must have a String as only argument
-- We distinguish between bound and unbound variables, and recurse accordingly
-- (note that we could also tie the knot here and use something like Map, but why not use our own
--  triemap here as well for string and int)
instance (HasTrieMap String, HasTrieMap DBNum) => HasTrieMapC' binder var 'CVar (S1 meta (Rec0 String)) where
  data TrieMapC' binder var 'CVar (S1 meta (Rec0 String)) v = TMCVar (TrieMap String v) (TrieMap DBNum v)
  emptyTMC' = TMCVar (emptyTM @String) (emptyTM @DBNum)
  alterTMC' env (M1 (K1 v)) f (TMCVar ms mv) = case v `lookupDBE` env of
    Nothing -> TMCVar (alterTM env v f ms) mv
    Just v' -> TMCVar ms (alterTM env v' f mv)
  lookupTMC' env (M1 (K1 v)) (TMCVar ms mv) = case v `lookupDBE` env of
    Nothing -> lookupTM env v ms
    Just v' -> lookupTM env v' mv
  foldTMC' k z (TMCVar tms tmv) = foldTM @String k (foldTM @DBNum k z tmv) tms
  unionWithTMC' f (TMCVar tms1 tmv1) (TMCVar tms2 tmv2) = TMCVar (unionWithTM @String f tms1 tms2) (unionWithTM @DBNum f tmv1 tmv2)

-- | Lift the constructor cases to an instance for all constructors, based on the metadata with the constructor name
instance (HasTrieMapC' binder var (IsConstructorTp binder var cnm) f) => HasTrieMap' binder var (M1 C ('MetaCons cnm p b) f) where
  data TrieMap' binder var (M1 C ('MetaCons cnm p b) f) v = TMC (TrieMapC' binder var (IsConstructorTp binder var cnm) f v)
  emptyTM' = TMC emptyTMC'
  alterTM' env (M1 v) f (TMC tm) = TMC (alterTMC' env v f tm)
  lookupTM' env (M1 v) (TMC tm) = lookupTMC' env v tm
  foldTM' k z (TMC tm) = foldTMC' k z tm
  unionWithTM' f (TMC tm1) (TMC tm2) = TMC (unionWithTMC' f tm1 tm2)

instance HasTrieMap' binder var f => HasTrieMap' binder var (M1 S meta f) where
  data TrieMap' binder var (M1 S meta f) v = TMS (TrieMap' binder var f v)
  emptyTM' = TMS emptyTM'
  alterTM' env (M1 v) f (TMS tm) = TMS (alterTM' env v f tm)
  lookupTM' env (M1 v) (TMS tm) = lookupTM' env v tm
  foldTM' k z (TMS tm) = foldTM' k z tm
  unionWithTM' f (TMS tm1) (TMS tm2) = TMS (unionWithTM' f tm1 tm2)

instance (HasTrieMap' binder var f, HasTrieMap' binder var g) => HasTrieMap' binder var (f :+: g) where
  data TrieMap' binder var (f :+: g) v = TMPair (TrieMap' binder var f v) (TrieMap' binder var g v)
  emptyTM' = TMPair emptyTM' emptyTM'
  alterTM' env (L1 v) f (TMPair tl tr) = TMPair (alterTM' env v f tl) tr
  alterTM' env (R1 v) f (TMPair tl tr) = TMPair tl (alterTM' env v f tr)
  lookupTM' env (L1 v) (TMPair tm _) = lookupTM' env v tm
  lookupTM' env (R1 v) (TMPair _ tm) = lookupTM' env v tm
  foldTM' k z (TMPair tm1 tm2) = foldTM' k (foldTM' k z tm2) tm1
  unionWithTM' f (TMPair tm1a tm1b) (TMPair tm2a tm2b) = TMPair (unionWithTM' f tm1a tm2a) (unionWithTM' f tm1b tm2b)

instance (HasTrieMap' binder var f, HasTrieMap' binder var g) => HasTrieMap' binder var (f :*: g) where
  data TrieMap' binder var (f :*: g) v = TMProd (TrieMap' binder var f (TrieMap' binder var g v))
  emptyTM' = TMProd emptyTM'
  alterTM' env (v1 :*: v2) f (TMProd tm) = TMProd (alterTM' env v1 (liftTF (alterTM' env v2 f)) tm)
  lookupTM' env (v1 :*: v2) (TMProd tm) = lookupTM' env v1 tm >>= lookupTM' env v2
  foldTM' k z (TMProd tm) = foldTM' (flip (foldTM' k)) z tm
  unionWithTM' f (TMProd tm1) (TMProd tm2) = TMProd (unionWithTM' (unionWithTM' f) tm1 tm2)

instance HasTrieMap a => HasTrieMap' binder var (Rec0 a) where
  data TrieMap' binder var (Rec0 a) v = TMRec (TrieMap a v)
  emptyTM' :: forall v. TrieMap' binder var (Rec0 a) v
  emptyTM' = TMRec (emptyTM @a @v)
  alterTM' env (K1 v) f (TMRec tm) = TMRec (alterTM env v f tm)
  lookupTM' env (K1 v) (TMRec tm) = lookupTM env v tm
  foldTM' k z (TMRec tm) = foldTM @a k z tm
  unionWithTM' f (TMRec tm1) (TMRec tm2) = TMRec (unionWithTM @a f tm1 tm2)

instance HasTrieMap' binder var U1 where
  data TrieMap' binder var U1 v = TMU1 (Maybe v)
  emptyTM' = TMU1 Nothing
  alterTM' _ U1 f (TMU1 mbv) = TMU1 (f mbv)
  lookupTM' _ U1 (TMU1 mbv) = mbv
  foldTM' k z (TMU1 mbv) = maybe z (`k` z) mbv
  unionWithTM' _ (TMU1 Nothing) (TMU1 Nothing) = TMU1 Nothing
  unionWithTM' _ (TMU1 Nothing) (TMU1 mbv2) = TMU1 mbv2
  unionWithTM' _ (TMU1 mbv1) (TMU1 Nothing) = TMU1 mbv1
  unionWithTM' f (TMU1 (Just v1)) (TMU1 (Just v2)) = TMU1 (Just $ f v1 v2)

liftTF :: HasTrieMap' binder var f
  => (TrieMap' binder var f v -> TrieMap' binder var f v)
  -> Maybe (TrieMap' binder var f v) -> Maybe (TrieMap' binder var f v)
liftTF f Nothing = Just (f emptyTM')
liftTF f (Just m) = Just (f m)


-- * Non-generic version of the triemap class, this uses Generic instances as defaults

class HasTrieMap a where
  type TrieMap a v :: Type
  type TrieMap a v = TrieMap' (Binder a) (Var a) (Rep a) v

  type Binder a :: Maybe Symbol
  type Binder a = Nothing -- no binder by default

  type Var a :: Maybe Symbol
  type Var a = Nothing -- no var by default

  emptyTM :: TrieMap a v
  default emptyTM :: (TrieMap a v ~ TrieMap' (Binder a) (Var a) (Rep a) v, HasTrieMap' (Binder a) (Var a) (Rep a))
                  => TrieMap a v
  emptyTM = emptyTM'

  alterTM :: DBEnv -> a -> (Maybe v -> Maybe v) -> TrieMap a v -> TrieMap a v
  default alterTM :: (Generic a, TrieMap a v ~ TrieMap' (Binder a) (Var a) (Rep a) v, HasTrieMap' (Binder a) (Var a) (Rep a))
                  => DBEnv -> a -> (Maybe v -> Maybe v) -> TrieMap a v -> TrieMap a v
  alterTM env x = alterTM' env (from x)

  lookupTM :: DBEnv -> a -> TrieMap a v -> Maybe v
  default lookupTM :: (Generic a, TrieMap a v ~ TrieMap' (Binder a) (Var a) (Rep a) v, HasTrieMap' (Binder a) (Var a) (Rep a))
                   => DBEnv -> a -> TrieMap a v -> Maybe v
  lookupTM env x = lookupTM' env (from x)

  foldTM :: (v -> r -> r) -> r -> TrieMap a v -> r
  default foldTM :: (Generic a, TrieMap a v ~ TrieMap' (Binder a) (Var a) (Rep a) v, HasTrieMap' (Binder a) (Var a) (Rep a))
                   => (v -> r -> r) -> r -> TrieMap a v -> r
  foldTM = foldTM'

  unionWithTM :: (v -> v -> v) -> TrieMap a v -> TrieMap a v -> TrieMap a v
  default unionWithTM :: (Generic a, TrieMap a v ~ TrieMap' (Binder a) (Var a) (Rep a) v, HasTrieMap' (Binder a) (Var a) (Rep a))
                   => (v -> v -> v) -> TrieMap a v -> TrieMap a v -> TrieMap a v
  unionWithTM = unionWithTM'

insertTM :: HasTrieMap a => a -> v -> TrieMap a v -> TrieMap a v
insertTM e v = alterTM emptyDBE e (const $ Just v)

deleteTM :: forall a v. HasTrieMap a => a -> TrieMap a v -> TrieMap a v
deleteTM e = alterTM @a @v emptyDBE e (const Nothing)

sizeTM :: forall a v. HasTrieMap a => TrieMap a v -> Int
sizeTM = foldTM @a @v (\_ n -> n + 1) 0

elemsTM :: forall a v. HasTrieMap a => TrieMap a v -> [v]
elemsTM = foldTM @a @v (:) []

lookupClosedTM :: HasTrieMap a => a -> TrieMap a v -> Maybe v
lookupClosedTM = lookupTM emptyDBE

-- * Default instances for common types

-- We can use the generic instance of lists
instance HasTrieMap a => HasTrieMap [a]

-- For 'Char' and 'Int' we use a regular map, this should exist for all primitive types
instance HasTrieMap Char where
  type TrieMap Char v = Map Char v
  emptyTM = Map.empty
  alterTM _ = flip Map.alter
  lookupTM _ = Map.lookup
  foldTM = Map.foldr
  unionWithTM = Map.unionWith

instance HasTrieMap Int where
  type TrieMap Int v = Map Int v
  emptyTM = Map.empty
  alterTM _ = flip Map.alter
  lookupTM _ = Map.lookup
  foldTM = Map.foldr
  unionWithTM = Map.unionWith

-- * Usage

data Expr
  = Var String
  | Lam String Expr
  | App Expr Expr
  deriving ( Generic )

-- | Make a TrieMap instance for Expr, by specifying the names of the
--   variable and binder constructors.
instance HasTrieMap Expr where
  type Binder Expr = Just "Lam"
  type Var Expr = Just "Var"

exampleE :: TrieMap Expr Int
exampleE = insertTM (Lam "x" $ Var "x") 5 $ insertTM (Var "x" `App` Var "x") 10 $ emptyTM @Expr

-- Returns 'Nothing'
example1 :: Maybe Int
example1 = lookupClosedTM (Var "y" `App` Var "y") exampleE

-- Returns 'Just 5', as (\y.y) is alpha-equivalent to (\x.x)
example2 :: Maybe Int
example2 = lookupClosedTM (Lam "y" $ Var "y") exampleE
