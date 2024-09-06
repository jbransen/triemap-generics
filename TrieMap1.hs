-- Section 3.8 from the paper

{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}

-- this is not nice
{-# LANGUAGE AllowAmbiguousTypes #-}
module TrieMap1 where

import GHC.Generics

import Data.Kind ( Type )
import Data.Map ( Map )
import qualified Data.Map as Map


-- * The generic instances

type TF v = Maybe v -> Maybe v

-- | The HasTrieMap' class defines functionality over the generic representation of data types
class HasTrieMap' (f :: Type -> Type) where
  data TrieMap' f :: Type -> Type

  emptyTM' :: TrieMap' f v
  alterTM' :: f x ->  TF v -> TrieMap' f v -> TrieMap' f v
  lookupTM' :: f x -> TrieMap' f v -> Maybe v
  foldTM' :: (v -> r -> r) -> r -> TrieMap' f v -> r
  unionWithTM' :: (v -> v -> v) -> TrieMap' f v -> TrieMap' f v -> TrieMap' f v

instance HasTrieMap' f => HasTrieMap' (M1 D meta f) where
  data TrieMap' (M1 D meta f) v = Empty | NonEmpty (TrieMap' f v)
  emptyTM' = Empty
  alterTM' (M1 v) f Empty = case f Nothing of
    Nothing -> Empty
    Just _  -> NonEmpty (alterTM' v f emptyTM')
  alterTM' (M1 v) f (NonEmpty tm) = NonEmpty (alterTM' v f tm)
  lookupTM' _ Empty = Nothing
  lookupTM' (M1 v) (NonEmpty tm) = lookupTM' v tm
  foldTM' _ z Empty = z
  foldTM' k z (NonEmpty tm) = foldTM' k z tm
  unionWithTM' _ Empty r = r
  unionWithTM' _ r Empty = r
  unionWithTM' f (NonEmpty tm1) (NonEmpty tm2) = NonEmpty (unionWithTM' f tm1 tm2)

instance HasTrieMap' f => HasTrieMap' (M1 C meta f) where
  data TrieMap' (M1 C meta f) v = TMC (TrieMap' f v)
  emptyTM' = TMC emptyTM'
  alterTM' (M1 v) f (TMC tm) = TMC (alterTM' v f tm)
  lookupTM' (M1 v) (TMC tm) = lookupTM' v tm
  foldTM' k z (TMC tm) = foldTM' k z tm
  unionWithTM' f (TMC tm1) (TMC tm2) = TMC (unionWithTM' f tm1 tm2)

instance HasTrieMap' f => HasTrieMap' (M1 S meta f) where
  data TrieMap' (M1 S meta f) v = TMS (TrieMap' f v)
  emptyTM' = TMS emptyTM'
  alterTM' (M1 v) f (TMS tm) = TMS (alterTM' v f tm)
  lookupTM' (M1 v) (TMS tm) = lookupTM' v tm
  foldTM' k z (TMS tm) = foldTM' k z tm
  unionWithTM' f (TMS tm1) (TMS tm2) = TMS (unionWithTM' f tm1 tm2)

instance (HasTrieMap' f, HasTrieMap' g) => HasTrieMap' (f :+: g) where
  data TrieMap' (f :+: g) v = TMPair (TrieMap' f v) (TrieMap' g v)
  emptyTM' = TMPair emptyTM' emptyTM'
  alterTM' (L1 v) f (TMPair tl tr) = TMPair (alterTM' v f tl) tr
  alterTM' (R1 v) f (TMPair tl tr) = TMPair tl (alterTM' v f tr)
  lookupTM' (L1 v) (TMPair tm _) = lookupTM' v tm
  lookupTM' (R1 v) (TMPair _ tm) = lookupTM' v tm
  foldTM' k z (TMPair tm1 tm2) = foldTM' k (foldTM' k z tm2) tm1
  unionWithTM' f (TMPair tm1a tm1b) (TMPair tm2a tm2b) = TMPair (unionWithTM' f tm1a tm2a) (unionWithTM' f tm1b tm2b)

instance (HasTrieMap' f, HasTrieMap' g) => HasTrieMap' (f :*: g) where
  data TrieMap' (f :*: g) v = TMProd (TrieMap' f (TrieMap' g v))
  emptyTM' = TMProd emptyTM'
  alterTM' (v1 :*: v2) f (TMProd tm) = TMProd (alterTM' v1 (liftTF (alterTM' v2 f)) tm)
  lookupTM' (v1 :*: v2) (TMProd tm) = lookupTM' v1 tm >>= lookupTM' v2
  foldTM' k z (TMProd tm) = foldTM' (flip (foldTM' k)) z tm
  unionWithTM' f (TMProd tm1) (TMProd tm2) = TMProd (unionWithTM' (unionWithTM' f) tm1 tm2)

instance HasTrieMap a => HasTrieMap' (Rec0 a) where
  data TrieMap' (Rec0 a) v = TMRec (TrieMap a v)
  emptyTM' :: forall v. TrieMap' (Rec0 a) v
  emptyTM' = TMRec (emptyTM @a @v)
  alterTM' (K1 v) f (TMRec tm) = TMRec (alterTM v f tm)
  lookupTM' (K1 v) (TMRec tm) = lookupTM v tm
  foldTM' k z (TMRec tm) = foldTM @a k z tm
  unionWithTM' f (TMRec tm1) (TMRec tm2) = TMRec (unionWithTM @a f tm1 tm2)

instance HasTrieMap' U1 where
  data TrieMap' U1 v = TMU1 (Maybe v)
  emptyTM' = TMU1 Nothing
  alterTM' U1 f (TMU1 mbv) = TMU1 (f mbv)
  lookupTM' U1 (TMU1 mbv) = mbv
  foldTM' k z (TMU1 mbv) = maybe z (`k` z) mbv
  unionWithTM' _ (TMU1 Nothing) (TMU1 Nothing) = TMU1 Nothing
  unionWithTM' _ (TMU1 Nothing) (TMU1 mbv2) = TMU1 mbv2
  unionWithTM' _ (TMU1 mbv1) (TMU1 Nothing) = TMU1 mbv1
  unionWithTM' f (TMU1 (Just v1)) (TMU1 (Just v2)) = TMU1 (Just $ f v1 v2)

liftTF :: HasTrieMap' f => (TrieMap' f v -> TrieMap' f v) -> Maybe (TrieMap' f v) -> Maybe (TrieMap' f v)
liftTF f Nothing = Just (f emptyTM')
liftTF f (Just m) = Just (f m)


-- * Non-generic version of the triemap class, this uses Generic instances as defaults

class HasTrieMap a where
  type TrieMap a v :: Type
  type TrieMap a v = TrieMap' (Rep a) v

  emptyTM :: TrieMap a v
  default emptyTM :: (TrieMap a v ~ TrieMap' (Rep a) v, HasTrieMap' (Rep a))
                  => TrieMap a v
  emptyTM = emptyTM'

  alterTM :: a -> (Maybe v -> Maybe v) -> TrieMap a v -> TrieMap a v
  default alterTM :: (Generic a, TrieMap a v ~ TrieMap' (Rep a) v, HasTrieMap' (Rep a))
                  => a -> (Maybe v -> Maybe v) -> TrieMap a v -> TrieMap a v
  alterTM x = alterTM' (from x)

  lookupTM :: a -> TrieMap a v -> Maybe v
  default lookupTM :: (Generic a, TrieMap a v ~ TrieMap' (Rep a) v, HasTrieMap' (Rep a))
                   => a -> TrieMap a v -> Maybe v
  lookupTM x = lookupTM' (from x)

  foldTM :: (v -> r -> r) -> r -> TrieMap a v -> r
  default foldTM :: (Generic a, TrieMap a v ~ TrieMap' (Rep a) v, HasTrieMap' (Rep a))
                   => (v -> r -> r) -> r -> TrieMap a v -> r
  foldTM = foldTM'

  unionWithTM :: (v -> v -> v) -> TrieMap a v -> TrieMap a v -> TrieMap a v
  default unionWithTM :: (Generic a, TrieMap a v ~ TrieMap' (Rep a) v, HasTrieMap' (Rep a))
                   => (v -> v -> v) -> TrieMap a v -> TrieMap a v -> TrieMap a v
  unionWithTM = unionWithTM'

insertTM :: HasTrieMap a => a -> v -> TrieMap a v -> TrieMap a v
insertTM e v = alterTM e (const $ Just v)

deleteTM :: forall a v. HasTrieMap a => a -> TrieMap a v -> TrieMap a v
deleteTM e = alterTM @a @v e (const Nothing)

sizeTM :: forall a v. HasTrieMap a => TrieMap a v -> Int
sizeTM = foldTM @a @v (\_ n -> n + 1) 0

elemsTM :: forall a v. HasTrieMap a => TrieMap a v -> [v]
elemsTM = foldTM @a @v (:) []

-- * Default instances for common types

-- We can use the generic instance of lists
instance HasTrieMap a => HasTrieMap [a]

-- For characters we use a traditional map, this should also exist for other primitive types
instance HasTrieMap Char where
  type TrieMap Char v = Map Char v
  emptyTM = Map.empty
  alterTM = flip Map.alter
  lookupTM = Map.lookup
  foldTM = Map.foldr
  unionWithTM = Map.unionWith

-- * Usage

data Expr = Var String
          | App Expr Expr
          deriving ( Generic )

-- This is all we need to have triemap functionality for Expr
instance HasTrieMap Expr

exampleE :: TrieMap Expr Int
exampleE = insertTM (Var "x" `App` Var "y") 10 $ emptyTM @Expr

-- Lookup a value, returns 'Just 10'
example :: Maybe Int
example = lookupTM (Var "x" `App` Var "y") exampleE
