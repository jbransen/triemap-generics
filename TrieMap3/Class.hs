{-# LANGUAGE TypeFamilies #-}
module TrieMap3.Class where

import Data.Char ( ord )
import Data.Kind ( Type )
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM

-- * The class

class HasTrieMap (a :: Type) where
  data TrieMap a :: Type -> Type
  emptyTM :: TrieMap a v
  lookupTM :: a -> TrieMap a v -> Maybe v
  alterTM :: a -> (Maybe v -> Maybe v) -> TrieMap a v -> TrieMap a v

-- * Derived functionality

insertTM :: HasTrieMap a => a -> v -> TrieMap a v -> TrieMap a v
insertTM e v = alterTM e (const $ Just v)

deleteTM :: HasTrieMap a => a -> TrieMap a v -> TrieMap a v
deleteTM e = alterTM e (const Nothing)

-- * Basic instances

instance HasTrieMap Int where
  data instance TrieMap Int v = TrieMapInt (IntMap v)
  emptyTM = TrieMapInt IM.empty
  lookupTM i (TrieMapInt tm) = i `IM.lookup` tm
  alterTM i f (TrieMapInt tm) = TrieMapInt (IM.alter f i tm)

instance HasTrieMap Char where
  data instance TrieMap Char v = TrieMapChar (IntMap v)
  emptyTM = TrieMapChar IM.empty
  lookupTM i (TrieMapChar tm) = ord i `IM.lookup` tm
  alterTM i f (TrieMapChar tm) = TrieMapChar (IM.alter f (ord i) tm)

-- * Helpers

(|>) :: a -> (a -> b) -> b     -- Reverse application
infixl 0 |>
x |> f = f x

(|>>) :: (HasTrieMap m1, HasTrieMap m2)
      => ((Maybe (TrieMap m2 a) -> Maybe (TrieMap m2 a)) -> TrieMap m1 (TrieMap m2 a) -> TrieMap m1 (TrieMap m2 a))
      -> (TrieMap m2 a -> TrieMap m2 a)
      -> TrieMap m1 (TrieMap m2 a) -> TrieMap m1 (TrieMap m2 a)
infixl 1 |>>
(|>>) f g = f (Just . g . deMaybe)


deMaybe :: HasTrieMap t => Maybe (TrieMap t a) -> TrieMap t a
deMaybe Nothing  = emptyTM
deMaybe (Just t) = t
