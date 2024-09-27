{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
module TrieMap3.Class where

import Data.Char ( ord )
import Data.Kind ( Type )
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM

-- * The class

class HasTrieMap (a :: Type) where
  type TrieMap a v :: Type
  emptyTM :: TrieMap a v
  lookupTM :: a -> TrieMap a v -> Maybe v
  alterTM :: a -> (Maybe v -> Maybe v) -> TrieMap a v -> TrieMap a v

-- * Derived functionality

insertTM :: HasTrieMap a => a -> v -> TrieMap a v -> TrieMap a v
insertTM e v = alterTM e (const $ Just v)

deleteTM :: forall a v. HasTrieMap a => a -> TrieMap a v -> TrieMap a v
deleteTM e = alterTM @a @v e (const Nothing)

-- * Basic instances

instance HasTrieMap Int where
  type TrieMap Int v = IntMap v
  emptyTM = IM.empty
  lookupTM = IM.lookup
  alterTM = flip IM.alter

instance HasTrieMap Char where
  type TrieMap Char v = IntMap v
  emptyTM = IM.empty
  lookupTM = IM.lookup . ord
  alterTM = flip IM.alter . ord
