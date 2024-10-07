-- Section 3 from the paper, with Template Haskell

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module TrieMap3 where

import TrieMap3.Class
import TrieMap3.TH

data Expr
  = Var String
  | Lam String Expr
  | App Expr Expr
  | If Expr Expr Expr
  | Nop

-- Derive some instances
$(deriveTriemap ''[])
$(deriveTriemap ''Expr)
$(deriveTriemap ''Maybe)


exampleE :: TrieMap Expr Int
exampleE = insertTM (Var "x" `App` Var "y") 10 emptyTM

-- Lookup a value, returns 'Just 10'
example :: Maybe Int
example = lookupTM (Var "x" `App` Var "y") exampleE

-- Lookup a value, returns 'Nothing'
example2 :: Maybe Int
example2 = lookupTM (Var "y" `App` Var "y") exampleE


