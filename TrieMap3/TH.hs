{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module TrieMap3.TH where

import TrieMap3.Class
import Control.Monad
import Data.Maybe ( fromMaybe )
import Data.Char ( isAlphaNum )

import Language.Haskell.TH hiding ( Type )
import Language.Haskell.TH.Extras ( argTypesOfCon, nameOfCon, nameOfBinder )

deriveTriemap :: Name -> Q [Dec]
deriveTriemap nm = do
  TyConI (DataD [] _ tyvars Nothing cs _) <- reify nm
  let cons = map (\c -> (nameOfCon c, argTypesOfCon c)) cs

  -- The data type
  nEmpty <- newName $ "Empty_" ++ sanitizeName (nameBase nm)
  let cempty = NormalC nEmpty []
  nNonEmpty <- newName $ "NonEmpty_" ++ sanitizeName (nameBase nm)
  let v = mkName "v"
  fields <- forM cons $ \(cnm, fs) -> do
    let fnm = mkName $ "tm_" ++ sanitizeName (nameBase cnm)
    let tp = case fs of
          [] -> ConT ''Maybe `AppT` VarT v
          _  -> foldr (\t b -> ConT ''TrieMap `AppT` t `AppT` b) (VarT v) fs
    return (fnm, Bang NoSourceUnpackedness NoSourceStrictness, tp)
  let crec = RecC nNonEmpty fields

  let typeWithVars = foldl AppT (ConT nm) $ map (VarT . nameOfBinder) tyvars
  let dataDef = DataInstD [] (Just [PlainTV v ()]) (ConT ''TrieMap `AppT` typeWithVars `AppT` VarT v) Nothing [cempty, crec] []

  -- emptyTM
  let fEmpty = FunD 'emptyTM [Clause [] (NormalB $ ConE nEmpty) []]

  -- lookupTM
  lookupCs <- forM (zip cons fields) $ \((cnm, fs), (fnm, _, _)) -> do
    let tm = mkName "tm"
    vars <- forM fs $ \_ -> newName "v"
    let sel = VarE fnm `AppE` VarE tm
    let body = case vars of
          [] -> sel
          (v1:vs) -> foldr (\vx b -> VarE '(>>=) `AppE` b `AppE` (VarE 'lookupTM `AppE` VarE vx)) (VarE 'lookupTM `AppE` VarE v1 `AppE` sel) vs
    pure $ Clause [ConP cnm [] (map VarP vars), VarP tm] (NormalB body) []
  let fLookup = FunD 'lookupTM $
        Clause [WildP, ConP nEmpty [] []] (NormalB $ ConE 'Nothing) [] : lookupCs

  -- alterTM
  let ve = mkName "e"
  let vf = mkName "f"
  let mkEmpty = RecConE nNonEmpty
        [ (fnm, case tp of
              AppT (AppT (ConT c) _) _
                | c == ''TrieMap -> VarE 'emptyTM
              _ -> ConE 'Nothing)
        | (fnm, _, tp) <- fields
        ]
  alterEmp <- [|
                case $(varE vf) Nothing of
                  Nothing -> $(conE nEmpty)
                  Just nv -> alterTM $(varE ve) (\_ -> Just nv) $(pure mkEmpty)
               |]
  let alterEmpty = Clause [ VarP ve, VarP vf, ConP nEmpty [] [] ] (NormalB alterEmp) []
  alterCs <- forM (zip cons fields) $ \((cnm, fs), (fnm, _, _)) -> do
    let tm = mkName "tm"
    f <- newName "f"
    funs <- replicateM (0 `max` (length fs - 1)) $ newName "g"
    vars <- forM fs $ \_ -> newName "v"
    let body = RecUpdE (VarE tm) [(fnm, case vars of
                                      [] -> VarE f `AppE` (VarE fnm `AppE` VarE tm)
                                      (v1:_) -> VarE 'alterTM
                                                `AppE` VarE v1
                                                `AppE` VarE (head $ funs ++ [f])
                                                `AppE` (VarE fnm `AppE` VarE tm))]
    let wheres =
          [ FunD g [Clause [VarP vve]
                     (NormalB $ ConE 'Just
                       `AppE` (VarE 'alterTM `AppE` VarE var `AppE` VarE nextg
                               `AppE` (VarE 'fromMaybe `AppE` VarE 'emptyTM `AppE` VarE vve))) []]
          | let vve = mkName "e"
          , (g,nextg,var) <- zip3 funs (tail funs ++ [f]) (tail vars)
          ]
    pure $ Clause [ConP cnm [] (map VarP vars), VarP f, VarP tm] (NormalB body) wheres
  let fAlter = FunD 'alterTM $ alterEmpty : alterCs
  
  -- The instance
  let ctx = [ ConT ''HasTrieMap `AppT` VarT (nameOfBinder tyvar) | tyvar <- tyvars ]
  let inst = InstanceD Nothing ctx (ConT ''HasTrieMap `AppT` typeWithVars) [dataDef, fEmpty, fLookup, fAlter ]

  -- Return the types
  pure [inst]


sanitizeName :: String -> String
sanitizeName = map (\x -> if isAlphaNum x then x else '_')
