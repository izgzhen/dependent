{-# LANGUAGE RecordWildCards #-}

module Example where

import AST
import Typing

import Control.Lens
import qualified Data.Map as M

env1 :: Env
env1 = kindOf %~ (M.insert "Vector" (KPrf "x" TyInt KProp)) $ initState

tm1 :: Term
tm1 = TmAbs "v" (TyPi "x" TyInt (TyApp (TyVar "Vector") (TmVar "x"))) (TmVar "v")

tm2 :: Term
tm2 = TmAbs "x" (TyApp (TyVar "Vector") (TmInt 2)) $
        TmAbs "f" (TyPi "y" (TyApp (TyVar "Vector") (TmInt 2)) TyInt)
                  (TmApp (TmVar "f") (TmVar "x"))
