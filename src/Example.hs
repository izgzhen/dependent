{-# LANGUAGE RecordWildCards #-}

module Example where

import AST
import Typing

import Prelude hiding (succ)
import Control.Lens
import qualified Data.Map as M

-- Dependent type programming with Lambda LF

env1 :: Env
env1 = kindOf %~ (M.insert "Vector" (KPrf "x" TyInt KProp)) $ initState

tm1 :: Term
tm1 = TmAbs "v" (TyPi "x" TyInt (TyApp (TyVar "Vector") (TmVar "x"))) (TmVar "v")

tm2 :: Term
tm2 = TmAbs "x" (TyApp (TyVar "Vector") (TmInt 2)) $
        TmAbs "f" (TyPi "y" (TyApp (TyVar "Vector") (TmInt 2)) TyInt)
                  (TmApp (TmVar "f") (TmVar "x"))

-- Calculus of Construction

nat :: Term
nat = TmAll "a" TyProp $ -- ∀a:Prop.
        TmAll "z" (TyPrf (TmVar "a")) $ -- ∀z:Prf a.
            TmAll "s" (TyPi "x" (TyPrf (TmVar "a")) (TyPrf (TmVar "a"))) -- ∀s:Prf a -> Prf a.
                (TmVar "a") -- a

zero :: Term
zero = TmAbs "a" TyProp $ -- ∀a:Prop.
        TmAbs "z" (TyPrf (TmVar "a")) $ -- ∀z:Prf a.
            TmAbs "s" (TyPi "x" (TyPrf (TmVar "a")) (TyPrf (TmVar "a"))) -- ∀s:Prf a -> Prf a.
                (TmVar "z") -- z : Prf nat

succ :: Term
succ = TmAbs "n" (TyPrf (TmVar "nat")) $
        TmAbs "a" TyProp $
            TmAbs "z" (TyPrf (TmVar "a")) $
                TmAbs "s" (TyPi "x" (TyPrf (TmVar "a")) (TyPrf (TmVar "a"))) $
                    TmApp (TmVar "s") $
                        (TmApp
                            (TmApp
                                (TmApp
                                    (TmVar "n")
                                    (TmVar "a"))
                                (TmVar "z"))
                            (TmVar "s"))

add :: Term
add = TmAbs "m" (TyVar "Nat") $
        TmAbs "n" (TyVar "Nat") $
            TmApp
                (TmApp
                    (TmApp
                        (TmVar "m")
                        (TmVar "nat"))
                    (TmVar "n"))
                (TmVar "succ")

-- exists = λf:A→Prop.all c:Prop.all m:(Πx:Prop.Prf (f x)→Prf c).c
exists :: Term
exists = TmAbs "f" (TyPi "x" (TyVar "A") TyProp) $
            TmAll "c" TyProp $
                TmAll "m" (TyPi "x" (TyVar "A")
                                    (TyPi "x0" (TyPrf (TmApp
                                                        (TmVar "f")
                                                        (TmVar "x")))
                                               (TyPrf (TmVar "c"))))
                          (TmVar "c")

exercise261 :: Term
exercise261 = TmAbs "f" (TyPi "x" (TyVar "A") TyProp) $
                TmAbs "a" (TyVar "A") $
                    TmAbs "i" (TyPrf (TmApp (TmVar "f") (TmVar "a")))
                              (TmAll "x" (TyVar "A")
                                         (TmApp
                                            (TmVar "f")
                                            (TmVar "x")))


-- Leibniz equality
eq :: Term
eq = TmAbs "a" TyProp $
        TmAbs "x" (TyPrf (TmVar "a")) $
            TmAbs "y" (TyPrf (TmVar "a")) $
                TmAll "p" (TyPi "i" (TyPrf (TmVar "a")) TyProp) $
                    TmAll "h" (TyPrf (TmApp (TmVar "p") (TmVar "x"))) $
                        TmApp (TmVar "p") (TmVar "y")


-- The term as proof of reflexivity
eqRefl :: Term
eqRefl = TmAbs "a" TyProp $
            TmAbs "x" (TyPrf (TmVar "a")) $
                TmAbs "p" (TyPi "i" (TyPrf (TmVar "a")) TyProp) $
                    TmAbs "h" (TyPrf (TmApp (TmVar "p") (TmVar "x"))) $
                        TmVar "h"

eqReflTy :: Type
eqReflTy = TyPi "a" TyProp $
            TyPi "x" (TyPrf (TmVar "a")) $
                TyPrf (TmApp
                        (TmApp
                            (TmApp
                                (TmVar "eq")
                                (TmVar "a"))
                            (TmVar "x"))
                        (TmVar "x"))
 
proveReflex :: Either String ()
proveReflex = flip runCheck initState { _termOf = M.singleton "eq" eq } $ do
    eqReflTy' <- tyck eqRefl
    eqReflTy' `typeEquiv` eqReflTy

