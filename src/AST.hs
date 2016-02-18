{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module AST where

type Name = String

data Term = TmInt Int
          | TmVar Name
          | TmAbs Name Type Term
          | TmApp Term Term
          | TmAll Name Type Term -- universal qualification
          deriving (Eq)

data Type = TyInt
          | TyVar Name
          | TyPi Name Type Type
          | TyApp Type Term
          | TyProp     -- proposition
          | TyPrf Term -- family of proofs
          deriving (Eq)

data Kind = -- Γ ⊢ Prop :: ∗
            KProp
            -- Γ ⊢ Prf :: Πx:Prop. ∗
          | KPrf Name Type Kind
          deriving (Eq)

instance Show Term where
    show (TmInt i) = show i
    show (TmVar x) = x
    show (TmAbs x ty tm) = "(λ" ++ x ++ ":" ++ show ty ++ "." ++ show tm ++ ")"
    show (TmApp t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
    show (TmAll x ty tm) = "(∀" ++ x ++ ":" ++ show ty ++ "." ++ show tm ++ ")"

instance Show Type where
    show TyInt = "Int"
    show (TyVar t) = t
    show (TyPi x tyx ty) =
        if x == noCap
          then "(" ++ show tyx ++ " -> " ++ show ty ++ ")"
          else "(Π" ++ x ++ ":" ++ show tyx ++ "." ++ show ty ++ ")"
    show (TyApp ty tm) = "(" ++ show ty ++ " " ++ show tm ++ ")"
    show TyProp = "Prop"
    show (TyPrf tm) = "(Prf " ++ show tm ++ ")"

instance Show Kind where
    show KProp = "*"
    show (KPrf x ty kd) = "(Π" ++ x ++ ":" ++ show ty ++ "." ++ show kd ++ ")"



-- Clipboard: ∀,∃,Π,λ

(-->) :: Type -> Type -> Type
(-->) ty1 ty2 = TyPi noCap ty1 ty2

noCap :: Name
noCap = "_"

class AppShortCut a b where
    app :: a -> b -> Term

instance AppShortCut Name Name where
    app x y = TmApp (TmVar x) (TmVar y)

instance AppShortCut Term Name where
    app x y = TmApp x (TmVar y)

instance AppShortCut Name Term where
    app x y = TmApp (TmVar x) y

instance AppShortCut Term Term where
    app = TmApp

