module AST where

type Name = String

data Term = TmInt Int
          | TmVar Name
          | TmAbs Name Type Term
          | TmApp Term Term
          deriving (Eq)

data Type = TyInt
          | TyVar Name
          | TyPi Name Type Type
          | TyApp Type Term
          deriving (Eq)

data Kind = KProper
          | KPi Name Type Kind
          deriving (Eq)

instance Show Term where
    show (TmInt i) = show i
    show (TmVar x) = x
    show (TmAbs x ty tm) = "(λ" ++ x ++ ":" ++ show ty ++ "." ++ show tm ++ ")"
    show (TmApp t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"

instance Show Type where
    show TyInt = "Int"
    show (TyVar t) = t
    show (TyPi x tyx ty) = "(Π" ++ x ++ ":" ++ show tyx ++ "." ++ show ty ++ ")"
    show (TyApp ty tm) = "(" ++ show ty ++ " " ++ show tm ++ ")"

instance Show Kind where
    show KProper = "*"
    show (KPi x ty kd) = "(Π" ++ x ++ ":" ++ show ty ++ "." ++ show kd ++ ")"



