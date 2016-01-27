module AST where

type Name = String

data Term = TmVar Name
          | TmAbs Name Type Term
          | TmApp Term Term
          deriving (Show, Eq)

data Type = TyVar Name
          | TyPi Name Type Type
          | TyApp Type Term
          deriving (Show, Eq)

data Kind = KProper
          | KPi Name Type Kind
          deriving (Show, Eq)

