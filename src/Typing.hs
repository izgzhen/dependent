{-# LANGUAGE TemplateHaskell #-}

module Typing where

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M
import Control.Lens

import AST

data Env = Env {
  _kindOf :: M.Map Name Kind
, _typeOf :: M.Map Name Type
}

initState :: Env
initState = Env {
  _kindOf = M.empty
, _typeOf = M.empty
}

makeLenses ''Env

type Check = ExceptT String (State Env)

runType :: Term -> Env -> Either String Type
runType tm = evalState (runExceptT (tyck tm))

runKind :: Type -> Env -> Either String Kind
runKind ty = evalState (runExceptT (kind ty))


-- Kinding

kind :: Type -> Check Kind
kind TyInt = return KProper
kind (TyVar x) = lookupKind x   -- (KA-VAR)
kind ty@(TyPi x ty1 ty2) = do   -- (KA-PI)
    k1 <- kind ty1
    k2 <- withValType x ty1 $ kind ty2
    case (k1, k2) of
        (KProper, KProper) -> return KProper
        _ -> throwError $ "can't kind " ++ show ty
kind ty@(TyApp s t) = do        --- (KA-APP)
    ks  <- kind s
    ty2 <- tyck t
    case ks of
        KPi x ty1 k -> ty1 `typeEquiv` ty2 >> return (substKind x t k)
        _ -> throwError $ "can't kind " ++ show ty

-- Typing
tyck :: Term -> Check Type
tyck (TmInt _) = return TyInt
tyck (TmVar x) = lookupType x   -- (TA-VAR)
tyck tm@(TmAbs x s t) = do       -- (TA-ABS)
    ks <- kind s
    case ks of
        KProper -> TyPi x s <$> withValType x s (tyck t)
        _ -> throwError $ "can't type check " ++ show tm
tyck t@(TmApp t1 t2) = do       -- (TA-APP)
    ty1 <- tyck t1
    ty2 <- tyck t2
    case ty1 of
        TyPi x s1 ty -> s1 `typeEquiv` ty2 >> return (substTy x t2 ty)
        _ -> throwError $ "can't type check " ++ show t

-- Equivalence Checking

-- kind equivalence
kindEquiv :: Kind -> Kind -> Check ()
kindEquiv KProper KProper = return ()        -- (QKA-STAR)
kindEquiv (KPi x1 t1 k1) (KPi x2 t2 k2) = do -- (QKA-PI)
    t1 `typeEquiv` t2
    withValType x1 t1 $
        withValType x2 t2 $
            k1 `kindEquiv` k2

kindEquiv k1 k2 = throwError $ show k1 ++ " is not kind equivalent to " ++ show k2

-- type equivalence
typeEquiv :: Type -> Type -> Check ()
typeEquiv TyInt TyInt = return ()
typeEquiv (TyVar x) (TyVar x') | x == x' = return ()     -- (QTA-VAR)
typeEquiv (TyPi x s1 s2) (TyPi x' t1 t2) = do            -- (QTA-PI)
    s1 `typeEquiv` t1
    withValType x t1 $
        withValType x' t2 $
            s2 `typeEquiv` t2
typeEquiv (TyApp s1 tm1) (TyApp s2 tm2) = do            -- (QTA-APP)
    s1 `typeEquiv` s2
    tm1 `termEquiv` tm2

typeEquiv ty1 ty2 = throwError $ show ty1 ++ " is not type equivalent to " ++ show ty2

-- term equivalence
termEquiv :: Term -> Term -> Check ()
termEquiv (TmInt i) (TmInt i') | i == i' = return ()
termEquiv (TmVar x) (TmVar x') | x == x' = return ()    -- (QA-VAR)
termEquiv (TmAbs x1 s1 tm1) (TmAbs x2 s2 tm2) = do      -- (QA-ABS)
    s1 `typeEquiv` s2
    withValType x1 s1 $
        withValType x2 s2 $
            tm1 `termEquiv` substTm x2 (TmVar x1) tm2

termEquiv (TmApp s1 t1) (TmApp s2 t2) = do              -- (QA-APP)
    s1 `termEquiv` s2
    t1 `termEquiv` t2
termEquiv tm1 (TmAbs x s tm) =                          -- (QA-NABS1)
    withValType x s $ TmApp tm1 (TmVar x) `termEquiv` tm
termEquiv (TmAbs x s tm) tm1 =                          -- (QA-NABS2)
    withValType x s $ TmApp tm1 (TmVar x) `termEquiv` tm
termEquiv tm1 tm2 = throwError $ show tm1 ++ " is not term equivalent to " ++ show tm2


-- Utilities

lookupType :: Name -> Check Type
lookupType x = do
    mTy <- M.lookup x <$> use typeOf
    case mTy of
        Just ty -> return ty
        Nothing -> throwError $ "Can't find variable's type " ++ x

lookupKind :: Name -> Check Kind
lookupKind x = do
    mKd <- M.lookup x <$> use kindOf
    case mKd of
        Just kd -> return kd
        Nothing -> throwError $ "Can't find variable's kind " ++ x

withValType :: Name -> Type -> Check a -> Check a
withValType x ty ck = do
    old <- use typeOf
    typeOf %= M.insert x ty
    a <- ck
    typeOf .= old
    return a

substKind :: Name -> Term -> Kind -> Kind
substKind _ _ KProper = KProper
substKind x tm kd@(KPi x' ty' innerKd)
    | x == x'   = kd
    | otherwise = KPi x' (substTy x tm ty') (substKind x tm innerKd)

substTy :: Name -> Term -> Type -> Type
substTy _ _ TyInt = TyInt
substTy _ _ t@(TyVar _) = t
substTy x tm t@(TyPi x' ty' ty)
    | x == x'   = t
    | otherwise = TyPi x' (substTy x tm ty') (substTy x tm ty)
substTy x tm (TyApp ty tm') = TyApp (substTy x tm ty) (substTm x tm tm')

substTm :: Name -> Term -> Term -> Term
substTm _ _ (TmInt i) = TmInt i
substTm x tm t@(TmVar x')
    | x == x'   = tm
    | otherwise = t
substTm x tm t@(TmAbs x' ty' tm')
    | x == x'   = t
    | otherwise = TmAbs x (substTy x tm ty') (substTm x tm tm')
substTm x tm (TmApp t1 t2) = TmApp (substTm x tm t1) (substTm x tm t2)


