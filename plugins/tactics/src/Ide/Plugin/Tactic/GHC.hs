{-# LANGUAGE ViewPatterns #-}

module Ide.Plugin.Tactic.GHC where

import           Refinery.Tactic (choice)
import ConLike
import Data.Maybe (isJust, maybeToList)
import DataCon
import Ide.Plugin.Tactic.Types
import TcType
import TyCoRep
import TyCon
import Type
import TysWiredIn (intTyCon, floatTyCon, doubleTyCon, charTyCon)
import Unique
import Var


tcTyVar_maybe :: Type -> Maybe Var
tcTyVar_maybe ty | Just ty' <- tcView ty = tcTyVar_maybe ty'
tcTyVar_maybe (CastTy ty _) = tcTyVar_maybe ty  -- look through casts, as
                                                -- this is only used for
                                                -- e.g., FlexibleContexts
tcTyVar_maybe (TyVarTy v)   = Just v
tcTyVar_maybe _             = Nothing


instantiateType :: Type -> ([TyVar], Type)
instantiateType t = do
  let vs  = tyCoVarsOfTypeList t
      vs' = fmap cloneTyVar vs
      subst = foldr (\(v,t) a -> extendTCvSubst a v $ TyVarTy t) emptyTCvSubst
            $ zip vs vs'
   in (vs', substTy subst t)


cloneTyVar :: TyVar -> TyVar
cloneTyVar t =
  let uniq = getUnique t
      some_magic_number = 49
   in setVarUnique t $ deriveUnique uniq some_magic_number


------------------------------------------------------------------------------
-- | Is this a function type?
isFunction :: Type -> Bool
isFunction (tcSplitFunTys -> ((_:_), _)) = True
isFunction _ = False

------------------------------------------------------------------------------
-- | Is this an algebraic type?
algebraicTyCon :: Type -> Maybe TyCon
algebraicTyCon (splitTyConApp_maybe -> Just (tycon, _))
  | tycon == intTyCon    = Nothing
  | tycon == floatTyCon  = Nothing
  | tycon == doubleTyCon = Nothing
  | tycon == charTyCon   = Nothing
  | tycon == funTyCon    = Nothing
  | otherwise = Just tycon
algebraicTyCon _ = Nothing

------------------------------------------------------------------------------
-- | Can ths type be lambda-cased?
--
-- Return: 'Nothing' if no
--         @Just False@ if it can't be homomorphic
--         @Just True@ if it can
lambdaCaseable :: Type -> Maybe Bool
lambdaCaseable (splitFunTy_maybe -> Just (arg, res))
  | isJust (algebraicTyCon arg)
  = Just $ isJust $ algebraicTyCon res
lambdaCaseable _ = Nothing


data ConLikeGroup = ConLikeGroup
  { clgCons :: ![ConLike] -- ^ the constructors or patterns in this group
  , clgComplete :: !Bool  -- ^ should this group be treated as generating an exhaustive match?
  }

------------------------------------------------------------------------------
-- | What data-constructor, if any, does the type have?
-- Additional returns the type arguments to the TyCon of the type
tyDataCons :: Type -> Maybe ([DataCon], [Type])
tyDataCons g = do
  (tc, apps) <- splitTyConApp_maybe g
  pure $ (tyConDataCons tc, apps)

------------------------------------------------------------------------------
-- | What groups of con-likes are sensible to use when pattern matching on the argument?
-- Also returns the type arguments to the TyCon of the type
tyPatternMatchGroups :: Type -> ExtractM [(ConLikeGroup, [Type])]
tyPatternMatchGroups t = pure $ conGroup where
  conGroup = do
    (dcs, apps) <- maybeToList $ tyDataCons t
    pure (ConLikeGroup (RealDataCon <$> dcs) True, apps)

------------------------------------------------------------------------------
-- | What groups of con-likes are sensible to use when constructing the argument?
-- Also returns the type arguments to the TyCon of the type
tyConLikes :: Type -> ExtractM [(ConLike, [Type])]
tyConLikes t = pure $ conGroup where
  conGroup = do
    (dcs, apps) <- maybeToList $ tyDataCons t
    dc <- dcs
    pure (RealDataCon dc, apps)
