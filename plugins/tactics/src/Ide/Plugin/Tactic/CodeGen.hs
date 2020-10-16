{-# LANGUAGE FlexibleContexts #-}
module Ide.Plugin.Tactic.CodeGen where

import Control.Monad.Except
import Data.List
import Data.Traversable
import DataCon
import Development.IDE.GHC.Compat
import GHC.Exts
import GHC.SourceGen.Binds
import GHC.SourceGen.Expr
import GHC.SourceGen.Overloaded
import GHC.SourceGen.Pat
import Ide.Plugin.Tactic.Judgements
import Ide.Plugin.Tactic.Machinery
import Ide.Plugin.Tactic.Naming
import Ide.Plugin.Tactic.Types
import Ide.Plugin.Tactic.GHC
import Name
import ConLike
import PatSyn
import Type hiding (Var)

class Instantiable a where
  -- | Returns the original TyCon this thing builds
  origTyCon :: a -> Maybe TyCon
  -- | Returns just the instantiated value argument types of the 'a' (excluding dictionary arguments)
  instOrigArgTys :: a -> [Type] -> [Type]

instance Instantiable ConLike where
  origTyCon (RealDataCon dc) = origTyCon dc
  origTyCon (PatSynCon pc) =
    let (_, _, _, _, _, rt) = patSynSig pc
    in tyConAppTyCon_maybe rt
  instOrigArgTys = conLikeInstOrigArgTys

instance Instantiable DataCon where
  origTyCon = Just . dataConTyCon
  instOrigArgTys = dataConInstOrigArgTys'

destructMatches
    :: (Instantiable c, NamedThing c)
    => (c -> Judgement -> Rule)
       -- ^ How to construct each match
    -> (Judgement -> Judgement)
       -- ^ How to derive each match judgement
    -> [c]
       -- ^ Constructors being instantiated
    -> [Type]
       -- ^ instantiated type arguments to the result TyCon of the constructors
    -> Judgement
       -- ^ goal judgement
    -> RuleM [RawMatch]
destructMatches f f2 cons apps jdg = do
  let hy = jHypothesis jdg
      g  = jGoal jdg
  case cons of
    [] -> throwError $ GoalMismatch "destruct" g
    _ -> for cons $ \dc -> do
      let args = instOrigArgTys dc apps
      names <- mkManyGoodNames hy args

      let pat :: Pat GhcPs
          pat = conP (fromString $ occNameString $ getOccName dc)
              $ fmap bvar' names
          j = f2
            $ introducingPat (zip names $ coerce args)
            $ withNewGoal g jdg
      sg <- f dc j
      pure $ match [pat] $ unLoc sg

-- | Essentially same as 'dataConInstOrigArgTys' in GHC,
--   but we need some tweaks in GHC >= 8.8.
--   Since old 'dataConInstArgTys' seems working with >= 8.8,
--   we just filter out non-class types in the result.
dataConInstOrigArgTys' :: DataCon -> [Type] -> [Type]
dataConInstOrigArgTys' con ty =
    let tys0 = dataConInstOrigArgTys con ty
    in filter (maybe True (not . isClassTyCon) . tyConAppTyCon_maybe) tys0

------------------------------------------------------------------------------
-- | Combinator for performing case splitting, and running sub-rules on the
-- resulting matches.

destruct' :: (DataCon -> Judgement -> Rule) -> OccName -> Judgement -> Rule
destruct' f term jdg = do
  let hy = jHypothesis jdg
  case find ((== term) . fst) $ toList hy of
    Nothing -> throwError $ UndefinedHypothesis term
    Just (_, t)
      | Just (cs, apps) <- tyDataCons $ unCType t
      -> fmap noLoc $ case' (var' term) <$>
             destructMatches f (destructing term) cs apps jdg
    Just (_, t) -> throwError $ GoalMismatch "destruct" t


------------------------------------------------------------------------------
-- | Combinator for performign case splitting, and running sub-rules on the
-- resulting matches.
destructLambdaCase' :: (DataCon -> Judgement -> Rule) -> Judgement -> Rule
destructLambdaCase' f jdg = do
  let g  = jGoal jdg
  case splitFunTy_maybe (unCType g) of
    Just (arg, _)
      | isAlgType arg
      , Just (cs, apps) <- tyDataCons arg
      -> fmap noLoc $ lambdaCase <$>
             destructMatches f id cs apps jdg
    _ -> throwError $ GoalMismatch "destructLambdaCase'" g


------------------------------------------------------------------------------
-- | Construct a data con with subgoals for each field.
buildDataCon
    :: (Instantiable c, NamedThing c)
    => Judgement
    -> c            -- ^ The data con to build
    -> [Type]       -- ^ Type arguments for the data con
    -> RuleM (LHsExpr GhcPs)
buildDataCon jdg dc apps = do
  let args = instOrigArgTys dc apps
  sgs <- traverse (newSubgoal . flip withNewGoal jdg . CType) args
  pure
    . noLoc
    . foldl' (@@)
        (HsVar noExtField $ noLoc $ Unqual $ getOccName dc)
    $ fmap unLoc sgs


------------------------------------------------------------------------------
-- | Like 'var', but works over standard GHC 'OccName's.
var' :: Var a => OccName -> a
var' = var . fromString . occNameString

------------------------------------------------------------------------------
-- | Like 'bvar', but works over standard GHC 'OccName's.
bvar' :: BVar a => OccName -> a
bvar' = bvar . fromString . occNameString
