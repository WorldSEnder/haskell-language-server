{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}

-- | A plugin that uses tactics to synthesize code
module Ide.Plugin.Tactic
  ( descriptor
  , tacticTitle
  , TacticCommand (..)
  , TacticParams(..)
  ) where

import           Control.Arrow
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.Maybe
import           Data.Aeson
import           Data.Coerce
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import           Data.Traversable
import           Development.IDE.Core.PositionMapping
import           Development.IDE.Core.RuleTypes
import           Development.IDE.Core.Service (runAction)
import           Development.IDE.Core.Shake (useWithStale, IdeState (..))
import           Development.IDE.GHC.Compat
import           Development.IDE.GHC.Error (realSrcSpanToRange)
import           Development.IDE.Spans.LocalBindings (getDefiningBindings)
import           Development.Shake (Action)
import           DynFlags (xopt)
import qualified FastString
import           GHC.LanguageExtensions.Type (Extension (LambdaCase))
import           Ide.Plugin (mkLspCommand)
import           Ide.Plugin.Tactic.Context
import           Ide.Plugin.Tactic.GHC
import           Ide.Plugin.Tactic.Judgements
import           Ide.Plugin.Tactic.Range
import           Ide.Plugin.Tactic.Tactics
import           Ide.Plugin.Tactic.TestTypes
import           Ide.Plugin.Tactic.Types
import           Ide.TreeTransform (transform, graft, useAnnotatedSource)
import           Ide.Types
import           Language.Haskell.LSP.Core (clientCapabilities)
import           Language.Haskell.LSP.Types
import           OccName


descriptor :: PluginId -> PluginDescriptor
descriptor plId = (defaultPluginDescriptor plId)
    { pluginCommands
        = fmap (\tc -> withSomeTacticCommand tc $ \tac -> withSerializableContext tac $
            PluginCommand
              (tcCommandId tc)
              (tacticDesc $ tcCommandName tc)
              (tacticCmd tac))
            [minBound .. maxBound]
    , pluginCodeActionProvider = Just codeActionProvider
    }

tacticDesc :: T.Text -> T.Text
tacticDesc name = "fill the hole using the " <> name <> " tactic"

------------------------------------------------------------------------------
-- | A 'TacticProvider' is a way of giving context-sensitive actions to the LS
-- UI.
type TacticProvider = DynFlags -> PluginId -> Uri -> Range -> Judgement -> IO [CAResult]


------------------------------------------------------------------------------
-- | Construct a 'CommandId'
tcCommandId :: TacticCommand -> CommandId
tcCommandId c = coerce $ T.pack $ "tactics" <> show c <> "Command"


------------------------------------------------------------------------------
-- | The name of the command for the LS.
tcCommandName :: TacticCommand -> T.Text
tcCommandName = T.pack . show

------------------------------------------------------------------------------
-- | Mapping from tactic commands to their contextual providers. See 'provide',
-- 'filterGoalType' and 'filterBindingType' for the nitty gritty.
commandProvider :: TacticCommand -> TacticProvider
commandProvider Auto  = provide AutoS ()
commandProvider Intros =
  filterGoalType isFunction $
    provide IntrosS ()
commandProvider Destruct =
  filterBindingType destructFilter $ \occ _ ->
    provide DestructS $ T.pack $ occNameString occ
commandProvider Homomorphism =
  filterBindingType homoFilter $ \occ _ ->
    provide HomomorphismS $ T.pack $ occNameString occ
commandProvider DestructLambdaCase =
  requireExtension LambdaCase $
    filterGoalType (isJust . lambdaCaseable) $
      provide DestructLambdaCaseS ()
commandProvider HomomorphismLambdaCase =
  requireExtension LambdaCase $
    filterGoalType ((== Just True) . lambdaCaseable) $
      provide HomomorphismLambdaCaseS ()


------------------------------------------------------------------------------
-- | A mapping from tactic commands to actual tactics for refinery.
commandTactic :: KnownTacticCommand tc => proxy tc -> TacticContext tc -> TacticsM ()
commandTactic p = case ktcSing p of
  AutoS                   -> const auto
  IntrosS                 -> const intros
  DestructS               -> destruct . mkVarOcc . T.unpack
  HomomorphismS           -> homo . mkVarOcc . T.unpack
  DestructLambdaCaseS     -> const destructLambdaCase
  HomomorphismLambdaCaseS -> const homoLambdaCase


------------------------------------------------------------------------------
-- | We should show homos only when the goal type is the same as the binding
-- type, and that both are usual algebraic types.
homoFilter :: Type -> Type -> Bool
homoFilter (algebraicTyCon -> Just t1) (algebraicTyCon -> Just t2) = t1 == t2
homoFilter _ _ = False


------------------------------------------------------------------------------
-- | We should show destruct for bindings only when those bindings have usual
-- algebraic types.
destructFilter :: Type -> Type -> Bool
destructFilter _ (algebraicTyCon -> Just _) = True
destructFilter _ _ = False


runIde :: IdeState -> Action a -> IO a
runIde state = runAction "tactic" state


codeActionProvider :: CodeActionProvider
codeActionProvider _conf state plId (TextDocumentIdentifier uri) range _ctx
  | Just nfp <- uriToNormalizedFilePath $ toNormalizedUri uri =
      fromMaybeT (Right $ List []) $ do
        (_, jdg, _, dflags) <- judgementForHole state nfp range
        actions <- lift $
          -- This foldMap is over the function monoid.
          foldMap commandProvider [minBound .. maxBound]
            dflags
            plId
            uri
            range
            jdg
        pure $ Right $ List actions
codeActionProvider _ _ _ _ _ _ = pure $ Right $ codeActions []


codeActions :: [CodeAction] -> List CAResult
codeActions = List . fmap CACodeAction


------------------------------------------------------------------------------
-- | Terminal constructor for providing context-sensitive tactics. Tactics
-- given by 'provide' are always available.
provide :: (KnownTacticCommand tc, ToJSON (TacticContext tc)) => proxy tc -> TacticContext tc -> TacticProvider
provide tc args _ plId uri range _ = do
  let title = tacticTitle tc args
      params = TacticParams { file = uri , range = range , tac_args = args }
  cmd <- mkLspCommand plId (tcCommandId $ ktcValue tc) title (Just [toJSON params])
  pure
    $ pure
    $ CACodeAction
    $ CodeAction title (Just CodeActionQuickFix) Nothing Nothing
    $ Just cmd


------------------------------------------------------------------------------
-- | Restrict a 'TacticProvider', making sure it appears only when the given
-- predicate holds for the goal.
requireExtension :: Extension -> TacticProvider -> TacticProvider
requireExtension ext tp dflags plId uri range jdg =
  case xopt ext dflags of
    True  -> tp dflags plId uri range jdg
    False -> pure []


------------------------------------------------------------------------------
-- | Restrict a 'TacticProvider', making sure it appears only when the given
-- predicate holds for the goal.
filterGoalType :: (Type -> Bool) -> TacticProvider -> TacticProvider
filterGoalType p tp dflags plId uri range jdg =
  case p $ unCType $ jGoal jdg of
    True  -> tp dflags plId uri range jdg
    False -> pure []


------------------------------------------------------------------------------
-- | Multiply a 'TacticProvider' for each binding, making sure it appears only
-- when the given predicate holds over the goal and binding types.
filterBindingType
    :: (Type -> Type -> Bool)  -- ^ Goal and then binding types.
    -> (OccName -> Type -> TacticProvider)
    -> TacticProvider
filterBindingType p tp dflags plId uri range jdg =
  let hy = jHypothesis jdg
      g  = jGoal jdg
   in fmap join $ for (M.toList hy) $ \(occ, CType ty) ->
        case p (unCType g) ty of
          True  -> tp occ ty dflags plId uri range jdg
          False -> pure []


------------------------------------------------------------------------------
-- | Find the last typechecked module, and find the most specific span, as well
-- as the judgement at the given range.
judgementForHole
    :: IdeState
    -> NormalizedFilePath
    -> Range
    -> MaybeT IO (Range, Judgement, Context, DynFlags)
judgementForHole state nfp range = do
  (asts, amapping) <- MaybeT $ runIde state $ useWithStale GetHieAst nfp
  range' <- liftMaybe $ fromCurrentRange amapping range

  (binds, _) <- MaybeT $ runIde state $ useWithStale GetBindings nfp

  -- Ok to use the stale 'ModIface', since all we need is its 'DynFlags'
  -- which don't change very often.
  (modsum, _) <- MaybeT $ runIde state $ useWithStale GetModSummaryWithoutTimestamps nfp
  let dflags = ms_hspp_opts modsum

  (rss, goal) <- liftMaybe $ join $ listToMaybe $ M.elems $ flip M.mapWithKey (getAsts $ hieAst asts) $ \fs ast ->
      case selectSmallestContaining (rangeToRealSrcSpan (FastString.unpackFS fs) range') ast of
        Nothing -> Nothing
        Just ast' -> do
          let info = nodeInfo ast'
          ty <- listToMaybe $ nodeType info
          guard $ ("HsUnboundVar","HsExpr") `S.member` nodeAnnotations info
          pure (nodeSpan ast', ty)

  resulting_range <- liftMaybe $ toCurrentRange amapping $ realSrcSpanToRange rss
  (tcmod, _) <- MaybeT $ runIde state $ useWithStale TypeCheck nfp
  let tcg = fst $ tm_internals_ $ tmrModule tcmod
      ctx = mkContext
              (mapMaybe (sequenceA . (occName *** coerce))
                $ getDefiningBindings binds rss)
              tcg
      hyps = hypothesisFromBindings rss binds
  pure (resulting_range, mkFirstJudgement hyps goal, ctx, dflags)


tacticCmd :: KnownTacticCommand tc => proxy tc -> CommandFunction (TacticParams (TacticContext tc))
tacticCmd tac lf state (TacticParams uri range tacargs)
  | Just nfp <- uriToNormalizedFilePath $ toNormalizedUri uri =
      fromMaybeT (Right Null, Nothing) $ do
        (range', jdg, ctx, dflags) <- judgementForHole state nfp range
        let span = rangeToRealSrcSpan (fromNormalizedFilePath nfp) range'
        pm <- MaybeT $ useAnnotatedSource "tacticsCmd" state nfp
        case runTactic ctx jdg $ commandTactic tac tacargs of
          Left err ->
            pure $ (, Nothing)
              $ Left
              $ ResponseError InvalidRequest (T.pack $ show err) Nothing
          Right res -> do
            let g = graft (RealSrcSpan span) res
                response = transform dflags (clientCapabilities lf) uri g pm
            pure $ case response of
               Right res -> (Right Null , Just (WorkspaceApplyEdit, ApplyWorkspaceEditParams res))
               Left err -> (Left $ ResponseError InternalError (T.pack err) Nothing, Nothing)
tacticCmd _ _ _ _ =
  pure ( Left $ ResponseError InvalidRequest (T.pack "Bad URI") Nothing
       , Nothing
       )


fromMaybeT :: Functor m => a -> MaybeT m a -> m a
fromMaybeT def = fmap (fromMaybe def) . runMaybeT

liftMaybe :: Monad m => Maybe a -> MaybeT m a
liftMaybe a = MaybeT $ pure a

