{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

module Ide.Plugin.Tactic.Context where

import Bag
import Control.Arrow
import Control.Monad.Reader
import Data.Coerce
import Data.Maybe (mapMaybe)
import Development.IDE.Core.RuleTypes (TcModuleResult, tmrModule)
import Development.IDE.GHC.Compat
import Development.IDE.GHC.Util (HscEnvEq, hscEnv)
import Development.IDE.Spans.LocalBindings (Bindings, getDefiningBindings)
import DsMonad (initDsTc)
import Ide.Plugin.Tactic.Types
import OccName
import TcRnTypes
import TcRnMonad (initTcWithGbl)


mkContext :: HscEnvEq -> Bindings -> TcModuleResult -> RealSrcSpan -> Context
mkContext hsenv binds tcmod rss
  = Context locals globals runTcM
  where
    tcg = fst $ tm_internals_ $ tmrModule tcmod  
    locals  = mapMaybe (sequenceA . (occName *** coerce))
            $ getDefiningBindings binds rss
    globals = fmap splitId
            $ (getFunBindId =<<)
            $ fmap unLoc
            $ bagToList
            $ tcg_binds
            $ tcg
    runTcM = \tcr -> do
      (_, Just r) <- initTcWithGbl (hscEnv hsenv) tcg rss tcr
      pure r


splitId :: Id -> (OccName, CType)
splitId = occName &&& CType . idType


getFunBindId :: HsBindLR GhcTc GhcTc -> [Id]
getFunBindId (AbsBinds _ _ _ abes _ _ _)
  = abes >>= \case
      ABE _ poly _ _ _ -> pure poly
      _ -> []
getFunBindId _ = []


getCurrentDefinitions :: MonadReader Context m => m [OccName]
getCurrentDefinitions = asks $ fmap fst . ctxDefiningFuncs

getModuleHypothesis :: MonadReader Context m => m [(OccName, CType)]
getModuleHypothesis = asks ctxModuleFuncs

runDsM :: (MonadReader Context m, MonadIO m) => DsM r -> m r
runDsM ds = do
  runner <- asks ctxRunDsM
  liftIO . runner $ initDsTc ds
