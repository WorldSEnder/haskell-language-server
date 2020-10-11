{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Ide.Plugin.Tactic.TestTypes
  ( TacticCommand (..),
    TacticParams(..),
    TCSing (..),
    TacticContext,
    KnownTacticCommand,
    ktcSing,
    ktcValue,
    tacticTitle,
    withSomeTacticCommand,
    withSerializableContext,
  )
where

import Data.Aeson hiding (defaultOptions)
import Data.Proxy
import qualified Data.Text as T
import Data.Type.Equality
import           GHC.Generics (Generic)
import           Language.Haskell.LSP.Types


data TacticParams args = TacticParams
    { file :: Uri -- ^ Uri of the file to fill the hole in
    , range :: Range -- ^ The range of the hole
    , tac_args :: args -- ^ Additional arguments to the tactic
    }
  deriving (Show, Eq, Generic, ToJSON, FromJSON)

------------------------------------------------------------------------------

-- | The list of tactics exposed to the outside world. These are attached to
-- actual tactics via 'commandTactic' and are contextually provided to the
-- editor via 'commandProvider'.
data TacticCommand
  = Auto
  | Intros
  | Destruct
  | Homomorphism
  | DestructLambdaCase
  | HomomorphismLambdaCase
  deriving (Eq, Ord, Show, Enum, Bounded)

data TCSing (tc :: TacticCommand) where
  AutoS :: TCSing 'Auto
  IntrosS :: TCSing 'Intros
  DestructS :: TCSing 'Destruct
  HomomorphismS :: TCSing 'Homomorphism
  DestructLambdaCaseS :: TCSing 'DestructLambdaCase
  HomomorphismLambdaCaseS :: TCSing 'HomomorphismLambdaCase

instance TestEquality TCSing where
  testEquality AutoS AutoS = Just Refl
  testEquality IntrosS IntrosS = Just Refl
  testEquality DestructS DestructS = Just Refl
  testEquality HomomorphismS HomomorphismS = Just Refl
  testEquality DestructLambdaCaseS DestructLambdaCaseS = Just Refl
  testEquality HomomorphismLambdaCaseS HomomorphismLambdaCaseS = Just Refl
  testEquality _ _ = Nothing

class KnownTacticCommand (tc :: TacticCommand) where
  tcReflect :: TCSing tc

instance KnownTacticCommand 'Auto where
  tcReflect = AutoS

instance KnownTacticCommand 'Intros where
  tcReflect = IntrosS

instance KnownTacticCommand 'Destruct where
  tcReflect = DestructS

instance KnownTacticCommand 'Homomorphism where
  tcReflect = HomomorphismS

instance KnownTacticCommand 'DestructLambdaCase where
  tcReflect = DestructLambdaCaseS

instance KnownTacticCommand 'HomomorphismLambdaCase where
  tcReflect = HomomorphismLambdaCaseS

ktcSing :: KnownTacticCommand tc => proxy tc -> TCSing tc
ktcSing _ = tcReflect

ktcValue :: KnownTacticCommand tc => proxy tc -> TacticCommand
ktcValue p = case ktcSing p of
  AutoS -> Auto
  IntrosS -> Intros
  DestructS -> Destruct
  HomomorphismS -> Homomorphism
  DestructLambdaCaseS -> DestructLambdaCase
  HomomorphismLambdaCaseS -> HomomorphismLambdaCase

withSomeTacticCommand :: TacticCommand -> (forall tc. KnownTacticCommand tc => Proxy tc -> r) -> r
withSomeTacticCommand Auto = ($ (Proxy :: Proxy 'Auto))
withSomeTacticCommand Intros = ($ (Proxy :: Proxy 'Intros))
withSomeTacticCommand Destruct = ($ (Proxy :: Proxy 'Destruct))
withSomeTacticCommand Homomorphism = ($ (Proxy :: Proxy 'Homomorphism))
withSomeTacticCommand DestructLambdaCase = ($ (Proxy :: Proxy 'DestructLambdaCase))
withSomeTacticCommand HomomorphismLambdaCase = ($ (Proxy :: Proxy 'HomomorphismLambdaCase))

type family TacticContext (tc :: TacticCommand) :: * where
  TacticContext 'Auto = ()
  TacticContext 'Intros = ()
  TacticContext 'Destruct = T.Text
  TacticContext 'Homomorphism = T.Text
  TacticContext 'DestructLambdaCase = ()
  TacticContext 'HomomorphismLambdaCase = ()

withSerializableContext
  :: KnownTacticCommand tc
  => proxy tc
  -> ((Eq (TacticContext tc), FromJSON (TacticContext tc), ToJSON (TacticContext tc)) => r) -> r
withSerializableContext = helper . ktcSing
  where
    helper :: TCSing tc -> ((Eq (TacticContext tc), FromJSON (TacticContext tc), ToJSON (TacticContext tc)) => r) -> r
    helper AutoS r = r
    helper IntrosS r = r
    helper DestructS r = r
    helper HomomorphismS r = r
    helper DestructLambdaCaseS r = r
    helper HomomorphismLambdaCaseS r = r

-- | Generate a title for the command.
tacticTitle :: KnownTacticCommand tc => proxy tc -> TacticContext tc -> T.Text
tacticTitle = mkTitle . ktcSing
  where
    mkTitle :: TCSing tc -> TacticContext tc -> T.Text
    mkTitle AutoS _ = "Attempt to fill hole"
    mkTitle IntrosS _ = "Introduce lambda"
    mkTitle DestructS var = "Case split on " <> var
    mkTitle HomomorphismS var = "Homomorphic case split on " <> var
    mkTitle DestructLambdaCaseS _ = "Lambda case split"
    mkTitle HomomorphismLambdaCaseS _ = "Homomorphic lambda case split"
