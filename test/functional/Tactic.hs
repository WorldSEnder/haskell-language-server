{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}

module Tactic
  ( tests
  )
where

import           Control.Applicative.Combinators ( skipManyTill )
import           Control.Lens (view)
import           Control.Monad.IO.Class
import           Data.Aeson
import           Data.Foldable
import           Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Ide.Plugin.Tactic.TestTypes
import           Language.Haskell.LSP.Test
import           Language.Haskell.LSP.Types (ApplyWorkspaceEditRequest, Position(..) , Range(..) , CAResult(..))
import           Language.Haskell.LSP.Types.Lens (command, title, arguments)
import           Test.Hls.Util
import           Test.Tasty
import           Test.Tasty.HUnit
import           System.FilePath
import System.Directory (doesFileExist)
import Control.Monad (unless)


------------------------------------------------------------------------------
-- | Get a range at the given line and column corresponding to having nothing
-- selected.
--
-- NB: These coordinates are in "file space", ie, 1-indexed.
pointRange :: Int -> Int -> Range
pointRange
  (subtract 1 -> line)
  (subtract 1 -> col) =
    Range (Position line col) (Position line $ col + 1)


------------------------------------------------------------------------------
findCodeAction :: KnownTacticCommand tc => TCSing tc -> TacticContext tc -> [CAResult] -> Maybe CAResult
findCodeAction tac tacargs = find predicate
  where
    predicate (CACodeAction ca)
      | Just c <- view command ca
      , Just (toList -> (arg : _)) <- view arguments c
      , Success tacParams <- withSerializableContext tac $ fromJSON arg
      , withSerializableContext tac $ tac_args tacParams == tacargs
      , view title c == tacticTitle tac tacargs = True
    predicate _ = False

tests :: TestTree
tests = testGroup
  "tactic"
  [ mkTest
      "Produces intros code action"
      "T1.hs" 2 14
      [ (TestRig id IntrosS ())
      ]
  , mkTest
      "Produces destruct and homomorphism code actions"
      "T2.hs" 2 21
      [ (TestRig id DestructS "eab")
      , (TestRig id HomomorphismS "eab")
      ]
  , mkTest
      "Won't suggest homomorphism on the wrong type"
      "T2.hs" 8 8
      [ (TestRig not HomomorphismS "global")
      ]
  , mkTest
      "Won't suggest intros on the wrong type"
      "T2.hs" 8 8
      [ (TestRig not IntrosS ())
      ]
  , mkTest
      "Produces (homomorphic) lambdacase code actions"
      "T3.hs" 4 24
      [ (TestRig id HomomorphismLambdaCaseS ())
      , (TestRig id DestructLambdaCaseS ())
      ]
  , mkTest
      "Produces lambdacase code actions"
      "T3.hs" 7 13
      [ (TestRig id DestructLambdaCaseS ())
      ]
  , mkTest
      "Doesn't suggest lambdacase without -XLambdaCase"
      "T2.hs" 11 25
      [ (TestRig not DestructLambdaCaseS ())
      ]
  , goldenTest "GoldenIntros.hs"            2 8  IntrosS ()
  , goldenTest "GoldenEitherAuto.hs"        2 11 AutoS   ()
  , goldenTest "GoldenJoinCont.hs"          4 12 AutoS   ()
  , goldenTest "GoldenIdentityFunctor.hs"   3 11 AutoS   ()
  , goldenTest "GoldenIdTypeFam.hs"         7 11 AutoS   ()
  , goldenTest "GoldenEitherHomomorphic.hs" 2 15 AutoS   ()
  , goldenTest "GoldenNote.hs"              2 8  AutoS   ()
  , goldenTest "GoldenPureList.hs"          2 12 AutoS   ()
  , goldenTest "GoldenGADTDestruct.hs"      7 17 DestructS "gadt"
  , goldenTest "GoldenGADTAuto.hs"          7 13 AutoS   ()
  ]

data TestRig
  = forall tc. (KnownTacticCommand tc, FromJSON (TacticContext tc)) => TestRig
  { successJudgement :: Bool -> Bool
  -- ^ Use 'not' for actions that shouldnt be present, 'id' otherwise
  , tactic :: TCSing tc
  -- ^ The tactic that should be tried
  , tacticArgs :: TacticContext tc
  -- ^ A variable name to try the tactic for
  }

------------------------------------------------------------------------------
-- | Make a tactic unit test.
mkTest
    :: Foldable t
    => String  -- ^ The test name
    -> FilePath  -- ^ The file to load
    -> Int  -- ^ Cursor line
    -> Int  -- ^ Cursor columnn
    -> t TestRig -- ^ A collection of (un)expected code actions.
    -> TestTree
mkTest name fp line col ts =
  testCase name $ do
  runSession hieCommand fullCaps tacticPath $ do
    doc <- openDoc fp "haskell"
    actions <- getCodeActions doc $ pointRange line col
    for_ ts $ \TestRig {successJudgement = f, tactic = tc, tacticArgs = args} -> do
      let title = tacticTitle tc args
      liftIO $
        f (isJust $ findCodeAction tc args actions)
          @? ("Expected a code action with title " <> T.unpack title)


goldenTest :: KnownTacticCommand tc => FilePath -> Int -> Int -> TCSing tc -> TacticContext tc -> TestTree
goldenTest input line col tc args =
  testCase (input <> " (golden)") $ do
    runSession hieCommand fullCaps tacticPath $ do
      doc <- openDoc input "haskell"
      actions <- getCodeActions doc $ pointRange line col
      Just (CACodeAction (view command -> Just c)) <- pure $ findCodeAction tc args actions
      executeCommand c
      _resp :: ApplyWorkspaceEditRequest <- skipManyTill anyMessage message
      edited <- documentContents doc
      let expected_name = tacticPath </> input <.> "expected"
      -- Write golden tests if they don't already exist
      liftIO $ (doesFileExist expected_name >>=) $ flip unless $ do
        T.writeFile expected_name edited
      expected <- liftIO $ T.readFile expected_name
      liftIO $ edited @?= expected


tacticPath :: FilePath
tacticPath = "test/testdata/tactic"

