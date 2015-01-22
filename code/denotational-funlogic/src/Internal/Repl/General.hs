{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Internal.Repl.General
  (
  -- * Module handling
    mergeModule
  , loadModule
  , reloadModules
  -- * Input handling
  , askInput
  , runInterruptible
  -- * Miscellaneous
  , putDocLn
  , resultToEither
  , while
  ) where

import           Control.Lens
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import qualified Data.List                    as List
import qualified Data.Map                     as M
import           Data.Monoid
import qualified System.Console.Haskeline     as Haskeline
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Text.Trifecta

import qualified FunLogic.Core.AST            as FL
import qualified FunLogic.Core.ModBuilder     as FL

import           Internal.Repl.Types

-- * Module handling

-- | Merges a module into the REPL module.
mergeModule :: (MonadRepl tag m) => TagModule tag -> m Status
mergeModule newMod = do
  replMod <- use replModule
  case replMod `FL.importUnqualified` newMod of
    Left (ambADTs, ambBinds) ->
      return $ StatusErr $ PP.red (PP.text "Ambigous names defined in") PP.<+> PP.text (newMod ^. FL.modName) PP.</>
        PP.indent 2 (
            PP.text "ADTs:" PP.<+> PP.encloseSep mempty mempty PP.comma (map PP.text $ M.keys ambADTs)
            PP.</> PP.text "Bindings:" PP.<+> PP.encloseSep mempty mempty PP.comma (map PP.text $ M.keys ambBinds)
          )
    Right merged -> do
      replModule .= merged
      return StatusOK

-- | Load a module into the REPL session.
loadModule :: (MonadRepl tag m) => FilePath -> m ()
loadModule filePath = do
  liftIO $ PP.putDoc $ PP.text "Loading " PP.<+> PP.dullyellow (PP.text filePath) PP.<+> PP.text "..."
  loader <- view replLoader
  liftIO (loader filePath) >>= \case
    Left msg -> putDocLn $ PP.red (PP.text "Error loading") PP.<+> PP.text filePath PP.</> msg
    Right modul -> mergeModule modul >>= \case
      StatusErr msg -> liftIO (putStrLn "") >> putDocLn msg
      StatusOK -> do
        putDocLn $ PP.dullgreen $ PP.text "Success!"
        replFiles %= List.union [filePath]

-- | Reload all modules.
reloadModules :: (MonadRepl tag m) => m ()
reloadModules = do
  -- reset global module
  view replPrelude >>= assign replModule
  -- reload files
  use replFiles >>= mapM_ loadModule

-- * Input handling

-- | Asks the user for a value until it is accepted or the standard input was closed.
askInput :: Haskeline.MonadException m => Prompt m a -> Haskeline.InputT m (Maybe a)
askInput prompt = askUntilValid where
  askUntilValid = Haskeline.getInputLine (show $ promptDoc prompt) >>= \case
    Nothing -> return Nothing
    Just input -> lift (promptParse prompt input) >>= \case
      Left msg -> putDocLn msg >> askUntilValid
      Right value -> return $ Just value

-- | Runs the first action. When Ctrl-C is pressed, the action is aborted using an asynchronous exception and the
-- second action will be run for recovery.
runInterruptible :: Haskeline.MonadException m => Haskeline.InputT m a -> Haskeline.InputT m a -> Haskeline.InputT m a
runInterruptible action handler = Haskeline.withInterrupt (Haskeline.handleInterrupt handler action)

-- * Miscellaneous

-- | PP.putDoc lifted to MonadIO. Also appends a linebreak to each printed document.
putDocLn :: MonadIO m => PP.Doc -> m ()
putDocLn = liftIO . PP.putDoc . (<> PP.line)

-- | Converts a trifecta result to Either.
resultToEither :: Result a -> Either PP.Doc a
resultToEither res = case res of
  Failure msg -> Left msg
  Success val -> Right val

-- | Run an action as long as it returns success.
while :: Monad m => m LoopAction -> m ()
while action = action >>= \case
  Continue -> while action
  Break -> return ()