{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FunLogic.Internal.Repl.General
  (
  -- * Module handling
    mergeModule
  , loadModule
  , reloadModules
  -- * Input handling
  , askInput
  , runInterruptible
  -- * Output functions
  , displaySet
  -- * Miscellaneous
  , putDocLn
  , resultToEither
  , while
  , parseAbbrev
  ) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import qualified Data.Char                    as Char
import qualified Data.List                    as List
import qualified Data.Map                     as M
import           Data.Maybe
import           Data.Monoid
import qualified System.Console.Haskeline     as Haskeline
import qualified System.Console.Terminal.Size as Terminal
import qualified System.IO                    as IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Text.Trifecta

import qualified FunLogic.Core.AST            as FL
import qualified FunLogic.Core.ModBuilder     as FL

import           FunLogic.Internal.Repl.Types

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

-- | Prints a pretty-printer document to stdout with respect to the current terminal size.
putDocLn :: MonadIO m => PP.Doc -> m ()
putDocLn outDoc = liftIO $ do
  tsize <- fromMaybe (Terminal.Window 25 80) `liftM` Terminal.size
  PP.displayIO IO.stdout $ PP.renderPretty 0.8 (Terminal.width tsize) $ outDoc <> PP.line

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

-- | Generic function to display sets in an incremental way.
displaySet
  :: (Int -> v -> ReplInputM tag ())
  -- ^ Function to display an individual element. The first argument is the current indentation level.
  -- The current line is already indented, but each following line should be indented by that amount.
  -> Int
  -- ^ Initial indentation level.
  -> [v] -> ReplInputM tag ()
displaySet _     _   [] = return ()
displaySet printResult indent results = Haskeline.outputStr "{ " >> go results where
  prefix = List.replicate indent ' '
  putPrefix = Haskeline.outputStr prefix

  go [] = putPrefix >> Haskeline.outputStrLn "}"
  go xs = do
    nresults <- use replResultsPerStep
    let (curBlock, rest) = splitAt nresults xs
    sequence_ $ List.intersperse (putPrefix >> Haskeline.outputStr ", ") $ map (printResult $ indent + 2) curBlock
    if null rest
      then go []
      else do
        mch <- Haskeline.getInputChar "More (y/n)? "
        Haskeline.outputStr ", "
        if fromMaybe 'n' mch `elem` "yYjJ"
          then go rest
          else Haskeline.outputStr "... " >> go []


parseAbbrev :: (v -> String) -> [v] -> Parser v
parseAbbrev getKey values = (do
    let strLower = map Char.toLower
    name <- strLower <$> some letter
    case List.filter ((List.isPrefixOf name) . strLower . getKey) values of
      [] -> fail $ "Unknown value. Candidates: " ++ List.intercalate ", " (map getKey values)
      [x] -> return x
      multiple -> fail $ name ++ " is ambigous. Candidates are " ++ List.intercalate ", " (map getKey multiple)
  ) <?> "value"