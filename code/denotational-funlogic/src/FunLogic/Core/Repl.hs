{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE UndecidableInstances      #-}
module FunLogic.Core.Repl
  ( runRepl
  -- * REPL environment
  , Internal.ReplEnv (..)
  , Internal.replPrelude
  , Internal.replLoader
  , Internal.replPrompt
  , Internal.replCustomProperties
  , Internal.replCustomCommands
  , Internal.replInspectDefinition
  , Internal.replDefaultParse
  -- * REPL state
  , Internal.ReplState (..)
  , Internal.StepMode (..)
  , Internal.replModule
  , Internal.replFiles
  , Internal.replCustomState
  , Internal.replHelpText
  , Internal.replStepMode
  -- * Type families
  , Internal.TagBinding
  , Internal.TagState
  -- * Commands and properties
  , Internal.Command
  , Internal.ReplInputM
  , Internal.CommandDesc (..)
  , Internal.alwaysContinue
  , Internal.PropDesc (..)
  , Internal.mkProperty
  -- * Utility
  , Internal.putDocLn
  , Internal.displaySet
  ) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.List                       as List
import qualified Data.Maybe                      as Maybe
import           Data.Monoid
import qualified System.Console.GetOpt           as GetOpt
import qualified System.Console.Haskeline        as Haskeline
import qualified System.Environment              as Env
import qualified Text.PrettyPrint.ANSI.Leijen    as PP
import           Text.Trifecta

import           FunLogic.Internal.Repl.Commands as Internal
import           FunLogic.Internal.Repl.General  as Internal
import           FunLogic.Internal.Repl.Help     as Internal
import           FunLogic.Internal.Repl.Types    as Internal

-- | Specifies behavior in case of user interruption with Ctrl+C.
interruptionHandler :: ReplInputM tag LoopAction
interruptionHandler = do
  liftIO $ putStrLn "Interrupted!"
  return Continue

-- | command line options
cmdOptions :: [GetOpt.OptDescr CmdLineOpt]
cmdOptions = []

-- | Parses command line options, calling the given continuation on success.
parseOptions :: (Applicative m, MonadIO m) => m (Either PP.Doc ([CmdLineOpt], [FilePath]))
parseOptions = do
  (opts, files, errors) <- GetOpt.getOpt GetOpt.RequireOrder cmdOptions <$> liftIO Env.getArgs
  prog <- liftIO Env.getProgName
  if null errors
    then return $ Right (opts, files)
    else return $ Left $ PP.text "Invalid options: "
      PP.<$> PP.indent 2 (PP.vsep $ map PP.text errors)
      PP.<$> PP.text (GetOpt.usageInfo prog [])

-- | Build the initial REPL state from the environment
buildInitialState :: TagIsBinding tag => ReplEnv tag -> TagState tag -> ReplState tag
buildInitialState env cs = ReplState
  { _replModule       = env ^. replPrelude
  , _replFiles        = []
  , _replCustomState  = cs
  , _replHelpText     = buildHelpDoc (env ^. replCustomCommands) (env ^. replCustomProperties)
  , _replStepMode     = StepFixed 10
  }

-- | Start the REPL.
runRepl :: TagIsBinding tag => ReplEnv tag -> TagState tag -> IO ()
runRepl env cs = flip runReaderT envWithBuiltins
    $ flip evalStateT (buildInitialState envWithBuiltins cs)
    $ Haskeline.runInputT Haskeline.defaultSettings repl
  where
    envWithBuiltins = env
      & replCustomCommands   %~ (++ builtinCommands)
      & replCustomProperties %~ (++ builtinProperties)

-- | Run the loop.
repl :: TagIsBinding tag => ReplInputM tag ()
repl = parseOptions >>= \case
  Left msg -> putDocLn msg
  Right (_, files) -> do
    mapM_ loadModule files
    -- build prompt and run loop
    prompt <- Prompt <$> view replPrompt <*> pure parseInput
    let doIt = askInput prompt >>= Maybe.fromMaybe (return Break)
    while $ runInterruptible doIt interruptionHandler

-- | Parser for a line of REPL input
replLineParser :: [CommandDesc tag] -> Parser (Command tag) -> Parser (Command tag)
replLineParser cmds defaultParser = (defCommandParser cmds <|> defaultParser <|> pure doNothing) <* eof

-- | Parses a command starting with ":", automatically selecting the right parser for the command arguments.
defCommandParser :: [CommandDesc tag] -> Parser (Command tag)
defCommandParser cmds = char ':' >> commandName >>= \cmd -> case commandsByPrefix cmd cmds of
  []  -> fail "Command not found!"
  [c] -> cmdArgParser c
  xs  -> fail $ "Ambigous command. Candidates are " ++ List.intercalate ", " (map cmdName xs)

-- | Parses a command name (all letters)
commandName :: TokenParsing p => p String
commandName = token $ many letter

-- | Parses one line of input.
parseInput :: TagIsBinding tag => String -> ReplM tag (Either PP.Doc (Command tag))
parseInput input = do
  allCommands <- view replCustomCommands
  defaultParse <- view replDefaultParse
  return $ resultToEither $ parseString (replLineParser allCommands defaultParse) mempty input
