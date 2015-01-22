{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
module FunLogic.Internal.Repl.Types
  ( Status (..)
  , LoopAction (..)
  -- * Tag related type families and constraints
  , TagBinding
  , TagState
  , TagModule
  , TagIsBinding
  -- * REPL types
  , MonadRepl
  , StateReaderT
  , ReplM
  , ReplInputM
  , CmdLineOpt
  , Prompt (..)
  -- * State and Environment
  , ReplState (..)
  , ReplEnv (..)
  -- * Lenses for ReplState
  , replModule
  , replFiles
  , replCustomState
  , replHelpText
  -- * Lenses for ReplEnv
  , replPrelude
  , replLoader
  , replPrompt
  , replCustomProperties
  , replCustomCommands
  , replInspectDefinition
  , replDefaultParse
  -- * Command and Property description
  , Command
  , CommandDesc (..)
  , PropDesc (..)
  ) where

import           Control.Lens
import           Control.Monad.IO.Class
import           Control.Monad.Reader
-- REMARK: Haskeline.MonadException is only predefined for State.Strict
import           Control.Monad.State.Strict
import qualified System.Console.Haskeline     as Haskeline
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Text.Trifecta

import qualified FunLogic.Core.AST            as FL

-- | Generic return type reporting either success or an error message.
data Status = StatusOK | StatusErr PP.Doc
  deriving (Show)

-- | Either 'Continue' the REPL loop or 'Break' it.
data LoopAction = Break | Continue
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

-- | Select language specific types by one tag type
type family TagBinding tag
type family TagState   tag

type TagModule tag = FL.CoreModule (TagBinding tag)
type TagIsBinding tag = FL.IsBinding (TagBinding tag)

-- | Effects needed for REPL.
type MonadRepl tag m = (MonadIO m, MonadState (ReplState tag) m, MonadReader (ReplEnv tag) m, FL.IsBinding (TagBinding tag))

-- | State and reader.
type StateReaderT s r m = StateT s (ReaderT r m)

-- | REPL state and environment cs
type ReplM tag = StateReaderT (ReplState tag) (ReplEnv tag) IO

-- | REPL with Haskeline
type ReplInputM tag = Haskeline.InputT (ReplM tag)

-- | Currently there are no command line options.
data CmdLineOpt

-- | A command is a monadic action returning whether the REPL should continue or exit.
type Command tag = ReplM tag LoopAction

-- | Command parser with usage information
data CommandDesc tag = CommandDesc
  { cmdName      :: String
  -- ^ name of the command used for calling. A command "foo" is called by ":foo"
  , cmdArgParser :: Parser (Command tag)
  -- ^ arbitrary parser for argument string
  , cmdArgDescr  :: [String]
  -- ^ human readable description of the arguments used for the help screen.
  , cmdDescr     :: String
  -- ^ human readable description of what the command does.
  }

-- | Generic interface to properties
data PropDesc m = PropDesc
  { propName  :: String
  -- ^ name of the property used with ":get" and ":set"
  , propShow  :: m PP.Doc
  -- ^ action used for displaying the property
  , propPut   :: String -> m Status
  -- ^ action used for parsing and storing the property
  , propDescr :: PP.Doc
  -- ^ human readable description of that the property controls.
  }

-- | Encapsulates a prompt.
data Prompt m a
  = Prompt
  { promptDoc   :: PP.Doc
  -- ^ prompt text
  , promptParse :: String -> m (Either PP.Doc a)
  -- ^ parses the user input
  }

-- | Internal state of the REPL.
data ReplState tag
  = ReplState
  { _replModule      :: FL.CoreModule (TagBinding tag)
  -- ^ module merged from all loaded modules
  , _replFiles       :: [FilePath]
  -- ^ loaded files
  , _replCustomState :: TagState tag
  -- ^ user defined state
  , _replHelpText    :: PP.Doc
  -- ^ repl help document
  }

-- | Environment of the REPL, passed from outside.
data ReplEnv tag
  = ReplEnv
  { _replPrelude           :: TagModule tag
  -- ^ prelude module to be always included
  , _replLoader            :: FilePath -> IO (Either PP.Doc (TagModule tag))
  -- ^ loaded for additional modules
  , _replPrompt            :: PP.Doc
  -- ^ prompt shown to user
  , _replCustomProperties  :: [PropDesc (ReplM tag)]
  -- ^ definition of custom properties
  , _replCustomCommands    :: [CommandDesc tag]
  -- ^ definition of custom commands
  , _replInspectDefinition :: TagBinding tag -> PP.Doc
  -- ^ should return the definition of a binding
  , _replDefaultParse      :: Parser (Command tag)
  -- ^ parse for everything that is no command
  }

makeLenses ''ReplState
makeLenses ''ReplEnv

-- | This instance can only be defined with UndecidableInstances.
-- The 'MonadState' instances in the mtl are defined that way.
instance MonadReader r m => MonadReader r (Haskeline.InputT m) where
  ask = lift ask
  reader = lift . reader
  local f = Haskeline.mapInputT (local f)

-- | This instance can only be defined with UndecidableInstances.
-- The 'MonadState' instances in the mtl are defined that way.
instance MonadState s m => MonadState s (Haskeline.InputT m) where
  state = lift . state