{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}
module Main where

import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Maybe

import qualified Data.Char                      as Char
import qualified Data.List                      as List

import qualified Data.Foldable                  as F
import qualified Data.Map                       as M
import qualified Data.Maybe                     as Maybe
import           Data.Monoid
import qualified System.Console.GetOpt          as GetOpt
import qualified System.Console.Haskeline       as Haskeline
import qualified System.Environment             as Env
import qualified Text.PrettyPrint.ANSI.Leijen   as PP
import qualified Text.Printf                    as Text
import qualified Text.Read                      as Text
import           Text.Trifecta

import qualified Denotational.CuMin.Interpreter as CuMin
import qualified Language.CuMin.AST             as CuMin
import qualified Language.CuMin.ModBuilder      as CuMin
import qualified Language.CuMin.Parser          as CuMin
import qualified Language.CuMin.Prelude         as CuMin
import qualified Language.CuMin.Pretty          as CuMin
import qualified Language.CuMin.TypeChecker     as CuMin

import qualified Debug.Trace                    as Debug

-- | Type of command line options
data Opt = NoOpt

-- | Type of interactive commands
data Command
  = CmdQuit     -- ^ quit the REPL
  | CmdReload -- ^ reload module files
  | CmdDef String -- ^ get the definition of the given identifier
  | CmdList     -- ^ list all identifiers
  | CmdEval CuMin.Exp -- ^ evaluate expression
  | CmdType CuMin.Exp -- ^ type of expression
  | CmdGet String     -- ^ display property value
  | CmdSet String String -- ^ set property value
  | CmdHelp -- ^ show help
  | CmdNoOp -- ^ do nothing

-- | Command parser with usage information
data CommandP = CommandP
  { cmdName      :: String
  , cmdArgParser :: CuMin.CuMinParser Command
  , cmdArgDescr  :: [String]
  , cmdDescr     :: String
  }

-- | Generic interface to properties
data ReplProp m = ReplProp
  { propName  :: String
  , propGet   :: m PP.Doc
  , propSet   :: String -> m Status
  , propDescr :: PP.Doc
  }

data Status = StatusOK | StatusErr PP.Doc

data ReplState
  = ReplState
  { _replMod     :: CuMin.Module
  , _replFiles   :: [FilePath]
  , _replStepMax :: Integer
  }

makeLenses ''ReplState

-- The REPL Monad uses Haskeline input facilities and needs to store some state.
type ReplM = Haskeline.InputT (StateT ReplState IO)

-- | This instance can only be defined with UndecidableInstances.
-- The 'MonadState' instances in the mtl are defined that way.
instance MonadState s m => MonadState s (Haskeline.InputT m) where
  state = lift . state

-- * Constants and definitions

-- | REPL prompt text
prompt :: PP.Doc
prompt = PP.blue (PP.text "\x22A2\x03BB> ")

-- | Welcome message
header :: PP.Doc
header = PP.text "  _____      __  __ _       "
  PP.<$$> PP.text " / ____|    |  \\/  (_)      "
  PP.<$$> PP.text "| |    _   _| \\  / |_ _ __  "
  PP.<$$> PP.text "| |   | | | | |\\/| | | '_ \\ "
  PP.<$$> PP.text "| |___| |_| | |  | | | | | |"
  PP.<$$> PP.text " \\_____\\__,_|_|  |_|_|_| |_|"
  PP.<$$> PP.line
  PP.<$$> PP.text "Welcome to the CuMin REPL. Enter :help for help."
  PP.<$$> PP.empty

-- | PP.putDoc lifted to MonadIO. Also appends a linebreak to each printed document.
putDoc :: MonadIO m => PP.Doc -> m ()
putDoc = liftIO . PP.putDoc . (<> PP.line)

-- | command line options
cmdOptions :: [GetOpt.OptDescr Opt]
cmdOptions = []

-- | Parses command line options, calling the given continuation on success.
parseOptions :: (([Opt], [FilePath]) -> IO ()) -> IO ()
parseOptions next = do
  (opts, files, errors) <- GetOpt.getOpt GetOpt.RequireOrder cmdOptions <$> Env.getArgs
  if null errors
    then next (opts, files)
    else do
      putStrLn "Invalid options: "
      mapM_ putStrLn errors
      prog <- Env.getProgName
      putStrLn $ GetOpt.usageInfo prog cmdOptions

main :: IO ()
main = do
  PP.putDoc header
  parseOptions loader

-- | mapM variant of mapMaybe.
mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM _ [] = return []
mapMaybeM f (x:xs) = f x >>= (`liftM` mapMaybeM f xs) . maybe id (:)

-- | Handles command line options and loads files.
loader :: ([Opt], [FilePath]) -> IO ()
loader (_, files) =  flip evalStateT (ReplState interactivePrelude files 10)
  $ Haskeline.runInputT Haskeline.defaultSettings
  $ reloadModules >> repl

-- | The Prelude module with another name
interactivePrelude :: CuMin.Module
interactivePrelude = CuMin.preludeModule & CuMin.modName .~ "Interactive"

-- | (Re)load all module files listed in the state.
reloadModules :: (MonadIO m, MonadState ReplState m) => m ()
reloadModules = do
    files <- use replFiles
    -- merge prelude and all modules passed via command line into one big module
    mergedMods <- liftIO $ F.foldrM loadNext interactivePrelude files
    -- typecheck the module
    case CuMin.evalTC' (CuMin.includeBuiltIns >> CuMin.checkModule mergedMods) of
      Left tcerr -> putDoc $ PP.pretty tcerr
      Right _ -> do
        replMod .= mergedMods
        liftIO $ putStrLn "Ready!"
  where
    -- load a module file and merge it with prevMod
    loadNext modFile prevMod = do
      Text.printf "Loading %s\n" modFile
      CuMin.buildModuleFromFile modFile >>= \case
        Right m -> mergeNext modFile m prevMod
        Left msg -> do
          PP.putDoc $ PP.red (PP.text "Error loading") PP.<+> PP.text modFile PP.</> msg
          return prevMod
    -- merges nextMod into prevMod. modFile is used for error messages.
    mergeNext modFile nextMod prevMod =
      case prevMod `CuMin.importUnqualified` nextMod of
        Left (ambADTs, ambBinds) -> do
          PP.putDoc $ PP.red (PP.text "Ambigous names defined in") PP.<+> PP.text modFile PP.</>
            PP.indent 2 (
                PP.text "ADTs:" PP.<+> PP.encloseSep mempty mempty PP.comma (map PP.text $ M.keys ambADTs)
                PP.</> PP.text "Bindings:" PP.<+> PP.encloseSep mempty mempty PP.comma (map PP.text $ M.keys ambBinds)
              )
          return prevMod
        Right merged -> return merged

-- | Runs the REPL.
repl :: ReplM ()
repl = while $ flip catchUserInterrupt interruptHandler $ do
    minput <- Haskeline.getInputLine (show prompt)
    result <- runMaybeT $ case minput of
      Nothing -> mzero -- end of input
      Just input -> case parseInputLine input of
        Failure msg -> putDoc msg
        Success cmd -> case cmd of
          -- evaluates an expression to a set of possible values
          CmdEval expr ->
            checkInteractiveExpr expr >>= \case
              Left tyerr -> putDoc $ PP.pretty tyerr
              Right _   -> do
                interactiveMod <- use replMod
                stepIndex      <- use replStepMax
                let resultSet = CuMin.runEval (CuMin.eval expr) interactiveMod stepIndex :: [CuMin.Value []]
                putDoc $ PP.encloseSep PP.lbrace PP.rbrace PP.comma
                  (resultSet^..traverse.to PP.pretty)
          -- determines the type of an expression
          CmdType expr ->
            checkInteractiveExpr expr >>= \case
              Left tyerr -> putDoc $ PP.pretty tyerr
              Right ty   -> putDoc $ CuMin.prettyType ty
          -- reload modules
          CmdReload -> reloadModules
          -- prints the definition of an ADT or top-level definition
          CmdDef name
            | null name -> putDoc $ PP.red $ PP.text "name required"
            | Char.isUpper (head name) -> use (replMod . CuMin.modADTs . at name) >>= \case
                Nothing  -> putDoc $ PP.red $ PP.text $ Text.printf "ADT %s not found" name
                Just def -> putDoc $ CuMin.prettyADT def
            | otherwise -> use (replMod . CuMin.modBinds . at name) >>= \case
                Nothing  -> putDoc $ PP.red $ PP.text $ Text.printf "top-level binding %s not found" name
                Just bnd -> putDoc $ CuMin.prettyBinding bnd
          -- lists all ADTs and top-level definitions in scope
          CmdList -> do
            adts     <- use $ replMod . CuMin.modADTs . to M.elems
            bindings <- use $ replMod . CuMin.modBinds . to M.elems
            putDoc $ PP.text "ADTs:"
              PP.<$> PP.indent 2 (PP.vcat $ map shortADT adts)
              PP.<$> PP.text "top-level bindings:"
              PP.<$> PP.indent 2 (PP.vcat $ map shortBinding bindings)
          CmdGet prop -> case List.find ((== prop) . propName) replProperties of
            Just (ReplProp _ pget _ _) -> pget >>= liftIO . putDoc
            Nothing -> putDoc $ PP.red $ PP.text "unknown property"
          CmdSet prop val -> case List.find ((== prop) . propName) replProperties of
            Just (ReplProp _ _ pset _) -> pset val >>= \case
              StatusOK -> putDoc $ PP.text "OK"
              StatusErr msg -> putDoc msg
            Nothing -> putDoc $ PP.red $ PP.text "unknown property"
          -- nomen est omen
          CmdHelp -> putDoc helpDoc
          CmdQuit -> do
            liftIO $ putStrLn "Bye Bye"
            mzero
          CmdNoOp -> return ()
    -- mzero --> False (exit), otherwise continue
    return $ Maybe.isJust result
  where
    -- Handler for Ctrl-C interruptions.
    interruptHandler = liftIO $ putStrLn "interrupted!" >> return True

-- | Parses a line of input to a 'Command'.
parseInputLine :: String -> Result Command
parseInputLine = parseString (CuMin.runCuMinParser "<interactive>" replLineParser) mempty

-- | Parser for a line of REPL input
replLineParser :: CuMin.CuMinParser Command
replLineParser = (defCommandParser <|> evalCommandParser <|> pure CmdNoOp) <* eof

-- | Parses an evaluation command (i.e. a CuMin expression)
evalCommandParser :: CuMin.CuMinParser Command
evalCommandParser = CmdEval <$> CuMin.expression

-- | Parses a command starting with ":", automatically selecting the right parser for the command arguments.
defCommandParser :: CuMin.CuMinParser Command
defCommandParser = char ':' >> CuMin.varIdent >>= \cmd -> case matchingCommands cmd of
  []  -> fail "Command not found!"
  [c] -> cmdArgParser c
  xs  -> fail $ "Ambigous command. Candidates are " ++ List.intercalate ", " (map cmdName xs)

-- | Returns a list of commands having "cmd" as prefix.
matchingCommands :: String -> [CommandP]
matchingCommands cmd = filter (List.isPrefixOf cmd . cmdName) replCommands

-- | Displays an ADT and its type arguments.
shortADT :: CuMin.ADT -> PP.Doc
shortADT (CuMin.ADT tycon tyvars _ _) = PP.text tycon PP.<+> PP.sep (map PP.text tyvars)

-- | Displays a binding with its type signature
shortBinding :: CuMin.Binding -> PP.Doc
shortBinding (CuMin.Binding f _ _ ty _) = PP.text f PP.<+> PP.text "::" PP.<+> PP.hang 2 (CuMin.prettyTyDecl ty)

-- | Runs a monadic action while it returns true
while :: Monad m => m Bool -> m ()
while action = action >>= flip when (while action)

-- | Checks an expression entered in the interactive mode.
checkInteractiveExpr :: MonadState ReplState m => CuMin.Exp -> m (Either (CuMin.TCErr CuMin.CuMinErrCtx) CuMin.Type)
checkInteractiveExpr expr = do
  interactiveMod <- use replMod
  return $ CuMin.evalTC' $ do
    CuMin.includeBuiltIns
    CuMin.unsafeIncludeModule interactiveMod
    CuMin.checkExp expr

-- | The message printed on ":help" command
helpDoc :: PP.Doc
helpDoc = PP.text "The following commands are supported:"
  PP.<$> PP.indent 2 (PP.vcat $ map helpCommand replCommands)
  PP.<$> PP.text "Command names can be abbreviated as long as it is unambigous (for example :t instead of :type)."
  PP.<+> PP.text "To evaluate an expression, simply enter it without any command."
  PP.<$> PP.empty
  PP.<$> PP.text "List of properties"
  PP.<$> PP.indent 2 (PP.vcat $ map helpProperty (replProperties :: [ReplProp (State ReplState)]))

-- | Generates a help entry for a command
helpCommand :: CommandP -> PP.Doc
helpCommand (CommandP name _ args msg) =
  PP.char ':' PP.<> PP.text name PP.<+> PP.fillSep (map PP.text args) PP.<$> PP.indent 2 (PP.text msg)

-- | Generates a help entry for a property
helpProperty :: ReplProp m -> PP.Doc
helpProperty (ReplProp name _ _ msg) =
  PP.char '*' PP.<+> PP.text name PP.<$> PP.indent 2 msg

-- | A list of supported REPL commands
replCommands :: [CommandP]
replCommands =
  [ CommandP "quit" (pure CmdQuit) [] "Exits the REPL"
  , CommandP "reload" (pure CmdReload) [] "Reloads all loaded modules"
  , CommandP "def" (CmdDef <$> (CuMin.varIdent <|> CuMin.conIdent)) ["<name>"] "Shows the definition of an ADT or top-level binding"
  , CommandP "list" (pure CmdList) [] "Shows a list of all definitions"
  , CommandP "type" (CmdType <$> CuMin.expression) ["<expression>"] "Prints the type of an expression"
  , CommandP "set" (CmdSet <$> propNameP <* symbol "=" <*> many anyChar) ["<property>", "=", "<value>"] "Sets the value of a property"
  , CommandP "get" (CmdGet <$> propNameP) ["<property>"] "Reads the value of a property"
  , CommandP "help" (pure CmdHelp) [] "Prints this help message"
  ]
  where
    propNameP :: CharParsing m => m String
    propNameP = many (Char.toLower <$> letter)

-- | A list of tunable properties
replProperties :: (Applicative m, MonadState ReplState m) => [ReplProp m]
replProperties =
  [ ReplProp "stepmax"
      (PP.text . show <$> use replStepMax)
      (\val -> case Text.readMaybe val of
         Just n | n > 0 -> StatusOK <$ (replStepMax .= n)
         _ -> return $ StatusErr $ PP.red $ PP.text "positive number expected" )
      (PP.text "The initial step index used for evaluating the semantics"
        PP.<+> PP.text "(i.e. the maximum recursion depth, including the depth of values of free variables).")
  ]

-- | Runs the first action. When Ctrl-C is pressed, the action is aborted using an asynchronous exception and the
-- second action will be run for recovery.
catchUserInterrupt :: Haskeline.MonadException m => Haskeline.InputT m a -> Haskeline.InputT m a -> Haskeline.InputT m a
catchUserInterrupt action handler =
  Haskeline.withInterrupt (Haskeline.handleInterrupt handler action)
