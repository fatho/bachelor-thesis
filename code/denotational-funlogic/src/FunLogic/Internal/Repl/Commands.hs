{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE RankNTypes            #-}
module FunLogic.Internal.Repl.Commands
  ( builtinCommands
  , builtinProperties
  , commandsByPrefix
  , doNothing
  , alwaysContinue
  , mkProperty
  ) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.State.Class
import           Control.Monad.Trans
import qualified Data.Char                      as Char
import qualified Data.List                      as List
import qualified Data.Map                       as M
import qualified Data.Monoid                    as Monoid
import qualified Data.Text                      as Text
import qualified FunLogic.Core.AST              as FL
import qualified FunLogic.Core.Parser           as FL
import qualified FunLogic.Core.Pretty           as FL
import qualified Text.PrettyPrint.ANSI.Leijen   as PP
import qualified Text.Printf                    as Text
import           Text.Trifecta

import qualified FunLogic.Semantics.Denotational    as Denot
import           FunLogic.Internal.Repl.General
import           FunLogic.Internal.Repl.Types

-- | Creates action that always continues the REPL execution.
alwaysContinue :: ReplInputM tag a -> Command tag
alwaysContinue = (Continue <$)

-- | Quits the REPL.
doQuit :: Command tag
doQuit = liftIO (putStrLn "Bye bye!") >> return Break

-- | Reloads all modules.
doReload :: TagIsBinding tag => Command tag
doReload = alwaysContinue reloadModules

-- | Prints the definition of a top level declaration
doShowDefinition :: String -> Command tag
doShowDefinition name = alwaysContinue $ case name of
  [] -> putDocLn $ PP.red $ PP.text "name required"
  x0:_
    | Char.isUpper x0 -> use (replModule . FL.modADTs . at name) >>= \case
        Nothing  -> putDocLn $ PP.red $ PP.text $ Text.printf "ADT %s not found" name
        Just def -> putDocLn $ FL.prettyADT def
    | otherwise -> use (replModule . FL.modBinds . at name) >>= \case
        Nothing  -> putDocLn $ PP.red $ PP.text $ Text.printf "top-level binding %s not found" name
        Just bnd -> views replInspectDefinition ($ bnd) >>= putDocLn

-- | Prints a list of all top level definitions.
doListDefinitions :: TagIsBinding tag => Command tag
doListDefinitions = alwaysContinue $ do
  adts     <- use $ replModule . FL.modADTs . to M.elems
  bindings <- use $ replModule . FL.modBinds . to M.elems
  putDocLn $ PP.text "ADTs:"
    PP.<$> PP.indent 2 (PP.vcat $ map shortADT adts)
    PP.<$> PP.text "top-level bindings:"
    PP.<$> PP.indent 2 (PP.vcat $ map shortBinding bindings)

-- | Displays an ADT and its type arguments.
shortADT :: FL.ADT -> PP.Doc
shortADT (FL.ADT tycon tyvars _ _) = PP.text tycon PP.<+> PP.sep (map PP.text tyvars)

-- | Displays a binding with its type signature
shortBinding :: FL.IsBinding b => b -> PP.Doc
shortBinding bnd = PP.text (bnd ^. FL.bindingName) PP.<+> PP.text "::"
  PP.<+> PP.hang 2 (bnd ^. FL.bindingType . to FL.prettyTyDecl)

-- | Sets a property.
doSetProp :: String -> String -> Command tag
doSetProp prop val = alwaysContinue $
  views replCustomProperties (List.find ((List.isPrefixOf prop) . propName)) >>= \case
    Just (PropDesc _ _ pset _) -> lift (pset val) >>= \case
      StatusOK -> putDocLn $ PP.text "OK"
      StatusErr msg -> putDocLn msg
    Nothing -> putDocLn $ PP.red $ PP.text "unknown property"

-- | Shows the value of a property.
doGetProp :: Maybe String -> Command tag
doGetProp Nothing = alwaysContinue $ do
  props <- view replCustomProperties
  forM_ props $ \(PropDesc name pget _ _) -> do
    valDoc <- lift pget
    putDocLn $ PP.text name PP.<+> PP.text "=" PP.<+> valDoc
doGetProp (Just prop) = alwaysContinue $
  views replCustomProperties (List.find ((List.isPrefixOf prop) . propName)) >>= \case
    Just (PropDesc _ pget _ _) -> lift pget >>= putDocLn
    Nothing -> putDocLn $ PP.red $ PP.text "unknown property"

-- | Shows the help document
doShowHelp :: Command tag
doShowHelp = alwaysContinue $ use replHelpText >>= putDocLn

-- | Loads a module.
doLoadFile :: TagIsBinding tag => FilePath -> Command tag
doLoadFile path = alwaysContinue $ loadModule path

-- | Does nothing!
doNothing :: Command tag
doNothing = return Continue

-- | A list of supported REPL commands
builtinCommands :: TagIsBinding tag => [CommandDesc tag]
builtinCommands =
    [ CommandDesc "quit" (pure doQuit) [] "Exits the REPL"
    , CommandDesc "reload" (pure doReload) [] "Reloads all loaded modules"
    , CommandDesc "def" (doShowDefinition <$> (FL.varIdent <|> FL.conIdent)) ["<name>"] "Shows the definition of an ADT or top-level binding"
    , CommandDesc "list" (pure doListDefinitions) [] "Shows a list of all definitions"
    , CommandDesc "set" (doSetProp <$> propNameP <* skipOptional (symbolic '=') <*> many anyChar) ["<property>", "<value>"] "Sets the value of a property"
    , CommandDesc "get" (doGetProp <$> optional propNameP) ["<property>"] "Reads the value of a property"
    , CommandDesc "help" (pure doShowHelp) [] "Prints this help message"
    , CommandDesc "load" (doLoadFile <$> pathParser) ["<filename>"] "Loads a module from a file."
    ]
  where
    propNameP  = token $ some $ Char.toLower <$> letter
    pathParser = stringLiteral <|> (strip <$> many anyChar)
    strip      = Text.unpack . Text.strip . Text.pack

-- | Returns a list of commands having "cmd" as prefix.
commandsByPrefix :: String -> [ CommandDesc tag ] -> [ CommandDesc tag ]
commandsByPrefix cmd = filter (List.isPrefixOf cmd . cmdName)

-- | The list of properties built into the REPL.
builtinProperties :: (Functor m, MonadState (ReplState tag) m) => [PropDesc m]
builtinProperties =
    [ mkProperty "depth" replStepMode stepModeParser
        (PP.text "The initial step index used for evaluating the semantics"
         PP.<+> PP.text "(i.e. the maximum recursion depth, including the depth of values of free variables)."
         PP.<$> PP.text "Possible values are:"
         PP.<$> PP.indent 2
            (      PP.text "'n'     for a fixed evaluation depth"
            PP.<$> PP.text "'inf'   for an unlimited evaluation depth" ) )
    , mkProperty "numresults" replResultsPerStep (fromInteger <$> natural)
        (PP.text "The number of results in a set to be displayed at once.")
    , mkProperty "strategy" replEvalStrategy (parseAbbrev show [BFS, DFS])
        (PP.text "The evaluation strategy, either breadth-first (BFS) or depth-first (DFS).")
    ]

-- | Creates a property description from a lens into the 'ReplState' and a parser.
mkProperty :: (MonadState (ReplState tag) m, Functor m, PP.Pretty a)
    => String -> Lens' (ReplState tag) a -> Parser a -> PP.Doc -> PropDesc m
mkProperty name access parser = PropDesc name (uses access PP.pretty) readAndSet
  where
    readAndSet str = case parseString parser Monoid.mempty str of
      Failure msg -> return $ StatusErr msg
      Success mode -> StatusOK <$ (access .= mode)

stepModeParser :: Parser Denot.StepIndex
stepModeParser = choice
    [ Denot.StepNatural  <$> natural
    , Denot.StepInfinity <$  parseAbbrev id ["infinity"]
    ]
