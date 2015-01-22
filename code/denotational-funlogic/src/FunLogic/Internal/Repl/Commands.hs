{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE MultiWayIf       #-}
module FunLogic.Internal.Repl.Commands
  ( builtinCommands
  , commandsByPrefix
  , doNothing
  , alwaysContinue
  ) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.IO.Class
import qualified Data.Char                    as Char
import qualified Data.List                    as List
import qualified Data.Map                     as M
import qualified Data.Text                    as Text
import qualified FunLogic.Core.AST            as FL
import qualified FunLogic.Core.Parser         as FL
import qualified FunLogic.Core.Pretty         as FL
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Text.Printf                  as Text
import           Text.Trifecta

import           FunLogic.Internal.Repl.General
import           FunLogic.Internal.Repl.Types

-- | Creates action that always continues the REPL execution.
alwaysContinue :: ReplM tag a -> Command tag
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
  views replCustomProperties (List.find ((== prop) . propName)) >>= \case
    Just (PropDesc _ _ pset _) -> pset val >>= \case
      StatusOK -> putDocLn $ PP.text "OK"
      StatusErr msg -> putDocLn msg
    Nothing -> putDocLn $ PP.red $ PP.text "unknown property"

-- | Shows the value of a property.
doGetProp :: String -> Command tag
doGetProp prop = alwaysContinue $
  views replCustomProperties (List.find ((== prop) . propName)) >>= \case
    Just (PropDesc _ pget _ _) -> pget >>= liftIO . putDocLn
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
    , CommandDesc "set" (doSetProp <$> propNameP <*> many anyChar) ["<property>", "<value>"] "Sets the value of a property"
    , CommandDesc "get" (doGetProp <$> propNameP) ["<property>"] "Reads the value of a property"
    , CommandDesc "help" (pure doShowHelp) [] "Prints this help message"
    , CommandDesc "load" (doLoadFile <$> pathParser) ["<filename>"] "Loads a module from a file."
    ]
  where
    propNameP = token $ many $ Char.toLower <$> letter
    pathParser = stringLiteral <|> (strip <$> many anyChar)
    strip = Text.unpack . Text.strip . Text.pack

-- | Returns a list of commands having "cmd" as prefix.
commandsByPrefix :: String -> [ CommandDesc tag ] -> [ CommandDesc tag ]
commandsByPrefix cmd = filter (List.isPrefixOf cmd . cmdName)

