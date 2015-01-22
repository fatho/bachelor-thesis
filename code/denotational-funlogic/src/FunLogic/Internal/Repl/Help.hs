module FunLogic.Internal.Repl.Help
  ( buildHelpDoc
  , helpCommand
  , helpProperty
  ) where

import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           FunLogic.Internal.Repl.Types

-- | The message printed on ":help" command
buildHelpDoc :: [CommandDesc c] -> [PropDesc m] -> PP.Doc
buildHelpDoc cmds props = PP.text "The following commands are supported:"
  PP.<$> PP.indent 2 (PP.vcat $ map helpCommand cmds)
  PP.<$> PP.text "Command names can be abbreviated as long as it is unambigous (for example :t instead of :type)."
  PP.<+> PP.text "To evaluate an expression, simply enter it without any command."
  PP.<$> PP.empty
  PP.<$> PP.text "List of properties"
  PP.<$> PP.indent 2 (PP.vcat $ map helpProperty props)

-- | Generates a help entry for a command
helpCommand :: CommandDesc c -> PP.Doc
helpCommand (CommandDesc name _ args msg) =
  PP.char ':' PP.<> PP.text name PP.<+> PP.fillSep (map PP.text args) PP.<$> PP.indent 2 (PP.text msg)

-- | Generates a help entry for a property
helpProperty :: PropDesc m -> PP.Doc
helpProperty (PropDesc name _ _ msg) =
  PP.char '*' PP.<+> PP.text name PP.<$> PP.indent 2 msg
