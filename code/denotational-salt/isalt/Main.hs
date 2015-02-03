{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE UndecidableInstances      #-}
module Main where

import           Control.Applicative
import           Control.Lens
import qualified Control.Monad.Logic                  as Logic
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Either
import           Data.Default.Class
import qualified Data.Set                             as Set
import qualified Text.PrettyPrint.ANSI.Leijen         as PP
import           Text.Trifecta

import qualified FunLogic.Core.Repl                   as Repl
import qualified FunLogic.Semantics.Search            as Search
import qualified Language.SaLT.Semantics.Denotational as Denot

import qualified Language.SaLT.AST                    as SaLT
import qualified Language.SaLT.ModBuilder             as SaLT
import qualified Language.SaLT.Parser                 as SaLT
import qualified Language.SaLT.Prelude                as SaLT
import qualified Language.SaLT.Pretty                 as SaLT
import qualified Language.SaLT.TypeChecker            as SaLT

import qualified Debug.Trace                          as Debug

-- | Tag identifying the SaLT REPL.
data SaLTRepl

type instance Repl.TagBinding SaLTRepl = SaLT.Binding
type instance Repl.TagState SaLTRepl = ()

-- * SaLT specific REPL definitions

-- | Welcome message
header :: PP.Doc
header =  PP.text "      ___           ___           ___       ___     "
  PP.<$$> PP.text "     /\\  \\         /\\  \\         /\\__\\     /\\  \\    "
  PP.<$$> PP.text "    /::\\  \\       /::\\  \\       /:/  /     \\:\\  \\   "
  PP.<$$> PP.text "   /:/\\ \\  \\     /:/\\:\\  \\     /:/  /       \\:\\  \\  "
  PP.<$$> PP.text "  _\\:\\~\\ \\  \\   /::\\~\\:\\  \\   /:/  /        /::\\  \\ "
  PP.<$$> PP.text " /\\ \\:\\ \\ \\__\\ /:/\\:\\ \\:\\__\\ /:/__/        /:/\\:\\__\\"
  PP.<$$> PP.text " \\:\\ \\:\\ \\/__/ \\/__\\:\\/:/  / \\:\\  \\       /:/  \\/__/"
  PP.<$$> PP.text "  \\:\\ \\:\\__\\        \\::/  /   \\:\\  \\     /:/  /     "
  PP.<$$> PP.text "   \\:\\/:/  /        /:/  /     \\:\\  \\    \\/__/      "
  PP.<$$> PP.text "    \\::/  /        /:/  /       \\:\\__\\              "
  PP.<$$> PP.text "     \\/__/         \\/__/         \\/__/              "
  PP.<$$> PP.empty
  PP.<$$> PP.text "Welcome to the SaLT REPL. Enter :help for help."
  PP.<$$> PP.empty

-- | The Prelude module with another name
interactivePrelude :: SaLT.Module
interactivePrelude = SaLT.preludeModule & SaLT.modName .~ "Interactive"

-- | Load and type check a SaLT file.
saltLoader :: FilePath -> IO (Either PP.Doc SaLT.Module)
saltLoader filePath = runEitherT $ do
  modul <- EitherT $ SaLT.buildModuleFromFile filePath
  bimapEitherT PP.pretty (const modul) $ hoistEither
    $ SaLT.evalTC (SaLT.unsafeIncludeModule SaLT.preludeModule >> SaLT.checkModule modul) def def

-- | REPL environment
environment :: Repl.ReplEnv SaLTRepl
environment = Repl.ReplEnv
  { Repl._replPrelude = interactivePrelude
  , Repl._replPrompt  = PP.blue (PP.text "{\x03BB}> ")
  , Repl._replLoader  = saltLoader
  , Repl._replInspectDefinition = SaLT.prettyBinding
  , Repl._replCustomProperties = []
  , Repl._replCustomCommands = saltReplCommands
  , Repl._replDefaultParse = runInteractive $ doEvaluate <$> parseExpression
  }

-- | implements :type command
doGetType :: SaLT.Exp -> Repl.Command SaLTRepl
doGetType expr = Repl.alwaysContinue $ checkInteractiveExpr expr >>= \case
  Left errMsg -> Repl.putDocLn $ PP.pretty errMsg
  Right ty -> Repl.putDocLn $ SaLT.prettyType ty

-- | Monad with depth-first-search characteristics.
type DFSMonad = Search.UnFair Logic.Logic
-- | Monad with breadth-first-search characteristics.
type BFSMonad = Logic.Logic
-- | A value with observable results of non-determinism.
data ObservableValue = forall m. (Search.Observable m) => ObservableValue (Denot.Value m)

-- | Evaluates a SaLT expression using the given strategy.
evalWithStrategy
          :: Repl.Strategy
          -> (forall m. (Denot.NonDeterministic m) => Denot.EvalExp m (Denot.Value m) )
          -> SaLT.Module -> Denot.StepIndex -> ObservableValue
evalWithStrategy Repl.DFS action modul idx = ObservableValue (Denot.runEval action modul idx :: Denot.Value DFSMonad)
evalWithStrategy Repl.BFS action modul idx = ObservableValue (Denot.runEval action modul idx :: Denot.Value BFSMonad)

-- | implements evaluation command
doEvaluate :: SaLT.Exp -> Repl.Command SaLTRepl
doEvaluate expr = Repl.alwaysContinue $
  checkInteractiveExpr expr >>= \case
    Left tyerr -> Repl.putDocLn $ PP.pretty tyerr
    Right _   -> do
      interactiveMod <- use Repl.replModule
      strategy       <- use Repl.replEvalStrategy
      stepIndex      <- use Repl.replStepMode
      case evalWithStrategy strategy (Denot.eval expr) interactiveMod stepIndex of
        ObservableValue result -> displayValue 0 result

-- | SaLT specific REPL commands.
saltReplCommands :: [Repl.CommandDesc SaLTRepl]
saltReplCommands =
  [ Repl.CommandDesc "type" (runInteractive $ doGetType <$> parseExpression)
      ["<expression>"] "Prints the type of an expression"
  ]

-- | Run a SaLT parser with <interactive> name.
runInteractive :: SaLT.SaltParser a -> Parser a
runInteractive = SaLT.runSaltParser "<interactive>"

-- | Parses a SaLT expression and applies post-processing.
parseExpression :: SaLT.SaltParser SaLT.Exp
parseExpression = SaLT.postProcessExp Set.empty <$> (whiteSpace *> SaLT.expression)

-- | Checks an expression entered in the interactive mode.
checkInteractiveExpr :: MonadState (Repl.ReplState SaLTRepl) m => SaLT.Exp -> m (Either (SaLT.TCErr SaLT.SaltErrCtx) SaLT.Type)
checkInteractiveExpr expr = do
  interactiveMod <- use Repl.replModule
  return $ SaLT.evalTC' $ do
    SaLT.includeBuiltIns
    SaLT.unsafeIncludeModule interactiveMod
    SaLT.checkExp expr

-- | Gluing it all together.
main :: IO ()
main = do
  PP.putDoc header
  Repl.runRepl environment ()

-- | Displays a SaLT value, using 'displayValueSet' for set values.
displayValue :: (Search.Observable n) => Int -> Denot.Value n -> Repl.ReplInputM SaLTRepl ()
displayValue indent val = case val of
  Denot.VSet vset _ -> displayValueSet indent (Search.observeAll vset)
  other -> do
    showTypeInst <- use Repl.replDisplayTypes
    Repl.putDocLn $ Denot.prettyValue showTypeInst other

-- | Incremental output of results.
displayValueSet :: (Search.Observable n) => Int -> [Denot.Value n] -> Repl.ReplInputM SaLTRepl ()
displayValueSet = Repl.displaySet displayValue
