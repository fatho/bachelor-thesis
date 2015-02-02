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
import qualified Control.Monad.Logic.Class.Extended   as LogicExt
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Either
import           Data.Default.Class
import qualified Data.Set                             as Set
import qualified Text.PrettyPrint.ANSI.Leijen         as PP
import           Text.Trifecta

import qualified FunLogic.Core.Repl                   as Repl
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
cuminLoader :: FilePath -> IO (Either PP.Doc SaLT.Module)
cuminLoader filePath = runEitherT $ do
  modul <- EitherT $ SaLT.buildModuleFromFile filePath
  bimapEitherT PP.pretty (const modul) $ hoistEither
    $ SaLT.evalTC (SaLT.unsafeIncludeModule SaLT.preludeModule >> SaLT.checkModule modul) def def

-- | REPL environment
environment :: Repl.ReplEnv SaLTRepl
environment = Repl.ReplEnv
  { Repl._replPrelude = interactivePrelude
  , Repl._replPrompt  = PP.blue (PP.text "{\x03BB}> ")
  , Repl._replLoader  = cuminLoader
  , Repl._replInspectDefinition = SaLT.prettyBinding
  , Repl._replCustomProperties = []
  , Repl._replCustomCommands = cuminReplCommands
  , Repl._replDefaultParse = runInteractive $ doEvaluate <$> parseExpression
  }

-- | implements :type command
doGetType :: SaLT.Exp -> Repl.Command SaLTRepl
doGetType expr = Repl.alwaysContinue $ checkInteractiveExpr expr >>= \case
  Left errMsg -> Repl.putDocLn $ PP.pretty errMsg
  Right ty -> Repl.putDocLn $ SaLT.prettyType ty

-- | A value with observable results of non-determinism.
data ObservableValue = forall m. (LogicExt.Observable m) => ObservableValue (Denot.Value m)

-- | Evaluates a SaLT expression using the given strategy.
evalWithMonad :: (Denot.NonDeterministic m, LogicExt.Observable m, Denot.StepIndex idx)
         => Repl.StrategyMonad m
         -> Denot.EvalExp idx m (Denot.Value m)
         -> SaLT.Module -> idx -> ObservableValue
evalWithMonad _ action modul idx = ObservableValue (Denot.runEval action modul idx)

-- | Evaluates a SaLT expression using the given strategy.
evalWithStrategy :: (Denot.StepIndex idx)
         => Repl.Strategy
         -> (forall m. (Denot.NonDeterministic m) => Denot.EvalExp idx m (Denot.Value m) )
         -> SaLT.Module -> idx -> ObservableValue
evalWithStrategy Repl.DFS action = evalWithMonad Repl.MonadDFS action
evalWithStrategy Repl.BFS action = evalWithMonad Repl.MonadBFS action

-- | implements evaluation command
doEvaluate :: SaLT.Exp -> Repl.Command SaLTRepl
doEvaluate expr = Repl.alwaysContinue $
  checkInteractiveExpr expr >>= \case
    Left tyerr -> Repl.putDocLn $ PP.pretty tyerr
    Right _   -> do
      interactiveMod <- use Repl.replModule
      strategy <- use Repl.replEvalStrategy
      let eval' :: (Denot.StepIndex idx) => idx -> ObservableValue
          eval' = evalWithStrategy strategy (Denot.eval expr) interactiveMod
      (ObservableValue result) <- uses Repl.replStepMode $ \case
        Repl.StepFixed n   -> eval' n
        Repl.StepUnlimited -> eval' Denot.Infinity
      displayValue 0 result

-- | SaLT specific REPL commands.
cuminReplCommands :: [Repl.CommandDesc SaLTRepl]
cuminReplCommands =
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
displayValue :: (LogicExt.Observable n) => Int -> Denot.Value n -> Repl.ReplInputM SaLTRepl ()
displayValue indent val = case val of
  Denot.VSet vset _ -> displayValueSet indent (LogicExt.observeAll vset)
  other -> Repl.putDocLn $ PP.pretty other

-- | Incremental output of results.
displayValueSet :: (LogicExt.Observable n) => Int -> [Denot.Value n] -> Repl.ReplInputM SaLTRepl ()
displayValueSet = Repl.displaySet displayValue
