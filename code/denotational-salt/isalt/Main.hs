{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
module Main where

import           Control.Applicative
import           Control.Lens
import qualified Control.Monad.Logic                   as Logic
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Either
import           Data.Default.Class
import qualified Data.Set                              as Set
import qualified Text.PrettyPrint.ANSI.Leijen          as PP
import           Text.Trifecta

import qualified FunLogic.Core.Repl                    as Repl
import qualified Language.SaLT.Semantics.Denotational as Denot

import qualified Language.SaLT.AST                    as SaLT
import qualified Language.SaLT.ModBuilder             as SaLT
import qualified Language.SaLT.Parser                 as SaLT
import qualified Language.SaLT.Prelude                as SaLT
import qualified Language.SaLT.Pretty                 as SaLT
import qualified Language.SaLT.TypeChecker            as SaLT

import qualified Debug.Trace                           as Debug

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

-- | implements evaluation command
doEvaluate :: SaLT.Exp -> Repl.Command SaLTRepl
doEvaluate expr = Repl.alwaysContinue $
  checkInteractiveExpr expr >>= \case
    Left tyerr -> Repl.putDocLn $ PP.pretty tyerr
    Right _   -> do
      interactiveMod <- use Repl.replModule
      --stepIndex      <- use replStepMax
      let stepIndex = Denot.Infinity --5 :: Integer
      --let resultValue = Denot.mapValueSet Omega.each Omega.runOmega $ Denot.runEval (Denot.eval expr) interactiveMod stepIndex
      let resultValue = Denot.mapValueSet undefined (Logic.observeMany 10) $ Denot.runEval (Denot.eval expr) interactiveMod stepIndex
      Repl.putDocLn $ PP.pretty resultValue

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
