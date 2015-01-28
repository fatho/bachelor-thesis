{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
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
import qualified Data.Maybe                            as Maybe
import qualified Data.Set                              as Set
import qualified Text.PrettyPrint.ANSI.Leijen          as PP
import           Text.Trifecta

import qualified FunLogic.Core.Repl                    as Repl
import qualified Language.CuMin.Semantics.Denotational as Denot

import qualified Language.CuMin.AST                    as CuMin
import qualified Language.CuMin.ModBuilder             as CuMin
import qualified Language.CuMin.Parser                 as CuMin
import qualified Language.CuMin.Prelude                as CuMin
import qualified Language.CuMin.Pretty                 as CuMin
import qualified Language.CuMin.TypeChecker            as CuMin

import qualified System.Console.Haskeline              as Haskeline

import qualified Debug.Trace                           as Debug

-- | Tag identifying the CuMin REPL.
data CuMinRepl

type instance Repl.TagBinding CuMinRepl = CuMin.Binding
type instance Repl.TagState CuMinRepl = ()

-- * CuMin specific REPL definitions

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

-- | The Prelude module with another name
interactivePrelude :: CuMin.Module
interactivePrelude = CuMin.preludeModule & CuMin.modName .~ "Interactive"

-- | Load and type check a CuMin file.
cuminLoader :: FilePath -> IO (Either PP.Doc CuMin.Module)
cuminLoader filePath = runEitherT $ do
  modul <- EitherT $ CuMin.buildModuleFromFile filePath
  bimapEitherT PP.pretty (const modul) $ hoistEither
    $ CuMin.evalTC (CuMin.unsafeIncludeModule CuMin.preludeModule >> CuMin.checkModule modul) def def

-- | REPL environment
environment :: Repl.ReplEnv CuMinRepl
environment = Repl.ReplEnv
  { Repl._replPrelude = interactivePrelude
  , Repl._replPrompt  = PP.blue (PP.text "\x22A2\x03BB> ")
  , Repl._replLoader  = cuminLoader
  , Repl._replInspectDefinition = CuMin.prettyBinding
  , Repl._replCustomProperties = []
  , Repl._replCustomCommands = cuminReplCommands
  , Repl._replDefaultParse = runInteractive $ doEvaluate <$> parseExpression
  }

-- | implements :type command
doGetType :: CuMin.Exp -> Repl.Command CuMinRepl
doGetType expr = Repl.alwaysContinue $ checkInteractiveExpr expr >>= \case
  Left errMsg -> Repl.putDocLn $ PP.pretty errMsg
  Right ty -> Repl.putDocLn $ CuMin.prettyType ty

-- | implements evaluation command
doEvaluate :: CuMin.Exp -> Repl.Command CuMinRepl
doEvaluate expr = Repl.alwaysContinue $
  checkInteractiveExpr expr >>= \case
    Left tyerr -> Repl.putDocLn $ PP.pretty tyerr
    Right _   -> do
      interactiveMod <- use Repl.replModule
      let eval' :: (Denot.NonDeterministic n, Denot.StepIndex idx) => idx -> n (Denot.Value n)
          eval' = Denot.runEval (Denot.eval expr) interactiveMod
      resultSet <- uses Repl.replStepMode $ \case
        Repl.StepFixed n   -> eval' n
        Repl.StepUnlimited -> eval' Denot.Infinity

      displayResults 10 $ Logic.observeAll resultSet

-- | CuMin specific REPL commands.
cuminReplCommands :: [Repl.CommandDesc CuMinRepl]
cuminReplCommands =
  [ Repl.CommandDesc "type" (runInteractive $ doGetType <$> parseExpression)
      ["<expression>"] "Prints the type of an expression"
  ]

-- | Run a CuMin parser with <interactive> name.
runInteractive :: CuMin.CuMinParser a -> Parser a
runInteractive = CuMin.runCuMinParser "<interactive>"

-- | Parses a CuMin expression and applies post-processing.
parseExpression :: CuMin.CuMinParser CuMin.Exp
parseExpression = CuMin.postProcessExp Set.empty <$> (whiteSpace *> CuMin.expression)

-- | Checks an expression entered in the interactive mode.
checkInteractiveExpr :: MonadState (Repl.ReplState CuMinRepl) m => CuMin.Exp -> m (Either (CuMin.TCErr CuMin.CuMinErrCtx) CuMin.Type)
checkInteractiveExpr expr = do
  interactiveMod <- use Repl.replModule
  return $ CuMin.evalTC' $ do
    CuMin.includeBuiltIns
    CuMin.unsafeIncludeModule interactiveMod
    CuMin.checkExp expr

-- | Gluing it all together.
main :: IO ()
main = do
  PP.putDoc header
  Repl.runRepl environment ()

-- | Incremental output of results.
displayResults :: Int -> [Denot.Value n] -> Repl.ReplInputM CuMinRepl ()
displayResults _         [] = return ()
displayResults blockSize results = Haskeline.outputStr "{ " >> go results where
  go [] = Haskeline.outputStrLn "}"
  go xs = do
    let (curBlock, rest) = splitAt blockSize xs
    Repl.putDocLn $ PP.encloseSep PP.empty PP.empty (PP.text ", ")
      (curBlock^..traverse.to PP.pretty)
    if null rest
      then go []
      else do
        mch <- Haskeline.getInputChar "More (y/n)? "
        Haskeline.outputStr ", "
        if Maybe.fromMaybe 'n' mch `elem` "yYjJ"
          then go rest
          else Haskeline.outputStr "... " >> go []
