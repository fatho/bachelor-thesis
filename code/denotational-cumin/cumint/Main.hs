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
import qualified Control.Monad.Logic                   as Logic
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Either
import           Data.Default.Class
import qualified Data.Set                              as Set
import qualified System.Console.GetOpt                 as GetOpt
import           System.CPUTime                        (getCPUTime)
import qualified System.Environment                    as Env
import qualified Text.PrettyPrint.ANSI.Leijen          as PP
import           Text.Printf                           (printf)
import           Text.Trifecta

import qualified FunLogic.Core.Repl                    as Repl
import qualified FunLogic.Semantics.Pruning            as Pruning
import qualified FunLogic.Semantics.Search             as Search
import qualified Language.CuMin.Semantics.Denotational as Denot

import qualified Language.CuMin.AST                    as CuMin
import qualified Language.CuMin.ModBuilder             as CuMin
import qualified Language.CuMin.Parser                 as CuMin
import qualified Language.CuMin.Prelude                as CuMin
import qualified Language.CuMin.Pretty                 as CuMin
import qualified Language.CuMin.TypeChecker            as CuMin

data CuminOpts = CuminOpts

-- | command line options
cmdOptions :: [GetOpt.OptDescr (Either [String] CuminOpts -> Either [String] CuminOpts)]
cmdOptions = []

-- | Parses command line options, calling the given continuation on success.
parseOptions :: (Applicative m, MonadIO m) => m (Either PP.Doc (CuminOpts, [FilePath]))
parseOptions = do
  (opts, files, errors) <- GetOpt.getOpt GetOpt.Permute cmdOptions <$> liftIO Env.getArgs
  prog <- liftIO Env.getProgName
  if null errors
    then case foldl (flip id) (Right CuminOpts) opts of
      Left msgs -> return $ Left $ PP.text "Invalid values:" PP.<$> PP.indent 2 (PP.vsep $ map PP.text msgs)
      Right o -> return $ Right (o, files)
    else return $ Left $ PP.text "Invalid options: "
      PP.<$> PP.indent 2 (PP.vsep $ map PP.text errors)
      PP.<$> PP.text (GetOpt.usageInfo prog [])

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
    $ CuMin.evalTC' $ do
        CuMin.unsafeIncludeModule CuMin.preludeModule
        CuMin.checkModule modul

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


-- | Monad with depth-first-search characteristics.
type DFSMonad = Search.UnFair Logic.Logic
-- | Monad with breadth-first-search characteristics.
type BFSMonad = Logic.Logic

-- | Wrapper for any evaluation with observable results.
data ObservableSet = forall m. (Search.Observable m) => ObservableSet (m (Denot.Value m))

-- | Evaluates a SaLT expression using the given strategy.
evalWithStrategy
          :: Repl.Strategy
          -> (forall m. (Search.MonadSearch m) => Denot.Eval m (Denot.Value m) )
          -> CuMin.Module -> Denot.StepIndex -> ObservableSet
evalWithStrategy Repl.DFS action modul idx = ObservableSet (Denot.runEval action modul idx :: DFSMonad (Denot.Value DFSMonad))
evalWithStrategy Repl.BFS action modul idx = ObservableSet (Denot.runEval action modul idx :: BFSMonad (Denot.Value BFSMonad))

-- | implements evaluation command
doEvaluate :: CuMin.Exp -> Repl.Command CuMinRepl
doEvaluate expr = Repl.alwaysContinue $
  checkInteractiveExpr expr >>= \case
    Left tyerr -> Repl.putDocLn $ PP.pretty tyerr
    Right _   -> do
      interactiveMod <- use Repl.replModule
      strategy       <- use Repl.replEvalStrategy
      stepIndex      <- use Repl.replStepMode
      startTime      <- liftIO getCPUTime
      case evalWithStrategy strategy (Denot.eval expr) interactiveMod stepIndex of
        ObservableSet resultSet -> displayResults $ Search.observeAll resultSet
      endTime        <- liftIO getCPUTime
      let elapsed = realToFrac (endTime - startTime) / 1000000000000 :: Double
      Repl.putDocLn $ PP.text "CPU time elapsed:" PP.<+> PP.dullyellow (PP.text $ printf "%.3f s" elapsed)

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
  parseOptions >>= \case
    Left msg -> Repl.putDocLn msg
    Right (_, files) ->
      Repl.runRepl files environment ()

-- | Incremental output of results.
displayResults :: [Denot.Value n] -> Repl.ReplInputM CuMinRepl ()
displayResults vals = do
  showTypeInst <- use Repl.replDisplayTypes
  Repl.displaySet (const $ Repl.putDocLn . Denot.prettyValue showTypeInst) 0 vals
