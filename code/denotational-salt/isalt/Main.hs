{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}
module Main where

import           Control.Applicative
import           Control.Lens
import qualified Control.Monad.Logic                  as Logic
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Either
import           Control.Monad.Reader
import           Data.Char                            (toLower)
import           Data.Default.Class
import qualified Data.Set                             as Set
import qualified System.Console.GetOpt                as GetOpt
import           System.CPUTime                       (getCPUTime)
import qualified System.Environment                   as Env
import qualified Text.PrettyPrint.ANSI.Leijen         as PP
import           Text.Printf                          (printf)
import           Text.Trifecta

import qualified FunLogic.Core.Repl                   as Repl
import qualified FunLogic.Semantics.Pruning           as Pruning
import qualified FunLogic.Semantics.Search            as Search
import qualified Language.SaLT.Semantics.Denotational as Denot

import qualified Language.SaLT                        as SaLT

import qualified Debug.Trace                          as Debug

data SaltOpts = SaltOpts
  { _optPrelude :: SaLT.Module
  } deriving (Show)

makeLenses ''SaltOpts

defaultOptions :: SaltOpts
defaultOptions = SaltOpts { _optPrelude = SaLT.preludeModule }

parsePreludeOpt :: String -> Either String SaLT.Module
parsePreludeOpt (map toLower->"salt") = Right SaLT.preludeModule
parsePreludeOpt (map toLower->"cumin") = Right SaLT.cuminPreludeModule
parsePreludeOpt (map toLower->"none") = Right $ SaLT.emptyModule "Empty"
parsePreludeOpt _ = Left "accepted values are 'salt', 'cumin' and 'none'"

combine :: Lens' a b -> (String -> Either String b) -> String -> Either [String] a -> Either [String] a
combine val parse str (Left errs) = Left $ either (:) (const id) (parse str) errs
combine val parse str (Right opts) = either (Left . pure) (\n -> Right (opts & val .~ n)) (parse str)

-- | command line options
cmdOptions :: [GetOpt.OptDescr (Either [String] SaltOpts -> Either [String] SaltOpts)]
cmdOptions =
  [GetOpt.Option "p" ["prelude"]
    (GetOpt.ReqArg (combine optPrelude parsePreludeOpt) "PRELUDE")
    "The prelude used by the REPL."
  ]

-- | Parses command line options, calling the given continuation on success.
parseOptions :: (Applicative m, MonadIO m) => m (Either PP.Doc (SaltOpts, [FilePath]))
parseOptions = do
  (opts, files, errors) <- GetOpt.getOpt GetOpt.Permute cmdOptions <$> liftIO Env.getArgs
  prog <- liftIO Env.getProgName
  if null errors
    then case foldl (flip id) (Right defaultOptions) opts of
      Left msgs -> return $ Left $ PP.text "Invalid values:" PP.<$> PP.indent 2 (PP.vsep $ map PP.text msgs)
      Right o -> return $ Right (o, files)
    else return $ Left $ PP.text "Invalid options: "
      PP.<$> PP.indent 2 (PP.vsep $ map PP.text errors)
      PP.<$> PP.text (GetOpt.usageInfo prog [])

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

-- | Load and type check a SaLT file.
saltLoader :: SaLT.Module -> FilePath -> IO (Either PP.Doc SaLT.Module)
saltLoader prelude filePath = runEitherT $ do
  modul <- EitherT $ SaLT.buildModuleFromFile filePath
  bimapEitherT PP.pretty (const modul) $ hoistEither
    $ SaLT.evalTC (SaLT.unsafeIncludeModule prelude >> SaLT.checkModule modul) def def

-- | REPL environment
environment :: SaLT.Module -> Repl.ReplEnv SaLTRepl
environment prelude = Repl.ReplEnv
  { Repl._replPrelude = prelude & SaLT.modName .~ "Interactive"
  , Repl._replPrompt  = PP.blue (PP.text "{\x03BB}> ")
  , Repl._replLoader  = saltLoader prelude
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

iterDeep :: Search.MonadSearch m => Denot.EvalExp m (Denot.Value m) -> Denot.EvalExp m (Denot.Value m)
iterDeep action = view Denot.stepIdx >>= go 1 where
  go idx stop
    | Denot.isZero stop = local (Denot.stepIdx .~ stop) action
    | otherwise         = local (Denot.stepIdx .~ Denot.StepNatural idx) action >>= \case
        Denot.VSet vs _ -> go (idx + 1) (Denot.decrement stop) >>= \case
            Denot.VSet rest _ -> return $ Denot.mkSet $ vs `mplus` rest
            _ -> error "not a set"
        _ -> error "not a set"
-- | Evaluates a SaLT expression using the given strategy.
evalWithStrategy
          :: Repl.Strategy
          -> (forall m. (Search.MonadSearch m) => Denot.EvalExp m (Denot.Value m) )
          -> (forall m. (Search.MonadSearch m) => Denot.PruningF m Denot.Value )
          -> SaLT.Module -> Denot.StepIndex -> ObservableValue
evalWithStrategy Repl.DFS action prune modul idx = ObservableValue (Denot.runEval action modul idx prune :: Denot.Value DFSMonad)
evalWithStrategy Repl.BFS action prune modul idx = ObservableValue (Denot.runEval action modul idx prune :: Denot.Value BFSMonad)
evalWithStrategy Repl.IterDFS action prune modul idx =
    ObservableValue (Denot.runEval (iterDeep action) modul idx prune :: Denot.Value DFSMonad)

pruneOf :: Search.MonadSearch n => Repl.Pruning -> Denot.PruningF n Denot.Value
pruneOf Repl.PruneNonMaximal = Pruning.pruneNonMaximal
pruneOf Repl.PruneDuplicates = Pruning.pruneDuplicates
pruneOf Repl.PruneNone       = id

isSet :: SaLT.Type -> Bool
isSet (SaLT.TCon "Set" _) = True
isSet _ = False

-- | implements evaluation command
doEvaluate :: SaLT.Exp -> Repl.Command SaLTRepl
doEvaluate expr = Repl.alwaysContinue $ do
  interactiveMod <- use Repl.replModule
  strategy       <- use Repl.replEvalStrategy
  stepIndex      <- use Repl.replStepMode
  pruning        <- use Repl.replPruning
  checkInteractiveExpr expr >>= \case
    Left tyerr -> Repl.putDocLn $ PP.pretty tyerr
    Right ty
       | strategy == Repl.IterDFS && not (isSet ty) ->
          Repl.putDocLn $ PP.red $ PP.text "Iterative deepening search is only available for set-typed values"
       | otherwise -> do
          startTime      <- liftIO getCPUTime
          case evalWithStrategy strategy (Denot.eval expr) (pruneOf pruning) interactiveMod stepIndex of
            ObservableValue result -> displayValue 0 result
          endTime        <- liftIO getCPUTime
          let elapsed = realToFrac (endTime - startTime) / 1000000000000 :: Double
          Repl.putDocLn $ PP.text "CPU time elapsed:" PP.<+> PP.dullyellow (PP.text $ printf "%.3f s" elapsed)

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
  parseOptions >>= \case
    Left msg -> Repl.putDocLn msg
    Right (opt, files) ->
      Repl.runRepl files (environment $ _optPrelude opt) ()

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
