{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Cont

import qualified Data.Char                      as Char

import qualified Data.Foldable                  as F
import qualified Data.Map                       as M
import           Data.Monoid
import qualified System.Console.GetOpt          as GetOpt
import           System.Console.Haskeline
import qualified System.Environment             as Env
import qualified Text.PrettyPrint.ANSI.Leijen   as PP
import           Text.Printf
import           Text.Trifecta

import           Denotational.CuMin.Interpreter as CuMin
import           FunLogic.Core.AST
import           FunLogic.Core.ModBuilder
import           FunLogic.Core.Parser
import           FunLogic.Core.Pretty
import           Language.CuMin.AST             as CuMin
import           Language.CuMin.ModBuilder      as CuMin
import           Language.CuMin.Pretty          as CuMin


-- | Type of command line options
data Opt = NoOpt

-- | Type of interactive commands
data Command
  = CmdQuit     -- ^ quit the REPL
  | CmdDef Name -- ^ get the definition of the given identifier
  | CmdList     -- ^ list all identifiers

data ReplState
  = ReplState
  { _replMod :: Module
  }

makeLenses ''ReplState

type ReplM = ContT () (StateT ReplState (InputT IO))

-- * Constants and definitions

-- | REPL prompt text
prompt :: PP.Doc
prompt = PP.blue (PP.text "\x03BB\x22A2> ")

header :: PP.Doc
header = PP.text "  _____      __  __ _       "
  PP.<$$> PP.text " / ____|    |  \\/  (_)      "
  PP.<$$> PP.text "| |    _   _| \\  / |_ _ __  "
  PP.<$$> PP.text "| |   | | | | |\\/| | | '_ \\ "
  PP.<$$> PP.text "| |___| |_| | |  | | | | | |"
  PP.<$$> PP.text " \\_____\\__,_|_|  |_|_|_| |_|"
  PP.<$$> PP.line


putDoc :: MonadIO m => PP.Doc -> m ()
putDoc = liftIO . PP.putDoc

-- | command line options
cmdOptions :: [GetOpt.OptDescr Opt]
cmdOptions = []

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

mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM _ [] = return []
mapMaybeM f (x:xs) = f x >>= (`liftM` mapMaybeM f xs) . maybe id (:)

loader :: ([Opt], [FilePath]) -> IO ()
loader (_, files) = do
    mergedMods <- F.foldrM loadNext (emptyModule "Interactive") files
    putStrLn "Ready!"
    runInputT defaultSettings $ flip evalStateT (ReplState mergedMods) $ runContT repl return
  where
    loadNext modFile prevMod = do
      printf "Loading %s\n" modFile
      buildModuleFromFile modFile >>= \case
        Right m -> case prevMod `importUnqualified` m of
          Left (ambADTs, ambBinds) -> do
            PP.putDoc $ PP.red (PP.text "Ambigous names defined in") PP.<+> PP.text modFile PP.</>
              PP.indent 2 (
                  PP.text "ADTs:" PP.<+> PP.encloseSep mempty mempty PP.comma (map PP.text $ M.keys ambADTs)
                  PP.</> PP.text "Bindings:" PP.<+> PP.encloseSep mempty mempty PP.comma (map PP.text $ M.keys ambBinds)
                )
            return prevMod
          Right merged -> return merged
        Left msg -> do
          PP.putDoc $ PP.red (PP.text "Error loading") PP.<+> PP.text modFile PP.</> msg
          return prevMod

repl :: ReplM ()
repl = callCC $ \exit -> forever $ do
    minput <- lift $ lift $ getInputLine (show prompt)
    case minput of
      Nothing -> exit ()
      Just (x:xs)
        | x == ':'  -> case parseCommand xs of
          Failure msg -> putDoc $ msg <> PP.line
          Success cmd -> case cmd of
            CmdDef name
              | null name -> putDoc $ PP.red $ PP.text "name required" <> PP.line
              | Char.isUpper (head name) -> use (replMod.modADTs.at name) >>= \case
                  Nothing  -> putDoc $ PP.red $ PP.text $ printf "ADT %s not found\n" name
                  Just def -> putDoc $ prettyADT def <> PP.line
              | otherwise -> use (replMod.modBinds.at name) >>= \case
                  Nothing  -> putDoc $ PP.red $ PP.text $ printf "top-level binding %s not found\n" name
                  Just def -> putDoc $ prettyBinding def <> PP.line
            CmdList -> do
              adts     <- use $ replMod.modADTs.to M.elems
              bindings <- use $ replMod.modBinds.to M.elems
              putDoc $ PP.text "ADTs:"
                PP.<$> PP.indent 2 (PP.vcat $ map shortADT adts)
                PP.<$> PP.text "top-level bindings:"
                PP.<$> PP.indent 2 (PP.vcat $ map shortBinding bindings)
                    <> PP.line
            CmdQuit -> do
              liftIO $ putStrLn "Bye Bye"
              exit ()
        | otherwise -> return () --parseExpr line
      Just _ -> return ()
  where
    parseCommand = parseString cmdParser mempty
    cmdParser = choice
      [ CmdQuit <$ anySymbol ["quit", "q"]
      , CmdDef <$> (anySymbol ["def", "d"] *> (varIdent <|> conIdent))
      , CmdList <$ anySymbol ["list", "l"]
      ]
    anySymbol = void . choice . map (try.symbol)

    shortADT (ADT tycon tyvars _ _) = PP.text tycon PP.<+> PP.sep (map PP.text tyvars)
    shortBinding (Binding f _ _ ty _) = PP.text f PP.<+> PP.text "::" PP.<+> PP.hang 2 (prettyTyDecl ty)
