{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Language.SaLT.Semantics.DenotationalSpec where

import           Control.Applicative
import           Control.Monad
import qualified Control.Monad.Logic                  as Logic
import           Data.Functor.Identity
import           Data.Monoid
import           Test.Hspec
import qualified Test.Hspec.SmallCheck                as HSC
import qualified Test.SmallCheck                      as SC
import qualified Test.SmallCheck.Series               as SC
import qualified Text.PrettyPrint.ANSI.Leijen         as PP

import qualified FunLogic.Semantics.Denotational      as Core
import qualified FunLogic.Semantics.PartialOrder      as PO
import qualified FunLogic.Semantics.Search            as Search
import qualified Language.SaLT.AST                    as SaLT
import qualified Language.SaLT.Parser                 as SaLT
import qualified Language.SaLT.Prelude                as SaLT
import qualified Language.SaLT.Pretty                 as SaLT
import qualified Language.SaLT.Semantics.Denotational as SaLT
import qualified Language.SaLT.TH                     as SaLT
import qualified Language.SaLT.TypeChecker            as SaLT

docStr :: PP.Doc -> String
docStr = flip PP.displayS "" . PP.renderPretty 0.9 80 . PP.plain

-- | Generates all possible lists containing _|_ and 0.
natList :: Monad m => SC.Series m (SaLT.Value n)
natList = SC.decDepthChecked (pure $ SaLT.VBot "") $ bot SC.\/ nil SC.\/ cons where
  bot  = pure $ SaLT.VBot ""
  nil  = pure $ SaLT.VCon "Nil" [] [SaLT.TNat]
  bin  = bot <|> pure (SaLT.VNat 0) -- <|> pure (SaLT.VNat 1)
  cons = bin SC.>>- \x -> natList SC.>>- \xs ->
    return $ SaLT.VCon "Cons" [x, xs] [SaLT.TNat]

natSeries :: Monad m => SC.Series m (SaLT.Value n)
natSeries = pure (SaLT.VBot "") <|> go 0 where
  go n = pure (SaLT.VNat n) <|> SC.decDepth (go $ n + 1)

prettyListAsSet :: [PP.Doc] -> PP.Doc
prettyListAsSet = PP.encloseSep PP.lbrace PP.rbrace PP.comma

-- | Checks if each element has a matching element from the other set that is at least as defined.
partiallyEqual :: PO.PartialOrd a => [a] -> [a] -> Bool
partiallyEqual as bs = (as `entailedBy` bs) && (bs `entailedBy` as) where

-- | Checks if for each element from the first list, there is an greater or equal element in the second list.
entailedBy :: PO.PartialOrd a => [a] -> [a] -> Bool
entailedBy xs ys = all (\x -> any (x `PO.leq`) ys) xs


valuesEqual :: (Search.Observable m) => SaLT.Value m -> SaLT.Value m -> Bool
valuesEqual (SaLT.VSet vs u1) (SaLT.VSet ws u2) = u1 == u2 || (Search.observeAll vs `partiallyEqual` Search.observeAll ws)
valuesEqual x y = x == y

-- | Expects that the expression has a valid type.
hasValidType :: SaLT.Exp -> Expectation
hasValidType expr = case SaLT.evalTC' $ do
  SaLT.includeBuiltIns
  SaLT.unsafeIncludeModule SaLT.preludeModule
  SaLT.checkExp expr of
    Left msg -> expectationFailure $ show $ PP.plain $ PP.pretty msg
    Right _ -> return ()

-- | Evaluates an expression with DFS and expects that it has a valid type.
dfsResults :: SaLT.Exp -> IO (SaLT.Value (Search.UnFair Logic.Logic))
dfsResults expr = do
  let pexpr = SaLT.postProcessExp mempty expr
  hasValidType pexpr
  return (SaLT.runEval (SaLT.eval pexpr)
                   SaLT.preludeModule (SaLT.StepNatural 10) id
     :: SaLT.Value (Search.UnFair Logic.Logic))

-- | Expects that the result of the evaluation is equivalent to the given set of values.
shouldEvalTo :: SaLT.Exp -> SaLT.Value (Search.UnFair Logic.Logic) -> Expectation
shouldEvalTo expr expected = do
    result <- dfsResults expr
    unless (expected `valuesEqual` result) (raiseError result)
  where
      raiseError result = expectationFailure $ docStr $ PP.brackets (SaLT.prettyExp expr)
        PP.<+> PP.text "="
        PP.<+> PP.pretty result
        PP.<+> PP.text "but expected"
        PP.<+> PP.pretty expected

listToSet :: (Applicative n, MonadPlus n) => [SaLT.Value n] -> SaLT.Value n
listToSet xs = SaLT.mkSet $ msum $ fmap return xs

spec :: Spec
spec = do
  describe "base cases of interpreter" $ do
    it "addition" $ do
      [SaLT.saltExp| 1 + 1 |]                         `shouldEvalTo` Core.naturalValue 2
      [SaLT.saltExp| failed<:Nat:> + 1 |]             `shouldEvalTo` Core.bottomValue ""
      [SaLT.saltExp| 1 + failed<:Nat:> |]             `shouldEvalTo` Core.bottomValue ""
      [SaLT.saltExp| failed<:Nat:> + failed<:Nat:> |] `shouldEvalTo` Core.bottomValue ""
    it "comparison (Nat)" $ do
      [SaLT.saltExp| 1 == 1 |]                         `shouldEvalTo` SaLT.boolValue True
      [SaLT.saltExp| failed<:Nat:> == 1 |]             `shouldEvalTo` Core.bottomValue ""
      [SaLT.saltExp| 1 == failed<:Nat:> |]             `shouldEvalTo` Core.bottomValue ""
      [SaLT.saltExp| failed<:Nat:> == failed<:Nat:> |] `shouldEvalTo` Core.bottomValue ""
    it "comparison (Data)"
      pending
    it "lambdas" $ do
      [SaLT.saltExp| (\x :: Nat -> x) 1 |]              `shouldEvalTo` Core.naturalValue 1
      [SaLT.saltExp| (\x :: Nat -> \x :: Nat -> x) 1 2 |] `shouldEvalTo` Core.naturalValue 2
      [SaLT.saltExp| (\x :: Nat -> \y :: Nat -> x) 1 2 |] `shouldEvalTo` Core.naturalValue 1
    it "free let variables" $ do
      [SaLT.saltExp| unknown<:Bool:> |] `shouldEvalTo` listToSet (fmap SaLT.boolValue [False,True])
    it "failed" $ do
      [SaLT.saltExp| failed<:Nat:> |]  `shouldEvalTo` Core.bottomValue ""
      [SaLT.saltExp| failed<:Bool:> |] `shouldEvalTo` Core.bottomValue ""
    it "case" $ do
      [SaLT.saltExp| case failed<:Bool:> of { True -> 1; False -> 2 } |] `shouldEvalTo` Core.bottomValue ""
      [SaLT.saltExp| case True of { True -> 1; False -> 2 } |]           `shouldEvalTo` Core.naturalValue 1
      [SaLT.saltExp| case False of { True -> 1; False -> 2 } |]          `shouldEvalTo` Core.naturalValue 2
    it "function application" $ do
      [SaLT.saltExp| id<:Nat:> failed<:Nat:> |] `shouldEvalTo` Core.bottomValue ""
      [SaLT.saltExp| id<:Nat:> 1 |]             `shouldEvalTo` Core.naturalValue 1

  describe "prelude behaves correctly" $ do
    it "addition with choose" $
      [SaLT.saltExp| choose<:Nat:> {1} {2} >>= \n :: Nat -> {n + 1} |] `shouldEvalTo` listToSet [Core.naturalValue 2, Core.naturalValue 3]
    it "tuples" $ do
      [SaLT.saltExp| fst<:Nat,Nat:> (Pair<:Nat,Nat:> 1 2) |] `shouldEvalTo` Core.naturalValue 1
      [SaLT.saltExp| snd<:Nat,Nat:> (Pair<:Nat,Nat:> 1 2) |] `shouldEvalTo` Core.naturalValue 2
    it "booleans" $ do
      [SaLT.saltExp| and True True |]   `shouldEvalTo` SaLT.boolValue True
      [SaLT.saltExp| and False True |]  `shouldEvalTo` SaLT.boolValue False
      [SaLT.saltExp| and True False |]  `shouldEvalTo` SaLT.boolValue False
      [SaLT.saltExp| and False False |] `shouldEvalTo` SaLT.boolValue False
      [SaLT.saltExp| or True True |]    `shouldEvalTo` SaLT.boolValue True
      [SaLT.saltExp| or False True |]   `shouldEvalTo` SaLT.boolValue True
      [SaLT.saltExp| or True False |]   `shouldEvalTo` SaLT.boolValue True
      [SaLT.saltExp| or False False |]  `shouldEvalTo` SaLT.boolValue False
      [SaLT.saltExp| not True |]   `shouldEvalTo` SaLT.boolValue False
      [SaLT.saltExp| not False |]  `shouldEvalTo` SaLT.boolValue True
    it "higher-order functions" $ do
      [SaLT.saltExp| either<:Bool,Nat,Nat:> (const<:Nat,Bool:> 1) id<:Nat:> (Left<:Bool,Nat:> False) |]
        `shouldEvalTo` Core.naturalValue 1
      [SaLT.saltExp| either<:Bool,Nat,Nat:> (const<:Nat,Bool:> 1) id<:Nat:> (Right<:Bool,Nat:> 2) |]
        `shouldEvalTo` Core.naturalValue 2
      [SaLT.saltExp| maybe<:Nat,Bool:> False (const<:Bool,Nat:> True) Nothing<:Nat:> |]
        `shouldEvalTo` SaLT.boolValue False
      [SaLT.saltExp| maybe<:Nat,Bool:> False (const<:Bool,Nat:> True) (Just<:Nat:> 1) |]
        `shouldEvalTo` SaLT.boolValue True

  describe "partial order of values" $ do
    it "`leq` is reflexive" $
      HSC.property $ SC.over natList $ \(a :: SaLT.Value Identity) -> a `PO.leq` a
    it "`leq` is anti-symmetric" $
      HSC.property $ SC.over natList $ \(a :: SaLT.Value Identity) ->
        SC.over natList $ \b -> (a `PO.leq` b) && (b `PO.leq` a) SC.==> (a == b)
    it "a `lt`  b <=> a `leq` b && a /= b" $
      HSC.property $ SC.over natList $ \(a :: SaLT.Value Identity) ->
        SC.over natList $ \b -> (a `PO.lt` b) == ((a `PO.leq` b) && (a /= b))
    it "a `leq` b <=> a `lt`  b || a == b" $
      HSC.property $ SC.over natList $ \(a :: SaLT.Value Identity) ->
        SC.over natList $ \b -> (a `PO.leq` b) == ((a `PO.lt` b) || (a == b))

