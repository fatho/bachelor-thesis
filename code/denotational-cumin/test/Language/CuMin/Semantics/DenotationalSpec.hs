{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Language.CuMin.Semantics.DenotationalSpec where

import           Control.Applicative
import           Control.Monad
import qualified Control.Monad.Logic                   as Logic
import           Data.Functor.Identity
import           Data.Monoid
import           Test.Hspec
import qualified Test.Hspec.SmallCheck                 as HSC
import qualified Test.SmallCheck                       as SC
import qualified Test.SmallCheck.Series                as SC
import qualified Text.PrettyPrint.ANSI.Leijen          as PP

import qualified FunLogic.Semantics.Denotational       as Core
import qualified FunLogic.Semantics.PartialOrder       as PO
import qualified FunLogic.Semantics.Search             as Search
import qualified Language.CuMin.AST                    as CuMin
import qualified Language.CuMin.Parser                 as CuMin
import qualified Language.CuMin.Prelude                as CuMin
import qualified Language.CuMin.Pretty                 as CuMin
import qualified Language.CuMin.TypeChecker            as CuMin
import qualified Language.CuMin.Semantics.Denotational as CuMin
import qualified Language.CuMin.TH                     as CuMin

docStr :: PP.Doc -> String
docStr = flip PP.displayS "" . PP.renderPretty 0.9 80 . PP.plain

-- | Generates all possible lists containing _|_ and 0.
natList :: Monad m => SC.Series m (CuMin.Value n)
natList = SC.decDepthChecked (pure $ CuMin.VBot "") $ bot SC.\/ nil SC.\/ cons where
  bot  = pure $ CuMin.VBot ""
  nil  = pure $ CuMin.VCon "Nil" [] [CuMin.TNat]
  bin  = bot <|> pure (CuMin.VNat 0) -- <|> pure (CuMin.VNat 1)
  cons = bin SC.>>- \x -> natList SC.>>- \xs ->
    return $ CuMin.VCon "Cons" [x, xs] [CuMin.TNat]

natSeries :: Monad m => SC.Series m (CuMin.Value n)
natSeries = pure (CuMin.VBot "") <|> go 0 where
  go n = pure (CuMin.VNat n) <|> SC.decDepth (go $ n + 1)

prettyListAsSet :: [PP.Doc] -> PP.Doc
prettyListAsSet = PP.encloseSep PP.lbrace PP.rbrace PP.comma

-- | Checks if each element has a matching element from the other set that is at least as defined.
partiallyEqual :: PO.PartialOrd a => [a] -> [a] -> Bool
partiallyEqual as bs = (as `entailedBy` bs) && (bs `entailedBy` as) where

-- | Checks if for each element from the first list, there is an greater or equal element in the second list.
entailedBy :: PO.PartialOrd a => [a] -> [a] -> Bool
entailedBy xs ys = all (\x -> any (x `PO.leq`) ys) xs

-- | Expects that the expression has a valid type.
hasValidType :: CuMin.Exp -> Expectation
hasValidType expr = case CuMin.evalTC' $ do
  CuMin.includeBuiltIns
  CuMin.unsafeIncludeModule CuMin.preludeModule
  CuMin.checkExp expr of
    Left msg -> expectationFailure $ show $ PP.plain $ PP.pretty msg
    Right _ -> return ()

-- | Evaluates an expression with DFS and expects that it has a valid type.
dfsResults :: CuMin.Exp -> IO [CuMin.Value (Search.UnFair Logic.Logic)]
dfsResults expr = do
  let pexpr = CuMin.postProcessExp mempty expr
  hasValidType pexpr
  return $ Search.observeAll
    (CuMin.runEval (CuMin.eval pexpr)
                   CuMin.preludeModule (CuMin.StepNatural 10) id
     :: Search.UnFair Logic.Logic (CuMin.Value (Search.UnFair Logic.Logic)))

-- | Expects that the result of the evaluation is equivalent to the given set of values.
shouldEvalTo :: CuMin.Exp -> [CuMin.Value (Search.UnFair Logic.Logic)] -> Expectation
shouldEvalTo expr expected = do
    results <- dfsResults expr
    unless (expected `partiallyEqual` results) (raiseError results)
  where
      raiseError results = expectationFailure $ docStr $ PP.brackets (CuMin.prettyExp expr)
        PP.<+> PP.text "="
        PP.<+> prettyListAsSet (map PP.pretty results)
        PP.<+> PP.text "but expected"
        PP.<+> prettyListAsSet (map PP.pretty expected)

-- | Expects that the result of the evaluation should contain all given values.
shouldEvalToSuperset :: CuMin.Exp -> [CuMin.Value (Search.UnFair Logic.Logic)] -> Expectation
shouldEvalToSuperset expr expected = do
  results <- dfsResults expr
  unless (expected `entailedBy` results) raiseError
 where
    raiseError = expectationFailure $ docStr $ PP.brackets (CuMin.prettyExp expr)
      PP.<$> PP.text "is no superset (by the partial ordering) of"
      PP.<$> prettyListAsSet (map PP.pretty expected)

spec :: Spec
spec = do
  describe "base cases of interpreter" $ do
    it "addition" $ do
      [CuMin.cuminExp| 1 + 1 |]                         `shouldEvalTo` [Core.naturalValue 2]
      [CuMin.cuminExp| failed<:Nat:> + 1 |]             `shouldEvalTo` [Core.bottomValue ""]
      [CuMin.cuminExp| 1 + failed<:Nat:> |]             `shouldEvalTo` [Core.bottomValue ""]
      [CuMin.cuminExp| failed<:Nat:> + failed<:Nat:> |] `shouldEvalTo` [Core.bottomValue ""]
    it "comparison (Nat)" $ do
      [CuMin.cuminExp| 1 == 1 |]                         `shouldEvalTo` [CuMin.boolValue True]
      [CuMin.cuminExp| failed<:Nat:> == 1 |]             `shouldEvalTo` [Core.bottomValue ""]
      [CuMin.cuminExp| 1 == failed<:Nat:> |]             `shouldEvalTo` [Core.bottomValue ""]
      [CuMin.cuminExp| failed<:Nat:> == failed<:Nat:> |] `shouldEvalTo` [Core.bottomValue ""]
    it "comparison (Data)"
      pending
    it "let binding" $ do
      [CuMin.cuminExp| let x = 1 in x |]              `shouldEvalTo` [Core.naturalValue 1]
      [CuMin.cuminExp| let x = 1 in let x = 2 in x |] `shouldEvalTo` [Core.naturalValue 2]
      [CuMin.cuminExp| let y = 1 in let x = 2 in y |] `shouldEvalTo` [Core.naturalValue 1]
    it "free let variables" $ do
      [CuMin.cuminExp| let x :: Bool free in x |] `shouldEvalTo` fmap CuMin.boolValue [False,True]
      [CuMin.cuminExp| let x :: Nat free in x |] `shouldEvalToSuperset` fmap Core.naturalValue [1..10]
    it "failed" $ do
      [CuMin.cuminExp| failed<:Nat:> |]  `shouldEvalTo` [Core.bottomValue ""]
      [CuMin.cuminExp| failed<:Bool:> |] `shouldEvalTo` [Core.bottomValue ""]
    it "case" $ do
      [CuMin.cuminExp| case failed<:Bool:> of { True -> 1; False -> 2 } |] `shouldEvalTo` [Core.bottomValue ""]
      [CuMin.cuminExp| case True of { True -> 1; False -> 2 } |]           `shouldEvalTo` [Core.naturalValue 1]
      [CuMin.cuminExp| case False of { True -> 1; False -> 2 } |]          `shouldEvalTo` [Core.naturalValue 2]
    it "function application" $ do
      [CuMin.cuminExp| id<:Nat:> failed<:Nat:> |] `shouldEvalTo` [Core.bottomValue ""]
      [CuMin.cuminExp| id<:Nat:> 1 |]             `shouldEvalTo` [Core.naturalValue 1]

  describe "prelude behaves correctly" $ do
    it "addition with choose" $
      [CuMin.cuminExp| 1 + choose<:Nat:> 1 2 |] `shouldEvalTo` [Core.naturalValue 2, Core.naturalValue 3]
    it "tuples" $ do
      [CuMin.cuminExp| fst<:Nat,Nat:> (Pair<:Nat,Nat:> 1 2) |] `shouldEvalTo` [Core.naturalValue 1]
      [CuMin.cuminExp| snd<:Nat,Nat:> (Pair<:Nat,Nat:> 1 2) |] `shouldEvalTo` [Core.naturalValue 2]
    it "booleans" $ do
      [CuMin.cuminExp| and True True |]   `shouldEvalTo` [CuMin.boolValue True]
      [CuMin.cuminExp| and False True |]  `shouldEvalTo` [CuMin.boolValue False]
      [CuMin.cuminExp| and True False |]  `shouldEvalTo` [CuMin.boolValue False]
      [CuMin.cuminExp| and False False |] `shouldEvalTo` [CuMin.boolValue False]
      [CuMin.cuminExp| or True True |]    `shouldEvalTo` [CuMin.boolValue True]
      [CuMin.cuminExp| or False True |]   `shouldEvalTo` [CuMin.boolValue True]
      [CuMin.cuminExp| or True False |]   `shouldEvalTo` [CuMin.boolValue True]
      [CuMin.cuminExp| or False False |]  `shouldEvalTo` [CuMin.boolValue False]
      [CuMin.cuminExp| not True |]   `shouldEvalTo` [CuMin.boolValue False]
      [CuMin.cuminExp| not False |]  `shouldEvalTo` [CuMin.boolValue True]
    it "higher-order functions" $ do
      [CuMin.cuminExp| either<:Bool,Nat,Nat:> (const<:Nat,Bool:> 1) id<:Nat:> (Left<:Bool,Nat:> False) |]
        `shouldEvalTo` [Core.naturalValue 1]
      [CuMin.cuminExp| either<:Bool,Nat,Nat:> (const<:Nat,Bool:> 1) id<:Nat:> (Right<:Bool,Nat:> 2) |]
        `shouldEvalTo` [Core.naturalValue 2]
      [CuMin.cuminExp| maybe<:Nat,Bool:> False (const<:Bool,Nat:> True) Nothing<:Nat:> |]
        `shouldEvalTo` [CuMin.boolValue False]
      [CuMin.cuminExp| maybe<:Nat,Bool:> False (const<:Bool,Nat:> True) (Just<:Nat:> 1) |]
        `shouldEvalTo` [CuMin.boolValue True]

  describe "partial order of values" $ do
    it "`leq` is reflexive" $
      HSC.property $ SC.over natList $ \(a :: CuMin.Value Identity) -> a `PO.leq` a
    it "`leq` is anti-symmetric" $
      HSC.property $ SC.over natList $ \(a :: CuMin.Value Identity) ->
        SC.over natList $ \b -> (a `PO.leq` b) && (b `PO.leq` a) SC.==> (a == b)
    it "a `lt`  b <=> a `leq` b && a /= b" $
      HSC.property $ SC.over natList $ \(a :: CuMin.Value Identity) ->
        SC.over natList $ \b -> (a `PO.lt` b) == ((a `PO.leq` b) && (a /= b))
    it "a `leq` b <=> a `lt`  b || a == b" $
      HSC.property $ SC.over natList $ \(a :: CuMin.Value Identity) ->
        SC.over natList $ \b -> (a `PO.leq` b) == ((a `PO.lt` b) || (a == b))

