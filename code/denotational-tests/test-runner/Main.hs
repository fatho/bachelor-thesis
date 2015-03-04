module Main where

import           Test.Hspec

import qualified Denotational.Test.Equiv as TestEquiv

main :: IO ()
main = hspec TestEquiv.spec
