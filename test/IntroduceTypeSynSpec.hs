module IntroduceTypeSynSpec (main, spec) where


import Test.Hspec
import Language.Haskell.Refact.Refactoring.IntroduceTypeSyn

import TestUtils
import System.Directory

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do
  describe "doIntroduceTypeSyn" $ do
    it "Introduces a small synonym and modifies the type of a single function." $ do
      res <- ct $ introduceTypeSyn logTestSettings testCradle "./IntroduceTypeSyn/TS1.hs" (2,0) "Name" "String"
      r' <- ct $ mapM makeRelativeToCurrentDirectory res
      r' `shouldBe` ["./IntroduceTypeSyn/TS1.hs"]
      diff <- ct $ compareFiles "./IntroduceTypeSyn/TS1.refactored.hs"
                           "./IntroduceTypeSyn/TS1.hs.expected"
      diff `shouldBe` []
      
    it "Intruduces the synonym for a tuple and changes the type of two functions" $ do
      res <- ct $ introduceTypeSyn defaultTestSettings testCradle "./IntroduceTypeSyn/TS2.hs" (2,0) "Foo" "(String,Int)"
      r' <- ct $ mapM makeRelativeToCurrentDirectory res
      r' `shouldBe` ["./IntroduceTypeSyn/TS2.hs"]
      diff <- compareFiles "./IntroduceTypeSyn/TS2.refactored.hs"
                           "./IntroduceTypeSyn/TS2.hs.expected"
      diff `shouldBe` []
