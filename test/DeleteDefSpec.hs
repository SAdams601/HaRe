module DeleteDefSpec (main, spec) where


import Test.Hspec
import Language.Haskell.Refact.Refactoring.DeleteDef

import TestUtils

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do
  describe "doDeleteDef" $ do
    it "removes a small definition from the top level of a function" $ do
      res <- deleteDef (testSettingsMainfile "./test/testdata/DeleteDef/Dd1Client.hs") testCradle "./test/testdata/DeleteDef/Dd1.hs"  (5,1)
      (show res) `shouldBe` "[\"./test/testdata/DeleteDef/Dd1.hs\"]"
      diff <- compareFiles "./test/testdata/DeleteDef/Dd1.refactored.hs"
                           "./test/testdata/DeleteDef/Dd1.hs.expected"
      diff `shouldBe` []
    it "checks that a definition used in another module is not deleted" $ do
      res <- catchException (deleteDef (testSettingsMainfile "./test/testdata/DeleteDef/Dd2Client.hs") testCradle "./test/testdata/DeleteDef/Dd2.hs" (4,1))
      (show res) `shouldBe` "Just \"The def to be deleted is still being used\""
    it "checks that a definition used in the same module is not deleted" $ do
      res <- catchException (deleteDef defaultTestSettings testCradle "./test/testdata/DeleteDef/Dd3.hs" (4,1))
      (show res) `shouldBe` "Just \"The def to be deleted is still being used\""
    it "checks that a recursive definition can be deleted" $ do
      res <- deleteDef defaultTestSettings testCradle "./test/testdata/DeleteDef/Dd1.hs" (21,1)
      (show res) `shouldBe` "[\"./test/testdata/DeleteDef/Dd1.hs\"]"
      diff <- compareFiles "./test/testdata/DeleteDef/Dd1.refactored.hs"
                           "./test/testdata/DeleteDef/Dd1.hs.expected2"
      diff `shouldBe` []
