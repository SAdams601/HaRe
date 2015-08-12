{-# LANGUAGE NamedFieldPuns #-}
module Language.Haskell.Refact.Refactoring.IntroduceTypeSyn where

import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB
import qualified GHC
import qualified Name as GHC
import qualified RdrName as GHC
import Control.Monad
import Language.Haskell.GhcMod
import Language.Haskell.Refact.API
import Data.Generics.Strafunski.StrategyLib.StrategyLib
import FastString
import Unique
import Lexer
import DynFlags
import StringBuffer
import Bag
import SrcLoc
import Outputable
import Language.Haskell.GhcMod
import Language.Haskell.GHC.ExactPrint.Types
import Language.Haskell.GHC.ExactPrint
import Language.Haskell.GHC.ExactPrint.Parsers
import qualified Data.Map as Map

introduceTypeSyn :: RefactSettings -> Cradle -> FilePath -> SimpPos -> String -> String -> IO [FilePath]
introduceTypeSyn settings cradle fileName (row,col) newName typeRep=
  runRefacSession settings defaultOptions [(Left fileName)] (comp fileName (row,col) newName typeRep)

comp ::FilePath -> SimpPos -> String -> String -> RefactGhc [ApplyRefacResult]
comp fileName (row,col) newName typeRep = do
  getModuleGhc fileName
  renamed <- getRefactRenamed
  ((refactoredMod@((_fp,ismod),(anns',parsed')),_))<- applyRefac (addSyn (row,col) newName typeRep fileName) RSAlreadyLoaded
  case ismod of
    RefacUnmodified -> error "Introduce type synonym failed"
    RefacModified -> return ()
  return [refactoredMod]
    
addSyn :: SimpPos -> String -> String -> FilePath -> RefactGhc ()
addSyn pos@(row, col) newName typeRep fileName = do
  parsed <- getRefactParsed
  let maybePn = locToName (row,col) parsed
  case maybePn of
    Just _ -> error "Introduce type synonym failed value already defined at source location"
    Nothing -> do
      let fullStr = "type " ++ newName ++ " = " ++ typeRep
          (modName, str) = gfromJust "Tried to get mod name" $ getModuleName parsed
          buff = stringToStringBuffer fullStr
      modSum <- GHC.getModSummary modName
      let newSum = modSum {GHC.ms_hspp_buf = Just buff}
      parsedMod <- GHC.parseModule newSum
      let fullStr = "type " ++ newName ++ " = " ++ typeRep
      Right (anns, mod@(GHC.L l unLocMod)) <- liftIO $ parseModule fileName
      (tyAs, tyMod, tydec) <- addTyDecl pos fullStr anns mod
      Right (_, oldType)  <- liftIO $ withDynFlags (\t -> parseType t (modNameFromMaybe $ GHC.hsmodName unLocMod) typeRep)
      Right res@(tyAnns, newNameTy)  <- liftIO $ withDynFlags (\t -> parseType t (modNameFromMaybe $ GHC.hsmodName unLocMod) newName)
      (finAs, finMod) <- renameSigs tyAs tyMod tydec res oldType
      putRefactParsed finMod finAs
      return ()
      
type Module = GHC.Located (GHC.HsModule GHC.RdrName)

addTyDecl :: SimpPos -> String -> Anns -> Module -> RefactGhc (Anns, Module, GHC.LHsDecl GHC.RdrName)
addTyDecl (row,col) tyDecl anns (GHC.L l mod) = do
  Right res@(decAnns, tydec) <- liftIO $ withDynFlags (\d -> parseDecl d (modNameFromMaybe $ GHC.hsmodName mod) tyDecl)
  let
      newAs = Map.union anns decAnns
      (before, (post:after)) = break findInsertPoint (GHC.hsmodDecls mod)
      Just Ann{annEntryDelta} = Map.lookup (mkAnnKey post) newAs
      finalAnns = Map.adjust (\decAnn -> decAnn { annEntryDelta = annEntryDelta }) (mkAnnKey tydec)
                . Map.adjust (\postAnn -> postAnn { annEntryDelta = DP (2, 0) }) (mkAnnKey post) $ newAs
      finalMod = mod { GHC.hsmodDecls = (tydec:(GHC.hsmodDecls mod)) }
  return (finalAnns, GHC.L l finalMod, tydec)
  where findInsertPoint (GHC.L l _)
          | newLoc <= (GHC.srcSpanStart l) = True
          | otherwise = False
        newLoc = GHC.mkSrcLoc (mkFastString "") row col

renameSigs :: Anns -> Module -> (GHC.LHsDecl GHC.RdrName) -> (Anns, GHC.LHsType GHC.RdrName) -> GHC.LHsType GHC.RdrName -> RefactGhc (Anns, Module)
renameSigs as (GHC.L l m) tydec@(GHC.L _ (GHC.TyClD tyCls)) (tyAs, newName) oldType = do
  let mDecls = GHC.hsmodDecls m
      (GHC.L _ clsName) = GHC.tcdLName tyCls     
  newModDecls <- SYB.everywhereM (SYB.mkM replaceSig) mDecls
  let newAs = Map.union as tyAs
    --  finalAs = Map.adjust ()
  return (newAs, (GHC.L l (m {GHC.hsmodDecls = newModDecls})))
  where
    tyRhs = GHC.tcdRhs tyCls
    replaceSig :: GHC.LHsType GHC.RdrName -> RefactGhc (GHC.LHsType GHC.RdrName)
    replaceSig lDecl@(GHC.L l (GHC.HsFunTy sig1 sig2))
      | compareHsType oldType sig1 = return (GHC.L l (GHC.HsFunTy newName sig2))
      | compareHsType oldType sig2 = return (GHC.L l (GHC.HsFunTy sig1 newName))
    replaceSig other = return other    

modNameFromMaybe :: Maybe (GHC.Located GHC.ModuleName) -> String
modNameFromMaybe (Just (GHC.L _ mn)) = GHC.moduleNameString mn
modNameFromMaybe Nothing = "template"

compareSig :: (GHC.LHsDecl GHC.RdrName) -> (GHC.LHsDecl GHC.RdrName) -> Bool
compareSig (GHC.L _ (GHC.SigD (GHC.TypeSig _ ty1 _))) (GHC.L _ (GHC.SigD (GHC.TypeSig _ ty2 _))) = True
compareSig _ _ = False

compareHsType :: (Eq a) => (GHC.LHsType a) -> (GHC.LHsType a) -> Bool
compareHsType (GHC.L _ (GHC.HsTyVar n1)) (GHC.L _ (GHC.HsTyVar n2)) = n1 == n2
compareHsType (GHC.L _ (GHC.HsTupleTy _ lst1)) (GHC.L _ (GHC.HsTupleTy _ lst2)) = compareTyList lst1 lst2
compareHsType _ _ = False

compareTyList :: (Eq a) => [GHC.LHsType a] -> [GHC.LHsType a] -> Bool
compareTyList [] [] = True
compareTyList (ty1:rst1) (ty2:rst2) = (compareHsType ty1 ty2) && (compareTyList rst1 rst2)
compareTyList _ _ = False
