{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |

-- This module provides the primary interface to the combined
-- AST/Tokens, and the functions here will ensure that any changes are
-- properly synced and propagated.

module Language.Haskell.Refact.Utils.MonadFunctions
       (
       -- * Conveniences for state access

         fetchAnnsFinal
       , fetchToks -- Deprecated
       , getTypecheckedModule

       , getRefactStreamModified
       , setRefactStreamModified

       , getRefactInscopes

       , getRefactRenamed
       , putRefactRenamed

       , getRefactParsed
       , putRefactParsed

       -- * Annotations
       -- , addRefactAnns
       , setRefactAnns

       -- *
       , putParsedModule
       , clearParsedModule
       , getRefactFileName
       , getRefactTargetModule
       , getRefactModule
       , getRefactModuleName
       , getRefactNameMap

       -- * New ghc-exactprint interfacing
       , replaceRdrName
       , refactReplaceDecls
       , refactRunTransform
       , liftT

       -- * TokenUtils API
       , getToksForSpan

       -- * State flags for managing generic traversals
       , getRefactDone
       , setRefactDone
       , clearRefactDone

       , setStateStorage
       , getStateStorage

       -- * Parsing source
       , parseDeclWithAnns

       -- * Utility
       , nameSybQuery
       , fileNameFromModSummary

       , logDataWithAnns
       , logAnns
       , logParsedSource

       -- * For use by the tests only
       , initRefactModule
       , initTokenCacheLayout
       , initRdrNameMap
       ) where

import Control.Monad.State
-- import Control.Exception
import Data.List
import Data.Maybe

-- import qualified FastString    as GHC
import qualified GHC           as GHC
import qualified GhcMonad      as GHC

import qualified Data.Generics as SYB
-- import qualified GHC.SYB.Utils as SYB

import Language.Haskell.GHC.ExactPrint
import Language.Haskell.GHC.ExactPrint.Types
import Language.Haskell.GHC.ExactPrint.Parsers
-- import Language.Haskell.GHC.ExactPrint.Transform
import Language.Haskell.GHC.ExactPrint.Utils

import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.Types
import Language.Haskell.Refact.Utils.ExactPrint

import qualified Data.Map as Map
-- import Control.Applicative

-- ---------------------------------------------------------------------

-- |fetch the possibly modified tokens. Deprecated
fetchToks :: RefactGhc [PosToken]
fetchToks = do
  error $ "fetchToks no longer used"

-- |fetch the final annotations
fetchAnnsFinal :: RefactGhc Anns
fetchAnnsFinal = do
  Just tm <- gets rsModule
  let anns = (tkCache $ rsTokenCache tm) Map.! mainTid
  return anns

-- |Get the current tokens for a given GHC.SrcSpan.
getToksForSpan ::  GHC.SrcSpan -> RefactGhc [PosToken]
getToksForSpan _sspan = do
  error $ "getToksForSpan no longer used"


-- ---------------------------------------------------------------------

getTypecheckedModule :: RefactGhc GHC.TypecheckedModule
getTypecheckedModule = do
  mtm <- gets rsModule
  case mtm of
    Just tm -> return $ rsTypecheckedMod tm
    Nothing -> error "HaRe: file not loaded for refactoring"

getRefactStreamModified :: RefactGhc RefacResult
getRefactStreamModified = do
  Just tm <- gets rsModule
  return $ rsStreamModified tm

-- |For testing
setRefactStreamModified :: RefacResult -> RefactGhc ()
setRefactStreamModified rr = do
  st <- get
  let (Just tm) = rsModule st
  put $ st { rsModule = Just (tm { rsStreamModified = rr })}
  return ()

getRefactInscopes :: RefactGhc InScopes
getRefactInscopes = GHC.getNamesInScope

getRefactRenamed :: RefactGhc GHC.RenamedSource
getRefactRenamed = do
  mtm <- gets rsModule
  let tm = gfromJust "getRefactRenamed" mtm
  return $ gfromJust "getRefactRenamed2" $ GHC.tm_renamed_source $ rsTypecheckedMod tm

putRefactRenamed :: GHC.RenamedSource -> RefactGhc ()
putRefactRenamed renamed = do
  st <- get
  mrm <- gets rsModule
  let rm = gfromJust "putRefactRenamed" mrm
  let tm = rsTypecheckedMod rm
  let tm' = tm { GHC.tm_renamed_source = Just renamed }
  let rm' = rm { rsTypecheckedMod = tm' }
  put $ st {rsModule = Just rm'}

getRefactParsed :: RefactGhc GHC.ParsedSource
getRefactParsed = do
  mtm <- gets rsModule
  let tm = gfromJust "getRefactParsed" mtm
  let t  = rsTypecheckedMod tm

  let pm = GHC.tm_parsed_module t
  return $ GHC.pm_parsed_source pm

putRefactParsed :: GHC.ParsedSource -> Anns -> RefactGhc ()
putRefactParsed parsed newAnns = do
  st <- get
  mrm <- gets rsModule
  let rm = gfromJust "putRefactParsed" mrm
  let tm = rsTypecheckedMod rm
  -- let tk' = modifyAnns (rsTokenCache rm) (const newAnns)
  let tk' = modifyAnns (rsTokenCache rm) (mergeAnns newAnns)

  let pm = (GHC.tm_parsed_module tm) { GHC.pm_parsed_source = parsed }
  let tm' = tm { GHC.tm_parsed_module = pm }
  let rm' = rm { rsTypecheckedMod = tm', rsTokenCache = tk', rsStreamModified = RefacModified }
  put $ st {rsModule = Just rm'}

-- ---------------------------------------------------------------------
-- addRefactAnns :: Anns -> RefactGhc ()
-- addRefactAnns newAnns = liftT $ modifyAnnsT (mergeAnns newAnns)

-- | Combine the new with old, such that the new take priority
-- unionAnns :: Anns -> Anns -> Anns
-- unionAnns = mergeAnns

-- |Internal low level interface to access the current annotations from the
-- RefactGhc state.
getRefactAnns :: RefactGhc Anns
getRefactAnns =
  (Map.! mainTid) . tkCache . rsTokenCache . gfromJust "getRefactAnns"
    <$> gets rsModule

-- |Internal low level interface to access the current annotations from the
-- RefactGhc state.
setRefactAnns :: Anns -> RefactGhc ()
setRefactAnns anns = modifyRefactAnns (const anns)

-- |Internal low level interface to access the current annotations from the
-- RefactGhc state.
modifyRefactAnns :: (Anns -> Anns) -> RefactGhc ()
modifyRefactAnns f = do
  st <- get
  mrm <- gets rsModule
  let rm = gfromJust "modifyRefactAnns" mrm
  let tk' = modifyAnns (rsTokenCache rm) f
  let rm' = rm { rsTokenCache = tk', rsStreamModified = RefacModified }
  put $ st {rsModule = Just rm'}

-- |Internal low level interface to access the current annotations from the
-- RefactGhc state.
modifyAnns :: TokenCache Anns -> (Anns -> Anns) -> TokenCache Anns
modifyAnns tk f = tk'
  where
    anns = (tkCache tk) Map.! mainTid
    tk' = tk {tkCache = Map.insert mainTid
                                   (f anns)
                                   (tkCache tk) }

-- ----------------------------------------------------------------------

putParsedModule
  :: GHC.TypecheckedModule -> RefactGhc ()
putParsedModule tm = do
  st <- get
  put $ st { rsModule = initRefactModule tm }

clearParsedModule :: RefactGhc ()
clearParsedModule = do
  st <- get
  put $ st { rsModule = Nothing }

-- ---------------------------------------------------------------------

-- |Replace the Located RdrName in the ParsedSource
replaceRdrName :: GHC.Located GHC.RdrName -> RefactGhc ()
replaceRdrName (GHC.L l newName) = do
  -- ++AZ++ TODO: move this body to somewhere appropriate
  logm $ "replaceRdrName:" ++ showGhcQual (l,newName)
  parsed <- getRefactParsed
  anns <- getRefactAnns
  logm $ "replaceRdrName:before:parsed=" ++ showGhc parsed
  let replaceRdr :: GHC.Located GHC.RdrName -> State Anns (GHC.Located GHC.RdrName)
      replaceRdr old@(GHC.L ln _)
        | l == ln = do
           an <- get
           let new = (GHC.L l newName)
           put $ replaceAnnKey an old new
           return new
      replaceRdr x = return x

      replaceHsVar :: GHC.LHsExpr GHC.RdrName -> State Anns (GHC.LHsExpr GHC.RdrName)
      replaceHsVar (GHC.L ln (GHC.HsVar _))
        | l == ln = return (GHC.L l (GHC.HsVar newName))
      replaceHsVar x = return x

      replaceHsTyVar (GHC.L ln (GHC.HsTyVar _))
        | l == ln = return (GHC.L l (GHC.HsTyVar newName))
      replaceHsTyVar x = return x

      replacePat (GHC.L ln (GHC.VarPat _))
        | l == ln = return (GHC.L l (GHC.VarPat newName))
      replacePat x = return x

      fn :: State Anns GHC.ParsedSource
      fn = do
             r <- SYB.everywhereM (SYB.mkM replaceRdr
                              `SYB.extM` replaceHsTyVar
                              `SYB.extM` replaceHsVar
                              `SYB.extM` replacePat) parsed
             return r
      (parsed',anns') = runState fn anns
  logm $ "replaceRdrName:after:parsed'=" ++ showGhc parsed'
  putRefactParsed parsed' emptyAnns
  setRefactAnns anns'
  return ()

-- ---------------------------------------------------------------------

refactReplaceDecls :: (HasDecls a) => a -> [GHC.LHsDecl GHC.RdrName] -> RefactGhc a
refactReplaceDecls t decls = do
  liftT (replaceDecls t decls)

-- |Run a transformation in the ghc-exactprint Transform monad, updating the
-- current annotations and unique SrcSpan value.
refactRunTransform :: Transform a -> RefactGhc a
refactRunTransform transform = do
  u <- gets rsUniqState
  ans <- getRefactAnns
  let (a,(ans',u'),logLines) = runTransformFrom u ans transform
  putUnique u'
  setRefactAnns ans'
  when (not (null logLines)) $ do
    logm $ intercalate "\n" logLines
  return a

liftT :: Transform a -> RefactGhc a
liftT = refactRunTransform


putUnique :: Int -> RefactGhc ()
putUnique u = do
  s <- get
  put $ s { rsUniqState = u }

-- ---------------------------------------------------------------------

getRefactTargetModule :: RefactGhc TargetModule
getRefactTargetModule = do
  mt <- gets rsCurrentTarget
  case mt of
    Nothing -> error $ "HaRe:getRefactTargetModule:no module loaded"
    Just t -> return t

-- ---------------------------------------------------------------------

getRefactFileName :: RefactGhc (Maybe FilePath)
getRefactFileName = do
  mtm <- gets rsModule
  case mtm of
    Nothing  -> return Nothing
    -- Just tm -> do toks <- fetchOrigToks
    --                return $ Just (GHC.unpackFS $ fileNameFromTok $ ghead "getRefactFileName" toks)
    Just tm -> return $ Just (fileNameFromModSummary $ GHC.pm_mod_summary
                              $ GHC.tm_parsed_module $ rsTypecheckedMod tm)

-- ---------------------------------------------------------------------

fileNameFromModSummary :: GHC.ModSummary -> FilePath
fileNameFromModSummary modSummary = fileName
  where
    -- TODO: what if we are loading a compiled only client and do not
    -- have the original source?
    Just fileName = GHC.ml_hs_file (GHC.ms_location modSummary)

-- ---------------------------------------------------------------------

getRefactModule :: RefactGhc GHC.Module
getRefactModule = do
  mtm <- gets rsModule
  case mtm of
    Nothing  -> error $ "Hare.MonadFunctions.getRefactModule:no module loaded"
    Just tm -> do
      let t  = rsTypecheckedMod tm
      let pm = GHC.tm_parsed_module t
      return (GHC.ms_mod $ GHC.pm_mod_summary pm)

-- ---------------------------------------------------------------------

getRefactModuleName :: RefactGhc GHC.ModuleName
getRefactModuleName = do
  modu <- getRefactModule
  return $ GHC.moduleName modu

-- ---------------------------------------------------------------------

getRefactNameMap :: RefactGhc NameMap
getRefactNameMap = do
  mtm <- gets rsModule
  case mtm of
    Nothing  -> error $ "Hare.MonadFunctions.getRefacNameMap:no module loaded"
    Just tm -> return (rsNameMap tm)

-- ---------------------------------------------------------------------

getRefactDone :: RefactGhc Bool
getRefactDone = do
  flags <- gets rsFlags
  logm $ "getRefactDone: " ++ (show (rsDone flags))
  return (rsDone flags)

setRefactDone :: RefactGhc ()
setRefactDone = do
  logm $ "setRefactDone"
  st <- get
  put $ st { rsFlags = RefFlags True }

clearRefactDone :: RefactGhc ()
clearRefactDone = do
  logm $ "clearRefactDone"
  st <- get
  put $ st { rsFlags = RefFlags False }

-- ---------------------------------------------------------------------

setStateStorage :: StateStorage -> RefactGhc ()
setStateStorage storage = do
  st <- get
  put $ st { rsStorage = storage }

getStateStorage :: RefactGhc StateStorage
getStateStorage = do
  storage <- gets rsStorage
  return storage

-- ---------------------------------------------------------------------

logDataWithAnns :: (SYB.Data a) => String -> a -> RefactGhc ()
logDataWithAnns str ast = do
  anns <- getRefactAnns
  logm $ str ++ showAnnData anns 0 ast

-- ---------------------------------------------------------------------

logAnns :: String -> RefactGhc ()
logAnns str = do
  anns <- getRefactAnns
  logm $ str ++ showGhc anns

-- ---------------------------------------------------------------------

logParsedSource :: String -> RefactGhc ()
logParsedSource str = do
  parsed <- getRefactParsed
  logDataWithAnns str parsed

-- ---------------------------------------------------------------------

initRefactModule
  :: GHC.TypecheckedModule -> Maybe RefactModule
initRefactModule tm
  = Just (RefMod { rsTypecheckedMod = tm
                 , rsNameMap = initRdrNameMap tm
                 , rsTokenCache = initTokenCacheLayout (relativiseApiAnns
                                    (GHC.pm_parsed_source $ GHC.tm_parsed_module tm)
                                    (GHC.pm_annotations $ GHC.tm_parsed_module tm))
                 , rsStreamModified = RefacUnmodified
                 })


initTokenCacheLayout :: a -> TokenCache a
initTokenCacheLayout a = TK (Map.fromList [((TId 0),a)]) (TId 0)

initRdrNameMap :: GHC.TypecheckedModule -> NameMap
initRdrNameMap tm = r
  where
    parsed  = GHC.pm_parsed_source $ GHC.tm_parsed_module tm
    renamed = gfromJust "initRdrNameMap" $ GHC.tm_renamed_source tm

    checkRdr :: GHC.Located GHC.RdrName -> Maybe [GHC.SrcSpan]
    checkRdr (GHC.L l (GHC.Unqual _)) = Just [l]
    checkRdr (GHC.L l (GHC.Qual _ _)) = Just [l]
    checkRdr (GHC.L _ _)= Nothing

    checkName :: GHC.Located GHC.Name -> Maybe [GHC.Located GHC.Name]
    checkName ln = Just [ln]

    rdrNames = gfromJust "initRdrNameMap" $ SYB.everything mappend (nameSybQuery checkRdr ) parsed
    names    = gfromJust "initRdrNameMap" $ SYB.everything mappend (nameSybQuery checkName) renamed

    nameMap = Map.fromList $ map (\(GHC.L l n) -> (l,n)) names

    r1 = Map.fromList $ map (\l -> (l,Map.lookup l nameMap)) rdrNames
    -- r = Map.map (fromMaybe (error "initRdrNameMap:no val")) r1
    r = Map.mapWithKey (\k v -> fromMaybe (error $ "initRdrNameMap:no val for:" ++ showGhc k) v) r1

-- ---------------------------------------------------------------------

nameSybQuery :: (SYB.Typeable a, SYB.Typeable t)
             => (GHC.Located a -> Maybe r) -> t -> Maybe r
nameSybQuery checker = q
  where
    q = Nothing `SYB.mkQ`  worker
                `SYB.extQ` workerBind
                `SYB.extQ` workerExpr
                `SYB.extQ` workerLIE
                `SYB.extQ` workerHsTyVarBndr
                `SYB.extQ` workerLHsType

    worker (pnt :: (GHC.Located a))
      = checker pnt

    -- workerBind (GHC.L l (GHC.VarPat name) :: (GHC.Located (GHC.Pat a)))
    workerBind (GHC.L l (GHC.VarPat name))
      = checker (GHC.L l name)
    workerBind _ = Nothing

    -- workerExpr ((GHC.L l (GHC.HsVar name)) :: (GHC.Located (GHC.HsExpr a)))
    workerExpr ((GHC.L l (GHC.HsVar name)))
      = checker (GHC.L l name)
    workerExpr _ = Nothing

    workerLIE ((GHC.L _l (GHC.IEVar (GHC.L ln name))) :: (GHC.LIE a))
    -- workerLIE ((GHC.L _l (GHC.IEVar (GHC.L ln name))))
      = checker (GHC.L ln name)
    workerLIE _ = Nothing

    -- workerHsTyVarBndr ((GHC.L l (GHC.UserTyVar name))::  (GHC.LHsTyVarBndr a))
    workerHsTyVarBndr ((GHC.L l (GHC.UserTyVar name)))
      = checker (GHC.L l name)
    workerHsTyVarBndr _ = Nothing

    workerLHsType ((GHC.L l (GHC.HsTyVar name)))
      = checker (GHC.L l name)
    workerLHsType _ = Nothing

-- ---------------------------------------------------------------------

parseDeclWithAnns :: String -> RefactGhc (GHC.LHsDecl GHC.RdrName)
parseDeclWithAnns src = do
  let label = "<interactive"
  r  <- GHC.liftIO $ withDynFlags (\df -> parseDecl df label src)
  case r of
    Left err -> error (show err)
    Right (anns,decl) -> do
      -- addRefactAnns anns
      liftT $ modifyAnnsT (mergeAnns anns)
      return decl

-- EOF
