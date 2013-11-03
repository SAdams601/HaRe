{-# LANGUAGE CPP #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
-- |
--

module Language.Haskell.Refact.Utils.Layout (
    initTokenLayout
  , nullTokenLayout
  , allocTokens
  , retrieveTokens
  , getLoc
  ) where

import qualified Bag           as GHC
import qualified ForeignCall   as GHC
import qualified GHC           as GHC
import qualified Outputable    as GHC
import qualified SrcLoc        as GHC

import Outputable

import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB

import Data.List
import Data.Tree
import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.LayoutTypes
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.TokenUtils
import Language.Haskell.Refact.Utils.TokenUtilsTypes
import Language.Haskell.Refact.Utils.TypeSyn

-- ---------------------------------------------------------------------

-- | Extract the layout-sensitive parts of the GHC AST.

-- The layout keywords are `let`, `where`, `of` and `do`. The
-- expressions introduced by them need to be kept indented at the same
-- level.

{-

AST Items for layout keywords.

(gleaned from Parser.y.pp in the ghc sources)

`let`


@
  HsLet
    HsLet (HsLocalBinds id) (LHsExpr id) :: HsExpr id
              ^^keep aligned

  LetStmt
    LetStmt (HsLocalBindsLR idL idR) :: StmtLR idL idR
                ^^keep aligned
@

`where`

@
  HsModule
    -- not relevant to layout

  ClassDecl :: TyClDecl
    ClassDecl ....

  ClsInstD :: InstDecl
    ClsInstD typ binds sigs [fam_insts]
            ^^the binds, sigs, fam_insts should all align

  GRHSs
    GRHS [LStmt id] (LHsExpr id)
           ^^keep aligned

  TyDecl ::  TyClDecl
    TyDecl name vars defn fvs
                      ^^keep aligned
      [The `where` is in the defn]

  FamInstDecl
    FamInstDecl tycon pats defn fvs
                            ^^keep aligned
      [The `where` is in the defn]
@

`of`

@
  HsCase :: HsExpr
    HsCase (LHsExpr id) (MatchGroup id)
                           ^^keep aligned
@

`do`

@
  DoExpr :: HsExpr
    HsDo (HsStmtContext Name) [LStmt id] PostTcType
                                 ^^keep aligned
@
-}

-- Pretty print combinators of interest
--
-- ($$) :: Doc -> Doc -> Doc
--
--   Above, except that if the last line of the first argument stops at
--   least one position before the first line of the second begins,
--   these two lines are overlapped.
--
--
-- ($+$) :: Doc -> Doc -> Doc
--
--   Above, with no overlapping.
--
--
-- nest :: Int -> Doc -> Doc
--
--   Nest (or indent) a document by a given number of positions
--   (which may also be negative)
--
--
-- hang :: Doc -> Int -> Doc -> Doc
--
--   hang d1 n d2 = sep [d1, nest n d2]
--


-- ---------------------------------------------------------------------

deriving instance Show Label

instance Outputable (Tree Entry) where
  ppr (Node label subs) = hang (text "Node") 2 (vcat [ppr label,ppr subs])

instance Outputable Entry where
  ppr (Entry sspan lay toks) = text "Entry" <+> ppr sspan <+> ppr lay <+> text (show toks)

instance Outputable Layout where
  ppr (Above)      = text "Above"
  ppr (Offset r c) = text "Offset" <+> ppr r <+> ppr c
  ppr (NoChange)   = text "NoChange"

-- ---------------------------------------------------------------------

initTokenLayout :: GHC.ParsedSource -> [PosToken] -> LayoutTree
initTokenLayout parsed toks = (allocTokens parsed toks)

nullTokenLayout :: TokenLayout
-- nullTokenLayout = TL (Leaf nullSrcSpan NoChange [])
nullTokenLayout = TL (Node (Entry (sf nullSrcSpan) NoChange []) [])

-- ---------------------------------------------------------------------

-- TODO: bring in startEndLocIncComments'
allocTokens :: GHC.ParsedSource -> [PosToken] -> LayoutTree
allocTokens (GHC.L _l (GHC.HsModule maybeName maybeExports imports decls _warns _haddocks)) toks = r
  where
    (nameLayout,toks1) =
      case maybeName of
        Nothing -> ([],toks)
        Just (GHC.L ln _modName) -> ((makeLeafFromToks s1) ++ [makeLeaf ln NoChange modNameToks],toks')
          where
            (s1,modNameToks,toks') = splitToks (ghcSpanStartEnd ln) toks

    (exportLayout,toks2) =
      case maybeExports of
        Nothing -> ([],toks1)
        Just exps -> ((makeLeafFromToks s2) ++ (makeLeafFromToks expToks),toks2')
          where
            (s2,expToks,toks2') = splitToksForList exps toks1

    (importLayout,toks3) =
      case imports of
        [] -> ([],toks2)
        is -> ((makeLeafFromToks s3) ++ (makeLeafFromToks impToks),toks3')
          where
            (s3,impToks,toks3') = splitToksForList is toks2

    (declLayout,_toks4) =
      case decls of
        [] -> ([],toks3)
        -- is -> ([Leaf s4,Leaf impToks,Leaf toks4'],[])
        is -> ((makeLeafFromToks s4) ++ allocDecls is declToks ++ (makeLeafFromToks toks4'),[])
          where
            (s4,declToks,toks4') = splitToksForList is toks3

    r = makeGroup (strip $ nameLayout ++ exportLayout ++ importLayout ++ declLayout)
    -- r = error $ "allocTokens:(nameLayout,toks1)=" ++ (show (nameLayout,toks1)) -- ++AZ++
    -- r = error $ "allocTokens:(exportLayout,toks2)=" ++ (show (exportLayout,toks2)) -- ++AZ++
    -- r = error $ "allocTokens:(importLayout,toks3)=" ++ (show (importLayout,toks3)) -- ++AZ++
    -- r = error $ "allocTokens:(declLayout,toks4)=" ++ (show (declLayout,_toks4)) -- ++AZ++


-- ---------------------------------------------------------------------

allocDecls :: [GHC.LHsDecl GHC.RdrName] -> [PosToken] -> [LayoutTree]
allocDecls decls toks = r
  where
    (declLayout,tailToks) = foldl' doOne ([],toks) decls

    r = strip $ declLayout ++ (makeLeafFromToks tailToks)

    doOne :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
    doOne acc d@(GHC.L _ (GHC.TyClD       _)) = allocTyClD       acc d
    doOne acc d@(GHC.L _ (GHC.InstD       _)) = allocInstD       acc d
    doOne acc d@(GHC.L _ (GHC.DerivD      _)) = allocDerivD      acc d
    doOne acc d@(GHC.L _ (GHC.ValD        _)) = allocValD        acc d
    doOne acc d@(GHC.L _ (GHC.SigD        _)) = allocSigD        acc d
    doOne acc d@(GHC.L _ (GHC.DefD        _)) = allocDefD        acc d
    doOne acc d@(GHC.L _ (GHC.ForD        _)) = allocForD        acc d
    doOne acc d@(GHC.L _ (GHC.WarningD    _)) = allocWarningD    acc d
    doOne acc d@(GHC.L _ (GHC.AnnD        _)) = allocAnnD        acc d
    doOne acc d@(GHC.L _ (GHC.RuleD       _)) = allocRuleD       acc d
    doOne acc d@(GHC.L _ (GHC.VectD       _)) = allocVectD       acc d
    doOne acc d@(GHC.L _ (GHC.SpliceD     _)) = allocSpliceD     acc d
    doOne acc d@(GHC.L _ (GHC.DocD        _)) = allocDocD        acc d
    doOne acc d@(GHC.L _ (GHC.QuasiQuoteD _)) = allocQuasiQuoteD acc d

-- ---------------------------------------------------------------------

allocTyClD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocTyClD (acc,toks) (GHC.L l (GHC.TyClD (GHC.ForeignType ln _))) = (r,toks')
  where
    (s1,clToks,toks') = splitToks (ghcSpanStartEnd l) toks
    lnToks = allocLocated ln clToks
    r = acc ++ (strip $ (makeLeafFromToks s1) ++ lnToks)
allocTyClD (acc,toks) (GHC.L l (GHC.TyClD (GHC.TyFamily _f n@(GHC.L ln _) vars _mk))) = (r,toks')
  where
    (s1,clToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (s2,nToks,varsToks) = splitToks (ghcSpanStartEnd ln) toks'
    nLayout = allocLocated n nToks
    (varsLayout,s3) = allocTyVarBndrs vars varsToks
    r = acc ++ (strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks clToks)
                     ++ (makeLeafFromToks s2) ++ nLayout ++ varsLayout
                     ++ (makeLeafFromToks s3))
allocTyClD (acc,toks) (GHC.L l (GHC.TyClD (GHC.TyDecl (GHC.L ln _) vars def _fvs))) = (r,toks')
  where
    (s1,clToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (s2,nToks,toks'') = splitToks (ghcSpanStartEnd ln) clToks
    (varsLayout,toks3) = allocTyVarBndrs vars toks''
    (typeLayout,toks4) = allocHsTyDefn def toks3
    r = acc ++ (strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks s2)
                     ++ (makeLeafFromToks nToks) ++ varsLayout ++ typeLayout
                     ++ (makeLeafFromToks toks4))
allocTyClD (acc,toks) (GHC.L l (GHC.TyClD (GHC.ClassDecl ctx (GHC.L ln _) vars fds sigs meths ats atdefs docs _fvs))) = (r,toks')
  where
    (s1,clToks,toks') = splitToks (ghcSpanStartEnd l) toks
    r = error "allocTyClD ClassDecl undefined"

-- ---------------------------------------------------------------------

allocInstD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocInstD (acc,toks) d@(GHC.L l (GHC.InstD       _))
  = error "allocInstD undefined"

-- ---------------------------------------------------------------------

allocDerivD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocDerivD (acc,toks) d@(GHC.L l (GHC.DerivD      _))
  = error "allocDerivD undefined"

-- ---------------------------------------------------------------------

allocValD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocValD (acc,toks) (GHC.L l (GHC.ValD bind@(GHC.FunBind _ _ _ _ _ _))) = r
  where
    (s1,bindToks,toks') = splitToks (ghcSpanStartEnd l) toks
    bindLayout = allocBind (GHC.L l bind) bindToks
    r = (acc ++ (strip $ (makeLeafFromToks s1) ++ [makeGroup bindLayout] ),toks')

allocValD (acc,toks) (GHC.L l (GHC.ValD (GHC.PatBind lhs@(GHC.L ll _) (GHC.GRHSs rhs localBinds) _ _ _))) = (r,toks')
  where
    (s1,bindToks,toks')  = splitToks (ghcSpanStartEnd l) toks
    (s2,lhsToks,toks1) = splitToks (ghcSpanStartEnd ll) bindToks
    (s3,rhsToks,bindsToks) = splitToksForList rhs toks1
    lhsLayout = allocPat lhs lhsToks
    rhsLayout = allocList rhs rhsToks allocRhs
    localBindsLayout = allocLocalBinds localBinds bindsToks
    r = acc ++ (strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks s2)
             ++ lhsLayout ++ rhsLayout ++ (makeLeafFromToks s3)
             ++ localBindsLayout)

allocValD (acc,toks) d@(GHC.L l (GHC.ValD (GHC.VarBind n rhs _))) = error "allocValD:VarBinds"
allocValD (acc,toks) d@(GHC.L l (GHC.ValD (GHC.AbsBinds tvs vars exps ev binds))) = error "allocValD:AbsBinds"

-- ---------------------------------------------------------------------

allocSigD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocSigD (acc,toks) (GHC.L l (GHC.SigD (GHC.TypeSig names t@(GHC.L lt _)))) = (r,toks')
  where
    (s1,bindToks,toks')  = splitToks (ghcSpanStartEnd l) toks
    (s2,nameToks,toks'') = splitToksForList names bindToks
    (s3,typeToks,s4)     = splitToks (ghcSpanStartEnd lt) toks''
    nameLayout = allocList names nameToks allocLocated
    typeLayout = allocType t typeToks
    r = acc ++ (strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks s2)
                     ++ nameLayout ++ (makeLeafFromToks s3) ++ typeLayout
                     ++ (makeLeafFromToks s4))
allocSigD (acc,toks) (GHC.L l (GHC.SigD (GHC.GenericSig names t@(GHC.L lt _)))) = (r,toks')
  where
    (s1,bindToks,toks')  = splitToks (ghcSpanStartEnd l) toks
    (s2,nameToks,toks'') = splitToksForList names bindToks
    (s3,typeToks,s4)     = splitToks (ghcSpanStartEnd lt) toks''
    nameLayout = allocList names nameToks allocLocated
    typeLayout = allocType t typeToks
    r = acc ++ (strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks s2)
            ++ nameLayout ++ (makeLeafFromToks s3) ++typeLayout
            ++ (makeLeafFromToks s4) )
allocSigD (acc,toks) (GHC.L l (GHC.SigD (GHC.IdSig _i))) = (r,toks')
  where
    (s1,nameToks,toks') = splitToks (ghcSpanStartEnd l) toks
    r = acc ++ (strip $ (makeLeafFromToks s1) ++ [makeLeaf l NoChange nameToks])
allocSigD (acc,toks) (GHC.L l (GHC.SigD (GHC.FixSig (GHC.FixitySig n@(GHC.L ln _) _fix)))) = (r,toks')
  where
    (s1,fToks,toks')   = splitToks (ghcSpanStartEnd l) toks
    (s2,nToks,fixToks) = splitToks (ghcSpanStartEnd ln) fToks

    r = acc ++ (strip $ (makeLeafFromToks s1) ++ (allocLocated n nToks)
                     ++ (makeLeafFromToks s2) ++ (makeLeafFromToks fixToks))
allocSigD (acc,toks) (GHC.L l (GHC.SigD (GHC.InlineSig n@(GHC.L ln _) _ip))) = (r,toks')
  where
    (s1,sigToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (s2,nToks,ipToks)  = splitToks (ghcSpanStartEnd ln) sigToks
    r = acc ++ (strip $ (makeLeafFromToks s1) ++ (allocLocated n nToks)
                     ++ (makeLeafFromToks s2) ++ (makeLeafFromToks ipToks))
allocSigD (acc,toks) (GHC.L l (GHC.SigD (GHC.SpecSig n@(GHC.L ln _) t@(GHC.L lt _) _ip))) = (r,toks')
  where
    (s1,sigToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (s2,nToks,toks'')  = splitToks (ghcSpanStartEnd ln) sigToks
    (s3,tToks,ipToks)  = splitToks (ghcSpanStartEnd lt) toks''
    nameLayout = allocLocated n nToks
    typeLayout = allocType t tToks
    ipLayout = makeLeafFromToks ipToks
    r = acc ++ (strip $ (makeLeafFromToks s1) ++ nameLayout ++ (makeLeafFromToks s2)
                     ++ typeLayout ++ (makeLeafFromToks s3) ++ ipLayout)
allocSigD (acc,toks) (GHC.L l (GHC.SigD (GHC.SpecInstSig t))) = (acc ++ r,toks')
  where
    (s1,sigToks,toks') = splitToks (ghcSpanStartEnd l) toks
    r = acc ++ (strip $ (makeLeafFromToks s1) ++ allocType t sigToks)

-- ---------------------------------------------------------------------

allocDefD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocDefD (acc,toks) d@(GHC.L l (GHC.DefD        _))
  = error "allocDefD undefined"

-- ---------------------------------------------------------------------

allocForD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocForD (acc,toks) d@(GHC.L l (GHC.ForD        _))
  = error "allocForD undefined"

-- ---------------------------------------------------------------------

allocWarningD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocWarningD (acc,toks) d@(GHC.L l (GHC.WarningD    _))
  = error "allocWarningD undefined"

-- ---------------------------------------------------------------------

allocAnnD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocAnnD (acc,toks) d@(GHC.L l (GHC.AnnD        _))
  = error "allocAnnD undefined"

-- ---------------------------------------------------------------------

allocRuleD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocRuleD (acc,toks) d@(GHC.L l (GHC.RuleD       _))
  = error "allocRuleD undefined"

-- ---------------------------------------------------------------------

allocVectD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocVectD (acc,toks) d@(GHC.L l (GHC.VectD       _))
  = error "allocVectD undefined"

-- ---------------------------------------------------------------------

allocSpliceD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocSpliceD (acc,toks) d@(GHC.L l (GHC.SpliceD     _))
  = error "allocSpliceD undefined"

-- ---------------------------------------------------------------------

allocDocD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocDocD (acc,toks) d@(GHC.L l (GHC.DocD        _))
  = error "allocDocD undefined"

-- ---------------------------------------------------------------------

allocQuasiQuoteD :: ([LayoutTree],[PosToken]) -> GHC.LHsDecl GHC.RdrName -> ([LayoutTree],[PosToken])
allocQuasiQuoteD (acc,toks) d@(GHC.L l (GHC.QuasiQuoteD _))
  = error "allocQuasiQuoteD undefined"

-- ---------------------------------------------------------------------

allocMatches :: [GHC.LMatch GHC.RdrName] -> [PosToken] -> [LayoutTree]
allocMatches matches toksIn = allocList matches toksIn doOne
  where
    doOne :: GHC.LMatch GHC.RdrName -> [PosToken] -> [LayoutTree]
    doOne (GHC.L _ (GHC.Match pats _mtyp (GHC.GRHSs rhs localBinds))) toks = r
      where
        (s1,patsToks,toks1) = splitToksForList pats toks
        (s2,rhsToks,bindsToks) = splitToksForList rhs toks1
        patLayout = allocList pats patsToks allocPat
        rhsLayout = allocList rhs rhsToks allocRhs
        localBindsLayout = allocLocalBinds localBinds bindsToks
        r = (strip $ (makeLeafFromToks s1) ++ patLayout ++ (makeLeafFromToks s2) ++ rhsLayout ++ localBindsLayout)

-- ---------------------------------------------------------------------

allocPat :: GHC.LPat GHC.RdrName -> [PosToken] -> [LayoutTree]
allocPat (GHC.L l _) toks = makeLeafFromToks toks

-- ---------------------------------------------------------------------

allocRhs :: GHC.LGRHS GHC.RdrName -> [PosToken] -> [LayoutTree]
allocRhs (GHC.L _l (GHC.GRHS stmts expr)) toksIn = r
  where
    (s1,stmtsToks,toks') = splitToksForList stmts toksIn
    stmtsLayout = allocList stmts stmtsToks allocStmt
    exprLayout = allocExpr expr toks'
    r = strip $ (makeLeafFromToks s1) ++ stmtsLayout ++ exprLayout

-- ---------------------------------------------------------------------

allocStmt :: GHC.LStmt GHC.RdrName -> [PosToken] -> [LayoutTree]
allocStmt (GHC.L _ (GHC.LastStmt expr _)) toks = allocExpr expr toks
allocStmt (GHC.L _ (GHC.BindStmt pat@(GHC.L lp _) expr _ _)) toks = r
  where
    (s1,patToks,toks') = splitToks (ghcSpanStartEnd lp) toks
    patLayout = allocPat pat patToks
    exprLayout = allocExpr expr toks'
    r = strip $ (makeLeafFromToks s1) ++ patLayout ++ exprLayout
allocStmt (GHC.L _ (GHC.ExprStmt expr _ _ _)) toks = allocExpr expr toks
allocStmt (GHC.L _ (GHC.LetStmt binds))       toks = allocLocalBinds binds toks
#if __GLASGOW_HASKELL__ > 704
allocStmt (GHC.L _ (GHC.ParStmt stmts _ _))          toks = error "allocStmt ParStmt undefined"
#else
allocStmt (GHC.L _ (GHC.ParStmt stmts _ _ _))        toks = error "allocStmt ParStmt undefined"
#endif
allocStmt (GHC.L _ (GHC.TransStmt _ _ _ _ _ _ _ _ )) toks = error "allocStmt TransStmt undefined"
allocStmt (GHC.L _ (GHC.RecStmt _ _ _ _ _ _ _ _ _))  toks = error "allocStmt RecStmt undefined"

-- ---------------------------------------------------------------------

allocExpr :: GHC.LHsExpr GHC.RdrName -> [PosToken] -> [LayoutTree]
allocExpr (GHC.L l (GHC.HsVar _)) toks = [makeLeaf l NoChange toks]
allocExpr (GHC.L l (GHC.HsLit _)) toks = [makeLeaf l NoChange toks]
allocExpr (GHC.L l (GHC.HsOverLit _)) toks = [makeLeaf l NoChange toks]
allocExpr (GHC.L _ (GHC.HsLam (GHC.MatchGroup matches _))) toks
  = allocMatches matches toks
#if __GLASGOW_HASKELL__ > 704
allocExpr (GHC.L _ (GHC.HsLamCase _ (GHC.MatchGroup matches _))) toks
  = allocMatches matches toks
#endif
allocExpr (GHC.L _ (GHC.HsApp e1@(GHC.L l1 _) e2)) toks = r
  where
    (s1,e1Toks,e2Toks) = splitToks (ghcSpanStartEnd l1) toks
    e1Layout = allocExpr e1 e1Toks
    e2Layout = allocExpr e2 e2Toks
    r = strip $ (makeLeafFromToks s1) ++ e1Layout ++ e2Layout
allocExpr (GHC.L _ (GHC.OpApp e1@(GHC.L l1 _) e2@(GHC.L l2 _) _ e3)) toks = r
  where
    (s1,e1Toks,toks1) = splitToks (ghcSpanStartEnd l1) toks
    (s2,e2Toks,e3Toks) = splitToks (ghcSpanStartEnd l2) toks1
    e1Layout = allocExpr e1 e1Toks
    e2Layout = allocExpr e2 e2Toks
    e3Layout = allocExpr e3 e3Toks
    r = strip $ (makeLeafFromToks s1) ++ e1Layout ++ (makeLeafFromToks s2) ++ e2Layout ++ e3Layout
allocExpr (GHC.L _ (GHC.NegApp expr _)) toks = allocExpr expr toks
allocExpr (GHC.L _ (GHC.HsPar expr))    toks = allocExpr expr toks
allocExpr (GHC.L _ (GHC.SectionL e1@(GHC.L l1 _) e2)) toks = r
  where
    (s1,e1Toks,e2Toks) = splitToks (ghcSpanStartEnd l1) toks
    e1Layout = allocExpr e1 e1Toks
    e2Layout = allocExpr e2 e2Toks
    r = strip $ (makeLeafFromToks s1) ++ e1Layout ++ e2Layout
allocExpr (GHC.L _ (GHC.SectionR e1@(GHC.L l1 _) e2)) toks = r
  where
    (s1,e1Toks,e2Toks) = splitToks (ghcSpanStartEnd l1) toks
    e1Layout = allocExpr e1 e1Toks
    e2Layout = allocExpr e2 e2Toks
    r = strip $ (makeLeafFromToks s1) ++ e1Layout ++ e2Layout
allocExpr (GHC.L _ (GHC.ExplicitTuple tupArgs _)) toks = r
  where
    r = error $ "allocExpr ExplicitTuple undefined"
allocExpr (GHC.L _ (GHC.HsCase expr@(GHC.L le _) (GHC.MatchGroup matches _))) toks = r
  where
    (s1,exprToks,matchToks) = splitToks (ghcSpanStartEnd le) toks
    exprLayout = allocExpr expr exprToks
    matchesLayout = allocMatches matches matchToks
    r = strip $ (makeLeafFromToks s1) ++ exprLayout ++ matchesLayout
allocExpr (GHC.L _ (GHC.HsIf _ e1@(GHC.L l1 _) e2@(GHC.L l2 _) e3)) toks = r
  where
    (s1,e1Toks,toks1) = splitToks (ghcSpanStartEnd l1) toks
    (s2,e2Toks,e3Toks) = splitToks (ghcSpanStartEnd l2) toks1
    e1Layout = allocExpr e1 e1Toks
    e2Layout = allocExpr e2 e2Toks
    e3Layout = allocExpr e3 e3Toks
    r = strip $ (makeLeafFromToks s1) ++ e1Layout ++ (makeLeafFromToks s2) ++ e2Layout ++ e3Layout
#if __GLASGOW_HASKELL__ > 704
allocExpr (GHC.L _ (GHC.HsMultiIf _ rhs)) toks = allocList rhs toks allocRhs
#endif
allocExpr (GHC.L _ (GHC.HsLet localBinds expr@(GHC.L le _))) toks = r
  where
    (bindToks,exprToks,toks') = splitToks (ghcSpanStartEnd le) toks
    bindLayout = allocLocalBinds localBinds bindToks
    exprLayout = allocExpr expr exprToks
    r = strip $ bindLayout ++ [makeGroup exprLayout] ++ (makeLeafFromToks toks')
allocExpr (GHC.L _ (GHC.HsDo _ stmts _)) toks = allocList stmts toks allocStmt
allocExpr (GHC.L _ (GHC.ExplicitList _ exprs)) toks = allocList exprs toks allocExpr
allocExpr (GHC.L _ (GHC.ExplicitPArr _ exprs)) toks = allocList exprs toks allocExpr
allocExpr (GHC.L _ (GHC.RecordCon (GHC.L ln _) _ (GHC.HsRecFields fields _))) toks = r
  where
    (s1,nameToks,fieldsToks) = splitToks (ghcSpanStartEnd ln) toks
    nameLayout = [makeLeaf ln NoChange nameToks]
    fieldsLayout = error "allocExpr allocRecField needs work"
    r = strip $ (makeLeafFromToks s1) ++ nameLayout ++ fieldsLayout

allocExpr (GHC.L _ (GHC.ArithSeq _ info)) toks = allocArithSeqInfo info toks

allocExpr e toks = error $ "allocExpr undefined for " ++ (SYB.showData SYB.Parser 0  e)

-- ---------------------------------------------------------------------

allocLocalBinds :: GHC.HsLocalBinds GHC.RdrName -> [PosToken] -> [LayoutTree]
allocLocalBinds GHC.EmptyLocalBinds toks = strip $ makeLeafFromToks toks
allocLocalBinds (GHC.HsValBinds (GHC.ValBindsIn binds sigs)) toks = r
  where
    bindList = GHC.bagToList binds
    (s1,toksBinds,toks1) = splitToksForList bindList toks

    firstBindTok = ghead "allocLocalBinds" $ dropWhile isWhiteSpaceOrIgnored toksBinds

    (ro,co) = case (filter isWhereOrLet s1) of
               [] -> (0,0)
               (x:_) -> (tokenRow firstBindTok - tokenRow x,
                         tokenCol firstBindTok - tokenCol x)

    bindsLayout = case allocList bindList toksBinds allocBind of
      [] -> []
      bs -> [placeOffset ro co [placeAbove bs]]
    sigsLayout = allocList sigs toks1 allocSig
    r = strip $ (makeLeafFromToks s1) ++ bindsLayout ++ sigsLayout

allocLocalBinds (GHC.HsIPBinds ib)  toks = error "allocLocalBinds undefined"

-- ---------------------------------------------------------------------

allocBind :: GHC.LHsBind GHC.RdrName -> [PosToken] -> [LayoutTree]
allocBind (GHC.L l (GHC.FunBind (GHC.L ln _) _ (GHC.MatchGroup matches _) _ _ _)) toks = r
  where
    (nameLayout,toks1) = ((makeLeafFromToks s1)++[makeLeaf ln NoChange nameToks],toks')
      where
        (s1,nameToks,toks') = splitToks (ghcSpanStartEnd ln) toks

    (matchesLayout,toks2) = ((makeLeafFromToks s2) ++ allocMatches matches matchToks,toks2')
          where
            (s2,matchToks,toks2') = splitToksForList matches toks1

    r = strip $ [mkGroup l NoChange (strip $ nameLayout ++ matchesLayout)] ++ (makeLeafFromToks toks2)

-- ---------------------------------------------------------------------

allocSig :: GHC.LSig GHC.RdrName -> [PosToken] -> [LayoutTree]
allocSig (GHC.L l (GHC.TypeSig ns typ)) toks = r
  where
    (s1,sigToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (s2,nsToks,typToks) = splitToksForList ns sigToks
    nsLayout = allocList ns nsToks allocLocated
    typLayout = allocType typ typToks
    r = strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks s2)
             ++ nsLayout ++ typLayout ++ (makeLeafFromToks toks')
{-
GenericSig [Located name] (LHsType name)	 
IdSig Id	 
FixSig (FixitySig name)	 
InlineSig (Located name) InlinePragma	 
SpecSig (Located name) (LHsType name) InlinePragma	 
SpecInstSig (LHsType name)
-}
-- ---------------------------------------------------------------------

allocRecField :: GHC.HsRecFields GHC.RdrName (GHC.LHsExpr GHC.RdrName) -> [PosToken] -> [LayoutTree]
allocRecField = error "Layout.allocRecField undefined"

-- ---------------------------------------------------------------------

allocArithSeqInfo :: GHC.ArithSeqInfo GHC.RdrName -> [PosToken] -> [LayoutTree]
allocArithSeqInfo (GHC.From e) toks = allocExpr e toks
allocArithSeqInfo (GHC.FromThen e1@(GHC.L l _) e2) toksIn = r
  where
    (s1,e1Toks,e2Toks) = splitToks (ghcSpanStartEnd l) toksIn
    e1Layout = allocExpr e1 e1Toks
    e2Layout = allocExpr e2 e2Toks
    r = strip $ (makeLeafFromToks s1) ++ e1Layout ++ e2Layout

allocArithSeqInfo (GHC.FromTo e1@(GHC.L l _) e2) toksIn = r
  where
    (s1,e1Toks,e2Toks) = splitToks (ghcSpanStartEnd l) toksIn
    e1Layout = allocExpr e1 e1Toks
    e2Layout = allocExpr e2 e2Toks
    r = strip $ (makeLeafFromToks s1) ++ e1Layout ++ e2Layout
allocArithSeqInfo (GHC.FromThenTo e1@(GHC.L l1 _) e2@(GHC.L l2 _) e3) toksIn = r
  where
    (s1,e1Toks,toks)   = splitToks (ghcSpanStartEnd l1) toksIn
    (s2,e2Toks,e3Toks) = splitToks (ghcSpanStartEnd l2) toks
    e1Layout = allocExpr e1 e1Toks
    e2Layout = allocExpr e2 e2Toks
    e3Layout = allocExpr e3 e3Toks
    r = strip $ (makeLeafFromToks s1) ++ e1Layout ++ e2Layout ++ (makeLeafFromToks s2) ++  e3Layout

-- ---------------------------------------------------------------------

allocType :: GHC.LHsType GHC.RdrName -> [PosToken] -> [LayoutTree]
allocType (GHC.L l (GHC.HsForAllTy _ef vars (GHC.L lc ctx) typ) ) toks = r
  where
    (s1,exprToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (varsLayout,toks2) = allocTyVarBndrs vars exprToks
    (s2,ctxToks,toks3) = splitToks (ghcSpanStartEnd lc) toks2

    ctxLayout = allocHsContext ctx ctxToks
    typLayout = allocType typ toks3

    r = strip $ (makeLeafFromToks s1) ++ varsLayout ++ (makeLeafFromToks s2)
             ++ (makeLeafFromToks s2) ++ ctxLayout
             ++ typLayout ++ (makeLeafFromToks toks')
allocType n@(GHC.L _l (GHC.HsTyVar _) ) toks = allocLocated n toks
allocType (GHC.L l (GHC.HsAppTy t1@(GHC.L l1 _) t2@(GHC.L _ _)) ) toks = r
  where
    (s1,typeToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (s2,t1Toks,t2Toks) = splitToks (ghcSpanStartEnd l1) typeToks
    t1Layout = allocType t1 t1Toks
    t2Layout = allocType t2 t2Toks
    r = strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks s2)
             ++ t1Layout ++ t2Layout ++ (makeLeafFromToks toks')
allocType (GHC.L l (GHC.HsFunTy t1@(GHC.L l1 _) t2@(GHC.L _ _)) ) toks = r
  where
    (s1,typeToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (s2,t1Toks,t2Toks) = splitToks (ghcSpanStartEnd l1) typeToks
    t1Layout = allocType t1 t1Toks
    t2Layout = allocType t2 t2Toks
    r = strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks s2)
             ++ t1Layout ++ t2Layout ++ (makeLeafFromToks toks')
allocType (GHC.L l (GHC.HsListTy t1@(GHC.L l1 _)) ) toks = r
  where
    (s1,typeToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (s2,t1Toks,toks2) = splitToks (ghcSpanStartEnd l1) typeToks
    t1Layout = allocType t1 t1Toks
    r = strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks s2)
             ++ t1Layout ++ (makeLeafFromToks toks2) ++ (makeLeafFromToks toks')
allocType (GHC.L l (GHC.HsPArrTy t1@(GHC.L l1 _)) ) toks = r
  where
    (s1,typeToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (s2,t1Toks,toks2) = splitToks (ghcSpanStartEnd l1) typeToks
    t1Layout = allocType t1 t1Toks
    r = strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks s2)
             ++ t1Layout ++ (makeLeafFromToks toks2) ++ (makeLeafFromToks toks')
allocType (GHC.L l (GHC.HsTupleTy _sort types)) toks = r
  where
    (s1,typeToks,toks') = splitToks (ghcSpanStartEnd l) toks
    typesLayout = allocList types typeToks allocType
    r = strip $ (makeLeafFromToks s1)
             ++ typesLayout ++ (makeLeafFromToks toks')
{-
HsOpTy (LHsType name) (LHsTyOp name) (LHsType name)	 
HsParTy (LHsType name)	 
HsIParamTy HsIPName (LHsType name)	 
HsEqTy (LHsType name) (LHsType name)	 
HsKindSig (LHsType name) (LHsKind name)	 
HsQuasiQuoteTy (HsQuasiQuote name)	 
HsSpliceTy (HsSplice name) FreeVars PostTcKind	 
HsDocTy (LHsType name) LHsDocString	 
HsBangTy HsBang (LHsType name)	 
HsRecTy [ConDeclField name]	 
HsCoreTy Type	 
HsExplicitListTy PostTcKind [LHsType name]	 
HsExplicitTupleTy [PostTcKind] [LHsType name]	 
HsTyLit HsTyLit	 
HsWrapTy HsTyWrapper (HsType name)
-}
-- ---------------------------------------------------------------------

allocLocated :: GHC.Located b -> [PosToken] -> [LayoutTree]
allocLocated (GHC.L l _) toks = r
  where
    (s1,toks1,s2) = splitToks (ghcSpanStartEnd l) toks
    r = strip $ (makeLeafFromToks s1) ++ [makeLeaf l NoChange toks1] ++ (makeLeafFromToks s2)

-- ---------------------------------------------------------------------

allocTyVarBndrs :: GHC.LHsTyVarBndrs GHC.RdrName -> [PosToken] -> ([LayoutTree],[PosToken])
allocTyVarBndrs (GHC.HsQTvs _kvs tvs) toks = (r,s1)
  where
    (kvsToks,tyvarToks,s1) = splitToksForList tvs toks
    tyvarLayout = allocList tvs tyvarToks allocTyVarBndr
    r = (strip $ (makeLeafFromToks kvsToks) ++ tyvarLayout)

-- ---------------------------------------------------------------------

allocTyVarBndr :: GHC.LHsTyVarBndr GHC.RdrName -> [PosToken] -> [LayoutTree]
allocTyVarBndr = error "allocTyVarBndr undefined"

-- ---------------------------------------------------------------------

allocHsTyDefn :: GHC.HsTyDefn GHC.RdrName -> [PosToken] -> ([LayoutTree],[PosToken])
allocHsTyDefn (GHC.TySynonym typ@(GHC.L l _)) toks = (r,toks')
  where
    (s1,typToks,toks') = splitToks (ghcSpanStartEnd l) toks
    typeLayout = allocType typ typToks
    r = strip $ (makeLeafFromToks s1) ++ typeLayout
allocHsTyDefn (GHC.TyData _ (GHC.L lc ctx) mc mk cons mderivs) toks = (r,toks')
  where
    (s1,ctxToks,toks2) = splitToks (ghcSpanStartEnd lc) toks
    ctxLayout = allocHsContext ctx ctxToks

    -- TODO: correctly determine the token range for this
    (mcLayout,toks3) = case mc of
      Nothing -> ([],toks2)
      Just ct -> (rc,toks2')
        where
          ctLayout = allocCType ct toks2
          toks2' = toks2
          rc = strip $ ctLayout

    (mkLayout,toks4) = case mk of
      Nothing -> ([],toks3)
      Just k@(GHC.L lk _) -> (rk,toks3')
        where
          (sk,kToks,toks3') = splitToks (ghcSpanStartEnd lk) toks3
          kindLayout = allocHsKind k kToks
          rk = strip $ (makeLeafFromToks sk) ++ kindLayout

    (s2,consToks,toks5) = splitToksForList cons toks4
    consLayout = allocList cons consToks allocConDecl

    (mderivsLayout,toks6) = case mderivs of
      Nothing -> ([],toks5)
      Just ds -> (rd,toksd)
        where
          (sd,derivToks,toksd) = splitToksForList ds toks5
          derivLayout = allocList ds derivToks allocType
          rd = strip $ (makeLeafFromToks sd) ++ derivLayout
    toks' = toks6
    r = strip $ (makeLeafFromToks s1) ++ ctxLayout ++ mcLayout ++ mkLayout
             ++ (makeLeafFromToks s2) ++ consLayout ++ mderivsLayout

-- ---------------------------------------------------------------------

allocConDecl :: GHC.LConDecl GHC.RdrName -> [PosToken] -> [LayoutTree]
allocConDecl (GHC.L l (GHC.ConDecl n@(GHC.L ln _) _expl qvars (GHC.L lc ctx) details res mdoc _)) toks = r
  where
    (s1,conDeclToks,toks') = splitToks (ghcSpanStartEnd l) toks
    (s2,nameToks,toks2) = splitToks (ghcSpanStartEnd ln) conDeclToks
    nameLayout = allocLocated n nameToks
    (qvarsLayout,toks3) = allocTyVarBndrs qvars toks2
    (s3,ctxToks,toks4) = splitToks (ghcSpanStartEnd lc) toks3
    ctxLayout = allocHsContext ctx ctxToks

    (detailsLayout,toks5) = allocHsConDeclDetails details toks4
    (resLayout,toks6) = case res of
      GHC.ResTyH98 -> ([],toks5)
      GHC.ResTyGADT (ty@(GHC.L lt _)) -> (rt,toks6')
        where
          (st,tyToks,toks6') = splitToks (ghcSpanStartEnd lt) toks5
          tyLayout = allocType ty tyToks
          rt = strip $ (makeLeafFromToks st) ++ tyLayout

    (docLayout,toks7) = case mdoc of
      Nothing -> ([],toks6)
      Just ds@(GHC.L ld _) -> (rd,toks7')
        where
          (sd,dsToks,toks7') = splitToks (ghcSpanStartEnd ld) toks6
          dsLayout = allocLocated ds dsToks
          rd = strip (makeLeafFromToks sd) ++ dsLayout

    r = strip $ (makeLeafFromToks s1) ++ (makeLeafFromToks s2)
             ++ nameLayout ++ qvarsLayout ++ (makeLeafFromToks s3)
             ++ ctxLayout ++ detailsLayout ++ resLayout
             ++ docLayout ++ (makeLeafFromToks toks7)
             ++ (makeLeafFromToks toks')

-- ---------------------------------------------------------------------

allocHsConDeclDetails :: GHC.HsConDeclDetails GHC.RdrName -> [PosToken] -> ([LayoutTree],[PosToken])
allocHsConDeclDetails (GHC.PrefixCon ds) toks = (r,toks')
  where
    (s1,dsToks,toks') = splitToksForList ds toks
    dsLayout = allocList ds dsToks allocLBangTypeName
    r = strip $ (makeLeafFromToks s1) ++ dsLayout
allocHsConDeclDetails (GHC.RecCon conDecls) toks = (r,toks')
  where
    (r,toks') = foldl' doOne ([],toks) conDecls

    doOne (acc,toksOne) cdf = (r1,toks2)
      where
        (lay,toks2) = allocConDeclField cdf toksOne
        r1 = acc ++ lay
allocHsConDeclDetails (GHC.InfixCon bt1@(GHC.L lb1 _) bt2@(GHC.L lb2 _)) toks = (r,toks')
  where
    (s1,bt1Toks,toks2) = splitToks (ghcSpanStartEnd lb1) toks
    (s2,bt2Toks,toks') = splitToks (ghcSpanStartEnd lb2) toks2
    bt1Layout = allocType bt1 bt1Toks
    bt2Layout = allocType bt2 bt2Toks

    r = strip $ (makeLeafFromToks s1) ++ bt1Layout
             ++ (makeLeafFromToks s2) ++ bt2Layout

-- ---------------------------------------------------------------------

allocConDeclField :: GHC.ConDeclField GHC.RdrName -> [PosToken] -> ([LayoutTree],[PosToken])
allocConDeclField = error "allocConDeclField undefined"

-- ---------------------------------------------------------------------

allocLBangTypeName :: GHC.LBangType GHC.RdrName -> [PosToken] -> [LayoutTree]
allocLBangTypeName bt toks = allocType bt toks

-- ---------------------------------------------------------------------

allocHsKind :: GHC.LHsKind GHC.RdrName -> [PosToken] -> [LayoutTree]
allocHsKind = error "allocHsKind undefined"

-- ---------------------------------------------------------------------

allocCType :: GHC.CType -> [PosToken] -> [LayoutTree]
allocCType = error "allocCType undefined"

-- ---------------------------------------------------------------------

allocHsContext :: GHC.HsContext GHC.RdrName -> [PosToken] -> [LayoutTree]
allocHsContext ts toks = r
  where
    r = allocList ts toks allocType

-- ---------------------------------------------------------------------

strip :: [LayoutTree] -> [LayoutTree]
strip ls = filter (not . emptyNode) ls
  where
    emptyNode (Node (Entry _ _ []) []) = True
    emptyNode _                        = False

-- ---------------------------------------------------------------------

allocList :: [GHC.Located b] -> [PosToken]
   -> (GHC.Located b -> [PosToken] -> [LayoutTree])
   -> [LayoutTree]
allocList xs toksIn allocFunc = r
  where
    (s2,listToks,toks2') = splitToksForList xs toksIn
    (layout,toks2) = ((makeLeafFromToks s2) ++ allocAll xs listToks,toks2')

    allocAll xs' toks = res
      where
        (declLayout,tailToks) = foldl' doOne ([],toks) xs'

        res = strip $ declLayout ++ (makeLeafFromToks tailToks)

        -- doOne :: ([LayoutTree],[PosToken]) -> GHC.Located a -> ([LayoutTree],[PosToken])
        doOne (acc,toksOne) x@(GHC.L l _) = r1
          where
            (s1,funcToks,toks') = splitToks (ghcSpanStartEnd l) toksOne
            layout' = (makeLeafFromToks s1) ++ [makeGroup (strip $ allocFunc x funcToks)]
            r1 = (acc ++ (strip layout'),toks')

    r = strip $ layout ++ (makeLeafFromToks toks2)

-- ---------------------------------------------------------------------

-- | Split the given tokens into the ones that occur prior to the start
-- of the list and ones that occur after
splitToksForList :: [GHC.Located a] -> [PosToken] -> ([PosToken],[PosToken],[PosToken])
splitToksForList [] toks = ([],[],toks)
splitToksForList xs toks = splitToks (getGhcLoc s, getGhcLocEnd e) toks
  where
    (GHC.L s _) = head xs
    (GHC.L e _) = last xs

-- ---------------------------------------------------------------------

placeAbove :: [LayoutTree] -> LayoutTree
placeAbove [] = error "placeAbove []"
placeAbove ls = Node (Entry loc Above []) ls
  where
    loc = combineSpans (getLoc $ head ls) (getLoc $ last ls)

-- ---------------------------------------------------------------------

placeOffset :: RowOffset -> ColOffset -> [LayoutTree] -> LayoutTree
placeOffset _ _ [] = error "placeOffset []"
placeOffset r c ls = Node (Entry loc (Offset r c) []) ls
  where
    loc = combineSpans (getLoc $ head ls) (getLoc $ last ls)

-- ---------------------------------------------------------------------

makeGroup :: [LayoutTree] -> LayoutTree
makeGroup ls = makeGroupLayout NoChange ls

makeGroupLayout :: Layout -> [LayoutTree] -> LayoutTree
makeGroupLayout lay ls = Node (Entry loc lay []) ls
  where
    loc = case ls of
           [] -> sf nullSrcSpan
           _  -> combineSpans (getLoc $ head ls) (getLoc $ last ls)

mkGroup :: GHC.SrcSpan -> Layout -> [LayoutTree] -> LayoutTree
mkGroup sspan lay subs = Node (Entry (sf sspan) lay []) subs

-- ---------------------------------------------------------------------

makeLeafFromToks :: [PosToken] -> [LayoutTree]
makeLeafFromToks [] = []
makeLeafFromToks toks = [Node (Entry loc NoChange toks) []]
  where
    -- TODO: ignore leading/trailing comments etc
    loc = combineSpans (sf $ tokenSrcSpan $ head toks) (sf $ tokenSrcSpan $ last toks)

makeLeaf :: GHC.SrcSpan -> Layout -> [PosToken] -> LayoutTree
makeLeaf sspan lay toks = Node (Entry (sf sspan) lay toks) []

-- ---------------------------------------------------------------------

getLoc :: LayoutTree -> ForestSpan
getLoc (Node (Entry l _ _) _) = l

-- ---------------------------------------------------------------------

retrieveTokens :: LayoutTree -> [PosToken]
retrieveTokens layout = go [] layout
  where
    -- go acc (Group _ _ xs)  = acc ++ (concat $ map (go []) xs)
    -- go acc (Leaf _ _ toks) = acc ++ toks
    go acc (Node (Entry _ _ []  ) xs) = acc ++ (concat $ map (go []) xs)
    go acc (Node (Entry _ _ toks)  _) = acc ++ toks

-- ---------------------------------------------------------------------
