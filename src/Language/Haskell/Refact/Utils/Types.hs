module Language.Haskell.Refact.Utils.Types
       (
        ApplyRefacResult
       , RefacResult(..)
       , RefacSource(..)
       -- *
       , TreeId(..)
       , mainTid
       , TokenCache(..)
       , SimpPos
       , SimpSpan
       , Positioning(..)
       , NameMap

       -- , ghead
       -- , glast
       -- , gtail
       -- , gfromJust
       ) where

import qualified GHC      as GHC

import Language.Haskell.GHC.ExactPrint
-- import Language.Haskell.GHC.ExactPrint.Types
-- import Language.Haskell.GHC.ExactPrint.Utils

import qualified Data.Map as Map


-- ---------------------------------------------------------------------
-- | The result of a refactoring is the file, a flag as to whether it
-- was modified, and the updated AST
type ApplyRefacResult = ((FilePath, RefacResult), (Anns,GHC.ParsedSource))

data RefacResult = RefacModified | RefacUnmodified
                 deriving (Show,Ord,Eq)


data RefacSource = RSFile FilePath
                 | RSMod GHC.ModSummary
                 | RSAlreadyLoaded

-- ---------------------------------------------------------------------

data TreeId = TId !Int deriving (Eq,Ord,Show)

-- |Identifies the tree carrying the main tokens, not any work in
-- progress or deleted ones
mainTid :: TreeId
mainTid = TId 0

data TokenCache a = TK
  { tkCache :: !(Map.Map TreeId a)
  , tkLastTreeId :: !TreeId
  } deriving (Show)

type SimpPos = (Int,Int) -- Line, column
type SimpSpan = (SimpPos,SimpPos)

-- |How new SrcSpans should be inserted in the Token tree, relative to
-- the prior span
data Positioning = PlaceAdjacent -- ^Only a single space between the
                   -- end of the prior span and the new one
                 | PlaceAbsolute !Int !Int -- ^Start at the specified
                   -- line and col
                 | PlaceAbsCol !Int !Int !Int -- ^Line offset and
                                              -- absolute Col. Mainly
                                              -- for forcing start at
                                              -- left margin, number
                                              -- of lines to add at
                                              -- the end
                 | PlaceOffset !Int !Int !Int -- ^Line and Col offset for
                   -- start, num lines to add at the end
                   -- relative to the indent level of the prior span
                 | PlaceIndent !Int !Int !Int -- ^Line and Col offset for
                   -- start, num lines to add at the end
                   -- relative to the indent level of the prior line
                 deriving (Show)


-- ---------------------------------------------------------------------

type NameMap = Map.Map GHC.SrcSpan GHC.Name

-- ---------------------------------------------------------------------
-- Putting these here for the time being, to avoid import loops
{-}
ghead :: String -> [a] -> a
ghead  info []    = error $ "ghead "++info++" []"
ghead _info (h:_) = h

glast :: String -> [a] -> a
glast  info []    = error $ "glast " ++ info ++ " []"
glast _info h     = last h

gtail :: String -> [a] -> [a]
gtail  info []   = error $ "gtail " ++ info ++ " []"
gtail _info h    = tail h

gfromJust :: [Char] -> Maybe a -> a
gfromJust _info (Just h) = h
gfromJust  info Nothing = error $ "gfromJust " ++ info ++ " Nothing"
-}
