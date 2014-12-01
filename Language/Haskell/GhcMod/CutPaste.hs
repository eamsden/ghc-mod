module Language.Haskell.GhcMod.CutPaste (
    tree
  , freeVars
  ) where

import Control.Applicative ((<$>))
import Data.Generics.Aliases (extQ)
import Data.Generics.Text (gshow)
import Data.Data
import Data.Maybe (listToMaybe)
import Data.List (intersperse)
import Control.Exception (catch,SomeException(),evaluate)
import Exception (ghandle, SomeException(..))
import GHC (GhcMonad, LHsBind, LHsExpr, LPat, Id, TypecheckedModule(..), TypecheckedSource, unLoc)
import Name (getOccString)
import Var (Var())
import VarSet (varSetElems)
import qualified GHC as G
import qualified Outputable as O
import qualified Language.Haskell.GhcMod.Gap as Gap
import Language.Haskell.GhcMod.Monad
import Language.Haskell.GhcMod.SrcUtils
import Language.Haskell.GhcMod.Types
import Language.Haskell.GhcMod.Convert
import System.IO.Unsafe (unsafePerformIO)

----------------------------------------------------------------
-- HACK: print out the AST, setting off bombs inside a
--   containment vessel

bombSquad :: a -> (String -> String) -> (String -> String)
bombSquad bomb ss = unsafePerformIO $ 
                      catch
                        (do evaluate bomb
                            return ss)
                        (\e -> const (return ('\x2691':)) (e :: SomeException))


gshowsBombSquad :: (Data a) => a -> ShowS
gshowsBombSquad = 
  (\t -> bombSquad t (
             showChar '('
           . (showString . showConstr . toConstr $ t)
           . (foldr (.) id . gmapQ (((' ' :) .) . gshowsBombSquad) $ t)
           . showChar ')')
  ) `extQ` (showString :: String -> ShowS) `extQ` (showString . getOccString :: Var -> ShowS)

gshowBombSquad :: (Data a) => a -> String
gshowBombSquad t = gshowsBombSquad t ""

----------------------------------------------------------------

-- | Getting the TCed source
tree :: IOish m
        => FilePath     -- ^ A target file.
        -> G.SrcSpan
        -> GhcModT m String
tree file span = do
    opt <- options
    convert opt <$> ghandle handler body
  where
    body = inModuleContext file $ \dflag style -> do
        modSum <- Gap.fileModSummary file
        mExpr <- getSrc modSum span
        return $ maybe "No exprs in span" gshowBombSquad mExpr
    handler (SomeException _) = return "Cannot show span exprs"


getSrc :: GhcMonad m => G.ModSummary -> G.SrcSpan -> m (Maybe (LHsExpr Id))
getSrc modSum span = do
    p <- G.parseModule modSum
    TypecheckedModule{tm_typechecked_source = tcs} <- G.typecheckModule p
    return $ listToMaybe $ (listifyContained tcs span :: [LHsExpr Id])

-- | Get the free variables in a source span
freeVars :: IOish m
            => FilePath
            -> G.SrcSpan
            -> GhcModT m String
freeVars file span = do
  opt <- options
  convert opt <$> ghandle handler body
  where
    body = inModuleContext file $ \dflag style -> do
        modSum <- Gap.fileModSummary file
        mExpr <- getSrc modSum span
        return $ maybe "No exprs in span" (concat . intersperse ", " . map getOccString . varSetElems . hsFreeVars . unLoc) mExpr
    handler (SomeException _) = return "Cannot show span vars"
