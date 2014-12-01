{-# LANGUAGE TupleSections, FlexibleInstances, Rank2Types, GADTs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Haskell.GhcMod.SrcUtils where

import Control.Applicative ((<$>))
import CoreUtils (exprType)
import Data.Generics hiding (Fixity)
import Data.Maybe (fromMaybe)
import Data.Ord as O
import GHC (LHsExpr, LPat, Id, DynFlags, SrcSpan, Type, Located, ParsedSource, RenamedSource, TypecheckedSource, GenLocated(L),Fixity(),unLoc)
import qualified GHC as G
import GHC.SYB.Utils (Stage(..), everythingStaged, somethingStaged)
import GhcMonad
import qualified Language.Haskell.Exts.Annotated as HE
import Language.Haskell.GhcMod.Doc (showOneLine, getStyle)
import Language.Haskell.GhcMod.DynFlags
import Language.Haskell.GhcMod.Gap (HasType(..), setWarnTypedHoles, setDeferTypeErrors)
import qualified Language.Haskell.GhcMod.Gap as Gap
import Language.Haskell.GhcMod.Monad (IOish, GhcModT)
import Language.Haskell.GhcMod.Target (setTargetFiles)
import OccName (OccName)
import Outputable (PprStyle)
import TcHsSyn (hsPatType)
import HsExpr(HsExpr(..), Match(..))
import NameSet(NameSet())
import Var(Var(), isLocalVar)
import VarSet
import HsPat(Pat(..))
import HsLit(PostTcType)

----------------------------------------------------------------

instance HasType (LHsExpr Id) where
    getType tcm e = do
        hs_env <- G.getSession
        mbe <- liftIO $ Gap.deSugar tcm e hs_env
        return $ (G.getLoc e, ) <$> CoreUtils.exprType <$> mbe

instance HasType (LPat Id) where
    getType _ (G.L spn pat) = return $ Just (spn, hsPatType pat)

----------------------------------------------------------------

listifyContained :: Typeable a => TypecheckedSource -> SrcSpan -> [Located a]
listifyContained tcs span = listifyStaged TypeChecker p tcs
  where
    p (L spn _) = spn `G.isSubspanOf` span

listifySpans :: Typeable a => TypecheckedSource -> (Int, Int) -> [Located a]
listifySpans tcs lc = listifyStaged TypeChecker p tcs
  where
    p (L spn _) = G.isGoodSrcSpan spn && spn `G.spans` lc

listifyParsedSpans :: Typeable a => ParsedSource -> (Int, Int) -> [Located a]
listifyParsedSpans pcs lc = listifyStaged Parser p pcs
  where
    p (L spn _) = G.isGoodSrcSpan spn && spn `G.spans` lc

listifyRenamedSpans :: Typeable a => RenamedSource -> (Int, Int) -> [Located a]
listifyRenamedSpans pcs lc = listifyStaged Renamer p pcs
  where
    p (L spn _) = G.isGoodSrcSpan spn && spn `G.spans` lc

listifyStaged :: Typeable r => Stage -> (r -> Bool) -> GenericQ [r]
listifyStaged s p = everythingStaged s (++) [] ([] `mkQ` (\x -> [x | p x]))

cmp :: SrcSpan -> SrcSpan -> Ordering
cmp a b
  | a `G.isSubspanOf` b = O.LT
  | b `G.isSubspanOf` a = O.GT
  | otherwise           = O.EQ

toTup :: DynFlags -> PprStyle -> (SrcSpan, Type) -> ((Int,Int,Int,Int),String)
toTup dflag style (spn, typ) = (fourInts spn, pretty dflag style typ)

fourInts :: SrcSpan -> (Int,Int,Int,Int)
fourInts = fromMaybe (0,0,0,0) . Gap.getSrcSpan

fourIntsHE :: HE.SrcSpan -> (Int,Int,Int,Int)
fourIntsHE loc = ( HE.srcSpanStartLine loc, HE.srcSpanStartColumn loc
                 , HE.srcSpanEndLine loc, HE.srcSpanEndColumn loc)

-- Check whether (line,col) is inside a given SrcSpanInfo
typeSigInRangeHE :: Int -> Int -> HE.Decl HE.SrcSpanInfo -> Bool
typeSigInRangeHE lineNo colNo (HE.TypeSig (HE.SrcSpanInfo s _) _ _) =
  HE.srcSpanStart s <= (lineNo, colNo) && HE.srcSpanEnd s >= (lineNo, colNo)
typeSigInRangeHE lineNo colNo (HE.TypeFamDecl (HE.SrcSpanInfo s _) _ _) =
  HE.srcSpanStart s <= (lineNo, colNo) && HE.srcSpanEnd s >= (lineNo, colNo)
typeSigInRangeHE lineNo colNo (HE.DataFamDecl (HE.SrcSpanInfo s _) _ _ _) =
  HE.srcSpanStart s <= (lineNo, colNo) && HE.srcSpanEnd s >= (lineNo, colNo)
typeSigInRangeHE _  _ _= False

pretty :: DynFlags -> PprStyle -> Type -> String
pretty dflag style = showOneLine dflag style . Gap.typeForUser

----------------------------------------------------------------

inModuleContext :: IOish m
                => FilePath
                -> (DynFlags -> PprStyle -> GhcModT m a)
                -> GhcModT m a
inModuleContext file action =
    withDynFlags (setWarnTypedHoles . setDeferTypeErrors . setNoWarningFlags) $ do
    setTargetFiles [file]
    Gap.withContext $ do
        dflag <- G.getSessionDynFlags
        style <- getStyle
        action dflag style

----------------------------------------------------------------

showName :: DynFlags -> PprStyle -> G.Name -> String
showName dflag style name = showOneLine dflag style $ Gap.nameForUser name

showOccName :: DynFlags -> PprStyle -> OccName -> String
showOccName dflag style name = showOneLine dflag style $ Gap.occNameForUser name

----------------------------------------------------------------

avoidPotholes :: Stage -> a -> GenericQ a -> GenericQ a
avoidPotholes stage x f = ((f `extQ` avoidNameSet stage x f) `extQ` avoidPostTcType stage x f) `extQ` avoidFixity stage x f

avoidNameSet :: Stage -> a -> GenericQ a -> NameSet -> a
avoidNameSet stage x f | stage `elem` [Parser,TypeChecker] = const x
                       | otherwise                         = f

avoidPostTcType :: Stage -> a -> GenericQ a -> PostTcType -> a
avoidPostTcType stage x f | stage < TypeChecker = const x
                          | otherwise           = f

avoidFixity :: Stage -> a -> GenericQ a -> Fixity -> a
avoidFixity stage x f | stage < Renamer = const x
                      | otherwise       = f 

hsFreeVars' :: (Data a) => a -> VarSet
hsFreeVars' x = unionVarSets $ gmapQ (avoidPotholes TypeChecker emptyVarSet $ (hsFreeVars' `extQ` hsFreeVars) `extQ` matchFreeVars) x

hsFreeVars :: HsExpr Var -> VarSet
hsFreeVars (HsVar x) | isLocalVar x = unitVarSet x
                     | otherwise = emptyVarSet
hsFreeVars hse = hsFreeVars' hse

patVars' :: (Data a) => a -> VarSet
patVars' x = unionVarSets $ gmapQ (avoidPotholes TypeChecker emptyVarSet $ patVars' `extQ` patVars) x

patVars :: Pat Var -> VarSet
patVars (VarPat x) = unitVarSet x
                   
patVars p = patVars' p 

matchFreeVars :: Match Var (LHsExpr Var) -> VarSet
matchFreeVars (Match pats _ rhs) = hsFreeVars' rhs `minusVarSet` (unionVarSets $ map (patVars . unLoc) pats)

----------------------------------------------------------------

