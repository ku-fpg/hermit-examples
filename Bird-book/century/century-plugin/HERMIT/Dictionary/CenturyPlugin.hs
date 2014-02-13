{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Dictionary.CenturyPlugin (plugin) where

import Control.Applicative ((<$>))
import Control.Arrow ((<<<))

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Optimize
import HERMIT.ParserCore (parse5beforeBiR)
import HERMIT.Utilities

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Reasoning (verifyEqualityLeftToRightT)
import HERMIT.Dictionary.Undefined (verifyStrictT)

-------------------------------------------------

plugin :: Plugin
plugin = optimize (interactive exts)

exts :: [External]
exts =
    [ external "foldr-fusion" ((\ f g h a b r1 r2 r3 -> foldrFusion (Just (r1,r2,r3)) f g h a b) :: CoreString -> CoreString -> CoreString -> CoreString -> CoreString -> RewriteH Core -> RewriteH Core -> RewriteH Core -> BiRewriteH Core)
      [ "Given proofs that: (i) f is strict, (ii) f a = b, (iii) f (g x y) = h x (f y), then",
        "f . foldr g a  <=>  foldr h b"
      ]
    , external "foldr-fusion-unsafe" (foldrFusion Nothing :: CoreString -> CoreString -> CoreString -> CoreString -> CoreString -> BiRewriteH Core)
      [ "f . foldr g a  <=>  foldr h b",
        "The following three preconditions are assumed to hold:",
        "(i) f is strict, (ii) f a = b, (iii) f (g x y) = h x (f y)"
      ]
    ]

-------------------------------------------------

foldrFusion :: Maybe (RewriteH Core, RewriteH Core, RewriteH Core) -> CoreString -> CoreString -> CoreString -> CoreString -> CoreString -> BiRewriteH Core
foldrFusion mp f g h a b = promoteExprBiR $ parse5beforeBiR (foldrFusionR $ fmap (\ (r1,r2,r3) -> (extractR r1, extractR r2, extractR r3)) mp) f g h a b

-- | foldr fusion
--
-- strict f    /\    f a = b    /\    forall x y. f (g x y) = h x (f y)
-----------------------------------------------------------------------
--           f . foldr g a = foldr h b
--
foldrFusionR :: forall c. (BoundVars c, HasGlobalRdrEnv c)
             => Maybe (Rewrite c HermitM CoreExpr, Rewrite c HermitM CoreExpr, Rewrite c HermitM CoreExpr)
             -> CoreExpr -- f :: A -> B
             -> CoreExpr -- g :: C -> A -> A
             -> CoreExpr -- h :: C -> B -> B
             -> CoreExpr -- a :: A
             -> CoreExpr -- b :: B
             -> BiRewrite c HermitM CoreExpr
foldrFusionR mp f g h a b = beforeBiR
                              (do
                                  tyA         <- exprTypeM a
                                  tyB         <- exprTypeM b
                                  (tyA',tyB') <- funExprArgResTypes f
                                  (tyC,tyAA)  <- funExprArgResTypes g
                                  (tyC',tyBB) <- funExprArgResTypes h
                                  tyA''       <- endoFunType tyAA
                                  tyB''       <- endoFunType tyBB
                                  guardMsg (equivalentBy eqType [tyA,tyA',tyA'']) "type mismatch (A)"
                                  guardMsg (equivalentBy eqType [tyB,tyB',tyB'']) "type mismatch (B)"
                                  guardMsg (eqType tyC tyC') "type mismatch (C)"
                                  case mp of
                                    Nothing                    -> return ()
                                    Just (fstrict,pbase,pstep) -> do x <- constT (Var <$> newIdH "x" tyC)
                                                                     y <- constT (Var <$> newIdH "y" tyA)
                                                                     verifyStrictT f fstrict
                                                                     verifyEqualityLeftToRightT (App f a) b pbase
                                                                     verifyEqualityLeftToRightT (App f (App (App g x) y))
                                                                                                (App (App h x) (App f y))
                                                                                                pstep
                                  return (tyA,tyB,tyC)
                              )
                              (\ tys -> bidirectional (ffL tys) (ffR tys))
  where
    ffL :: (Type,Type,Type) -> Rewrite c HermitM CoreExpr
    ffL (_,tyB,tyC) =
          do App (App compE f') (App (App foldrElhs g') a') <- idR
             guardMsg (exprAlphaEq f f' && exprAlphaEq g g' && exprAlphaEq a a') "Given functions do not match current expression."
             isCompValT  <<< return compE
             isFoldrValT <<< return foldrElhs
             foldrId <- findFoldrIdT
             let foldrErhs = mkCoreApps (Var foldrId) [Type tyC, Type tyB]
             return $ mkCoreApps foldrErhs [h,b]

    ffR :: (Type,Type,Type) -> Rewrite c HermitM CoreExpr
    ffR (tyA,tyB,tyC) =
          do App (App foldrErhs h') b' <- idR
             guardMsg (exprAlphaEq h h' && exprAlphaEq b b') "Given functions do not match current expression."
             isFoldrValT <<< return foldrErhs
             compId    <- findCompIdT
             let compE = mkCoreApps (Var compId) [Type tyA, Type tyB, Type (mkListTy tyC)]
             foldrId <- findFoldrIdT
             let foldrElhs = mkCoreApps (Var foldrId) [Type tyC, Type tyA]
             return $ mkCoreApps compE [f, mkCoreApps foldrElhs [g,a] ]

-- (.) :: (Y Z X   :: *) -> (Y -> Z) -> (X   -> Y) -> X   -> Z
-- (.) :: (A B [C] :: *) -> (A -> B) -> ([C] -> A) -> [C] -> B

-------------------------------------------------

-- TODO: check this
foldrLocation :: String
foldrLocation = "Data.List.foldr"

-- TODO: will crash if 'foldr' is not used (or explicitly imported) in the source file.
findFoldrIdT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Translate c m a Id
findFoldrIdT = findIdT foldrLocation

-- | Check if the current expression is \"foldr\" fully saturated with type arguments.
isFoldrValT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Translate c m CoreExpr ()
isFoldrValT = prefixFailMsg "not a foldr expression fully saturated with type arguments: " $
                  withPatFailMsg (wrongExprForm "foldr ty1 ty2") $
                  do App (App (Var f) (Type _)) (Type _) <- idR
                     f' <- findFoldrIdT
                     guardMsg (f == f') ("identifier is not " ++ foldrLocation)

-------------------------------------------------

-- TODO: check this
compLocation :: String
compLocation = "Data.Function.(.)"

-- TODO: will crash if '(.)' is not used (or explicitly imported) in the source file.
findCompIdT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Translate c m a Id
findCompIdT = findIdT compLocation

-- | Check if the current expression is \"(.)\" fully saturated with type arguments.
isCompValT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Translate c m CoreExpr ()
isCompValT = prefixFailMsg "not a composition expression fully saturated with type arguments: " $
                  withPatFailMsg (wrongExprForm "(.) ty1 ty2 ty3") $
                  do App (App (App (Var f) (Type _)) (Type _)) (Type _) <- idR
                     f' <- findCompIdT
                     guardMsg (f == f') ("identifier is not " ++ compLocation)

-------------------------------------------------
