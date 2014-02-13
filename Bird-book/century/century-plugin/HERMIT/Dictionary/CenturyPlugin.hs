{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Dictionary.CenturyPlugin (plugin) where

import HERMIT.ParserCore (parse5beforeBiR)
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Optimize

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

-- foldr fusion
--
-- strict f   /\   f a = b   /\   f (g x y) = h x (f y)
-------------------------------------------------------
-- |         f . foldr g a = foldr h b
--
foldrFusionR :: forall c m. Monad m
             => Maybe (Rewrite c m CoreExpr, Rewrite c m CoreExpr, Rewrite c m CoreExpr)
             -> CoreExpr -- f
             -> CoreExpr -- g
             -> CoreExpr -- h
             -> CoreExpr -- a
             -> CoreExpr -- b
             -> BiRewrite c m CoreExpr
foldrFusionR mp f g h a b = beforeBiR
                              (case mp of
                                 Nothing                    -> return ()
                                 Just (fstrict,pbase,pstep) -> do verifyStrictT f fstrict
                                                                  verifyEqualityLeftToRightT (App f a) b pbase
                                                                  verifyEqualityLeftToRightT (App f (App (App g x) y))
                                                                                             (App (App h x) (App f y))
                                                                                             pbase
                              )
                              (\ _ -> bidirectional ffL ffR)
  where
    ffL :: Rewrite c m CoreExpr
    ffL = idR

    ffR :: Rewrite c m CoreExpr
    ffR = idR

-- TODO: Need types!

-------------------------------------------------
