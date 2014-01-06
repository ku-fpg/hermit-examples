module CenturyPlugin (plugin) where

import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Optimize

-------------------------------------------------

plugin :: Plugin
plugin = optimize (interactive exts)

exts :: [External]
exts =
    [ external "foldr-fusion" ((\ r1 r2 r3 -> foldrFusion (Just (r1,r2,r3))) :: RewriteH Core -> RewriteH Core -> RewriteH Core -> BiRewriteH Core)
      [ "Given proofs that: (i) f is strict, (ii) f a = b, (iii) f (g x y) = h x (f y), then",
        "f . foldr g a  <=>  foldr h b"
      ]
    , external "foldr-fusion-unsafe" (foldrFusion Nothing :: BiRewriteH Core)
      [ "f . foldr g a  <=>  foldr h b",
        "The following three preconditions are assumed to hold:",
        "(i) f is strict, (ii) f a = b, (iii) f (g x y) = h x (f y)"
      ]
    ]

-------------------------------------------------

foldrFusion :: Maybe (RewriteH Core, RewriteH Core, RewriteH Core) -> BiRewriteH Core
foldrFusion = promoteExprBiR . foldrFusionR . fmap (\ (r1,r2,r3) -> (extractR r1, extractR r2, extractR r3))

-- foldr fusion
--
-- strict f   /\   f a = b   /\   f (g x y) = h x (f y)
-------------------------------------------------------
-- |         f . foldr g a = foldr h b
--
foldrFusionR :: Monad m => Maybe (Rewrite c m CoreExpr, Rewrite c m CoreExpr, Rewrite c m CoreExpr) -> BiRewrite c m CoreExpr
foldrFusionR _ = bidirectional idR idR -- TODO

-------------------------------------------------
