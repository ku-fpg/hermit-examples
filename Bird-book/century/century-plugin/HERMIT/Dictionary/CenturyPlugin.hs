module HERMIT.Dictionary.CenturyPlugin (plugin) where

import Control.Arrow ((<<<))
import Control.Monad.IO.Class (MonadIO)

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Plugin

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Reasoning
import HERMIT.Dictionary.Undefined (verifyStrictT)

import HERMIT.Shell.Proof

-------------------------------------------------

plugin :: Plugin
plugin = hermitPlugin (interactive exts)

exts :: [External]
exts =
    [ external "foldr-fusion-proof" foldrFusionProof
      [ "Given rewrites proving that: (i) f is strict, (ii) f a = b, (iii) f (g x y) = h x (f y), then",
        "f . foldr g a  ==  foldr h b"
      ]
    ]

-------------------------------------------------

foldrFusionProof :: RewriteH Core -> RewriteH Core -> RewriteH Core -> UserProofTechnique
foldrFusionProof r1 r2 r3 = userProofTechnique $ foldrFusionProofR (extractR r1) (extractR r2) (extractR r3)

-- | foldr fusion
--
-- f :: A -> B
-- g :: C -> A -> A
-- h :: C -> B -> B
-- a :: A
-- b :: B
--
-- strict f    /\    f a = b    /\    forall x y. f (g x y) = h x (f y)
-----------------------------------------------------------------------
--           f . foldr g a = foldr h b
--
foldrFusionProofR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr -> TransformH CoreExprEquality ()
foldrFusionProofR fstrict pbase pstep = prefixFailMsg "foldr-fusion-proof failed: " $
  do CoreExprEquality vs lhs rhs <- idR

     withPatFailMsg "Lemma does not have the form:  f . foldr g a = foldr h b" $
       do App (App compE f) (App (App foldrElhs g) a) <- return lhs
          App (App foldrErhs h) b                     <- return rhs

          isCompValT  <<< return compE
          isFoldrValT <<< return foldrElhs
          isFoldrValT <<< return foldrErhs

          tyA      <- exprTypeM a
          (tyC,_)  <- funExprArgResTypes g

          v_x <- constT (newIdH "x" tyC)
          v_y <- constT (newIdH "y" tyA)

          let withScope = withVarsInScope (vs ++ [v_x,v_y])
              x = Var v_x
              y = Var v_y

          prefixFailMsg "precondition (i) failed: "   $ verifyStrictT f (withScope fstrict)
          prefixFailMsg "precondition (ii) failed: "  $ verifyEqualityLeftToRightT (App f a) b (withScope pbase)
          prefixFailMsg "precondition (iii) failed: " $ verifyEqualityLeftToRightT (App f (App (App g x) y))
                                                                                   (App (App h x) (App f y))
                                                                                   (withScope pstep)

-------------------------------------------------

foldrLocation :: String
foldrLocation = "Data.List.foldr"

-- TODO: will crash if 'foldr' is not used (or explicitly imported) in the source file.
findFoldrIdT :: (BoundVars c, HasModGuts m, HasHscEnv m, MonadCatch m, HasDynFlags m, MonadThings m, MonadIO m) => Translate c m a Id
findFoldrIdT = findIdT foldrLocation

-- | Check if the current expression is \"foldr\" fully saturated with type arguments.
isFoldrValT :: (BoundVars c, HasModGuts m, HasHscEnv m, MonadCatch m, HasDynFlags m, MonadThings m, MonadIO m) => Translate c m CoreExpr ()
isFoldrValT = prefixFailMsg "not a foldr expression fully saturated with type arguments: " $
                  withPatFailMsg (wrongExprForm "foldr ty1 ty2") $
                  do App (App (Var f) (Type _)) (Type _) <- idR
                     f' <- findFoldrIdT
                     guardMsg (f == f') ("identifier is not " ++ foldrLocation)

-------------------------------------------------

compLocation :: String
compLocation = "Data.Function.." -- parentheses not needed

-- TODO: will crash if '(.)' is not used (or explicitly imported) in the source file.
findCompIdT :: (BoundVars c, HasModGuts m, HasHscEnv m, MonadCatch m, HasDynFlags m, MonadThings m, MonadIO m) => Translate c m a Id
findCompIdT = findIdT compLocation

-- | Check if the current expression is \"(.)\" fully saturated with type arguments.
isCompValT :: (BoundVars c, HasModGuts m, HasHscEnv m, MonadCatch m, HasDynFlags m, MonadThings m, MonadIO m) => Translate c m CoreExpr ()
isCompValT = prefixFailMsg "not a composition expression fully saturated with type arguments: " $
                  withPatFailMsg (wrongExprForm "(.) ty1 ty2 ty3") $
                  do App (App (App (Var f) (Type _)) (Type _)) (Type _) <- idR
                     f' <- findCompIdT
                     guardMsg (f == f') ("identifier is not " ++ compLocation)

-------------------------------------------------
