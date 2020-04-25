module LambdaUps.PCF.Smallstep

import Data.List
import Iter
import Subset

import Lambda.STLC.Ty
import PCF.Term
import LambdaUps.PCF.Term

%default total
%access public export

isVal : TermU g a -> Bool
isVal (Lam _)  = True
isVal (Var _)  = True
isVal  Zero    = True
isVal (Succ n) = isVal n
isVal  _       = False

step : TermU g a -> Maybe (TermU g a)
step (App (Lam t) u )                 = Just $ Let t (Slash u)
step (App  t      u )                 =
  if isVal t
    then Nothing
    else [| LambdaUps.PCF.Term.App (step t) (pure u) |]
step (Succ m)                         = Succ <$> step m
step (If0  Zero    t f)               = Just t
step (If0 (Succ n) t f)               = Just $ Let f (Slash n)
step (If0 p t f)                      = (\q => If0 q t f) <$> step p
step (Fix f)                          = Just $ Let f (Slash $ Fix f)
step (Let (Lam t)           s       ) = Just $ Lam (Let t (Lift s))
step (Let (App t u)         s       ) = Just $ App (Let t s) (Let u s)
step (Let  Zero             s       ) = Just Zero
step (Let (Succ t)          s       ) = Just $ Succ $ Let t s
step (Let (If0 b t f)       s       ) = Just $ If0 (Let b s) (Let t s) (Let f (Lift s))
step (Let (Fix f)           s       ) = Just $ Fix (Let f (Lift s))
step (Let (Var  Here)      (Slash t)) = Just t
step (Let (Var (There el)) (Slash _)) = Just $ Var el
step (Let (Var  Here)      (Lift _) ) = Just $ Var Here
step (Let (Var (There el)) (Lift s) ) = Just $ Let (Let (Var el) s) Shift
step (Let (Var  el)         Shift   ) = Just $ Var (There el)
step (Let  t                s       ) = [| Let (step t) (pure s) |]
step  _                               = Nothing

stepIter : Term [] a -> (Nat, TermU [] a)
stepIter = iterCount step . encode
