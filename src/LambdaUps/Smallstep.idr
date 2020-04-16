module LambdaUps.Smallstep

import Data.List
import Iter
import Subset

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LambdaUps.Term

%default total
%access public export

isVal : TermU g a -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

step : TermU g a -> Maybe (TermU g a)
step (App (Lam t) u )                 = Just $ Let t (Slash u)
step (App  t      u )                 =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step (Let (App t u)         s       ) = Just $ App (Let t s) (Let u s)
step (Let (Lam t)           s       ) = Just $ Lam (Let t (Lift s))
step (Let (Var  Here)      (Slash t)) = Just $ t
step (Let (Var (There el)) (Slash _)) = Just $ Var el
step (Let (Var  Here)      (Lift _) ) = Just $ Var Here
step (Let (Var (There el)) (Lift s) ) = Just $ Let (Let (Var el) s) Shift
step (Let (Var  el)         Shift   ) = Just $ Var (There el)
step  _                               = Nothing

stepIter : Term [] a -> (Nat, TermU [] a)
stepIter = iterCount step . encode
