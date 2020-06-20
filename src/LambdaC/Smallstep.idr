module LambdaC.Smallstep

import Data.List
import Iter
import Subset

import Lambda.STLC.Ty
import LambdaC.Term

import Lambda.STLC.Term

%default total
%access public export

-- substitution on terms

Subst : List Ty -> List Ty -> Type
Subst g d = {x : Ty} -> Elem x g -> Tm d x

exts : Subst g d -> Subst (b::g) (b::d)
exts _  Here      = V $ Var Here
exts s (There el) = renameTm There (s el)

mutual
  substVal : Subst g d -> Val g a -> Tm d a
  substVal s (Var el)    = s el
  substVal s (Lam t)     = V $ Lam $ substTm (exts s) t

  substTm : Subst g d -> Tm g a -> Tm d a
  substTm s (V v)     = substVal s v
  substTm s (App t u) = App (substTm s t) (substTm s u)
  substTm s (Let m n) = Let (substTm s m) (substTm (exts s) n)

Sub1 : Tm g a -> Subst (a::g) g
Sub1 s  Here      = s
Sub1 s (There el) = V $ Var el

subst1 : Tm (a::g) b -> Tm g a -> Tm g b
subst1 t s = substTm (Sub1 s) t

-- substitution on values

SubstV : List Ty -> List Ty -> Type
SubstV g d = {x : Ty} -> Elem x g -> Val d x

extsV : SubstV g d -> SubstV (b::g) (b::d)
extsV s  Here      = Var Here
extsV s (There el) = renameVal There (s el)

mutual
  substValV : SubstV g d -> Val g a -> Val d a
  substValV s (Var el)    = s el
  substValV s (Lam t)     = Lam $ substTmV (extsV s) t

  substTmV : SubstV g d -> Tm g a -> Tm d a
  substTmV s (V v)     = V $ substValV s v
  substTmV s (App t u) = App (substTmV s t) (substTmV s u)
  substTmV s (Let m n) = Let (substTmV s m) (substTmV (extsV s) n)

Sub1V : Val g a -> SubstV (a::g) g
Sub1V s  Here      = s
Sub1V s (There el) = Var el

subst1V : Val (a::g) b -> Val g a -> Val g b
subst1V t s = substValV (Sub1V s) t

-- reduction

step : Tm g a -> Maybe (Tm g a)
step (App   (V (Lam m))  n            ) = Just $ Let n m
step (App v@(V _)        n            ) = Just $ Let n (App (renameTm There v) (V $ Var Here))
step (App m              n            ) = Just $ Let m (App (V $ Var Here) (renameTm There n))
step (Let v@(V _)        m            ) = Just $ subst1 m v
step (Let m             (V (Var Here))) = Just m
step (Let   (Let m n)    p            ) = Just $ Let m (Let n (renameTm (ext There) p))
step (Let m              n            ) = [| Let (step m) (pure n) |]
step  _                                 = Nothing

stepIter : Tm [] a -> (Nat, Tm [] a)
stepIter = iterCount step

-- tests

private
test1 : stepIter (encodeLC TestTm0) = (2, encodeLC ResultTm)
test1 = Refl

private
test2 : stepIter (encodeLC TestTm1) = (7, encodeLC ResultTm)
test2 = Refl

private
test3 : stepIter (encodeLC TestTm2) = (4, encodeLC ResultTm)
test3 = Refl
