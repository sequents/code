module Lambda.STLC.CK

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term
import Lambda.STLC.Smallstep

%default total
%access public export

-- left-to-right, no environment

-- evaluation contexts
data Stack : List Ty -> Ty -> Ty -> Type where
  Mt : Stack g a a
  Arg : Term g a -> Stack g b c -> Stack g (a~>b) c
  Fun : Term (a::g) b -> Stack g b c -> Stack g a c

record State (g : List Ty) (b : Ty) where
  constructor St
  tm : Term g a
  stk : Stack g a b

step : State g a -> Maybe (State g a)
step (St (App t u)        s ) = Just $ St  t           (Arg u s)
step (St (Lam t)   (Arg u s)) = Just $ St  u           (Fun t s)
step (St  t        (Fun u s)) = Just $ St (subst1 u t)        s
step  _                       = Nothing

runCK : Term g a -> (Nat, State g a)
runCK t = iterCount step (St t Mt)

private
test0 : runCK TestTm0 = (3, St ResultTm Mt)f
test0 = Refl

private
test1 : runCK TestTm1 = (6, St ResultTm Mt)
test1 = Refl

private
test2 : runCK TestTm2 = (6, St ResultTm Mt)
test2 = Refl
