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
  NS : Stack g a a
  AS : Term g a -> Stack g b c -> Stack g (a~>b) c
  FS : Term (a::g) b -> Stack g b c -> Stack g a c

record State (g : List Ty) (b : Ty) where
  constructor St
  tm : Term g a
  stk : Stack g a b

step : State g a -> Maybe (State g a)
step (St (App t u)       s ) = Just $ St  t           (AS u s)
step (St (Lam t)   (AS u s)) = Just $ St  u           (FS t s)
step (St  t        (FS u s)) = Just $ St (subst1 u t)       s
step  _                      = Nothing

runCK : Term g a -> (Nat, State g a)
runCK t = iterCount step (St t NS)

private
test0 : runCK TestTm0 = (3, St ResultTm NS)
test0 = Refl

private
test1 : runCK TestTm1 = (6, St ResultTm NS)
test1 = Refl

private
test2 : runCK TestTm2 = (6, St ResultTm NS)
test2 = Refl
