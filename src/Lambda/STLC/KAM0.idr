module Lambda.STLC.KAM0

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term
import Lambda.STLC.Smallstep

%default total
%access public export

-- list of arguments encountered along the spine of a term
data Stack : List Ty -> Ty -> Ty -> Type where
  NS : Stack g a a
  CS : Term g a -> Stack g b c -> Stack g (a~>b) c

record State (g : List Ty) (b : Ty) where
  constructor St
  tm : Term g a
  stk : Stack g a b

step : State g b -> Maybe (State g b)
step (St (App t u)       s ) = Just $ St  t           (CS u s)
step (St (Lam t  ) (CS u s)) = Just $ St (subst1 t u)       s
step  _                      = Nothing

runKAM : Term g a -> (Nat, State g a)
runKAM t = iterCount step (St t NS)

private
test0 : runKAM TestTm0 = (2, St ResultTm NS)
test0 = Refl

private
test1 : runKAM TestTm1 = (4, St ResultTm NS)
test1 = Refl

private
test2 : runKAM TestTm2 = (4, St ResultTm NS)
test2 = Refl
