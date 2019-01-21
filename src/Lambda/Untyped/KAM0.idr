module Lambda.Untyped.KAM0

import Iter
import Lambda.Untyped.TermDB
import Lambda.Untyped.SmallstepDB

Stack : Type
Stack = List Term

State : Type
State = (Term, Stack)

step : State -> Maybe State
step (App t u,    s) = Just (t, u::s)
step (Lam t,   u::s) = Just (topSubst u t, s)
step  _              = Nothing

count0N : Term -> (Nat, Maybe Term)
count0N = iterCount step
