module Lambda.Untyped.CK

import Iter
import Lambda.Untyped.TermDB
import Lambda.Untyped.SmallstepDB

%default total
%access public export

-- left-to-right, no environment

-- non-empty evaluation contexts  
data Frame = Fun Term -- an evaluated function
           | Arg Term -- an argument to evaluate

Stack : Type
Stack = List Frame

State : Type
State = (Term, Stack)

step : State -> Maybe State
step (Lam t  , Arg t1::s) = Just $ (t1                 , Fun t::s)
step (Lam t  , Fun t1::s) = Just $ (topSubst (Lam t) t1,        s)
step (App t u,         s) = Just $ (t                  , Arg u::s)
step  _                   = Nothing

runCK : Term -> (Nat, Maybe State)
runCK t = iterCount step (t, [])

test0 : runCK Term0 = (6, Just $ (Lam $ Var 0, []))
test0 = Refl

test1 : runCK Term1 = (6, Just $ (Lam $ Var 0, []))
test1 = Refl

test2 : runCK Term2 = (6, Just $ (Lam $ Var 0, []))
test2 = Refl
