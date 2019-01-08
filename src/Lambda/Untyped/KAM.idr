module Lambda.Untyped.KAM

import Util
import Lambda.Untyped.TermDB

%default total
%access public export

mutual
  Env : Type 
  Env = List Clos

  data Clos = Cl Term Env

Stack : Type
Stack = List Clos

State : Type
State = (Term, Env, Stack)

step : State -> Maybe State
step (Var  Z   , Cl t e::_,    s) = Just (    t,    e,         s)
step (Var (S n),      _::e,    s) = Just (Var n,    e,         s)
step (Lam t    ,         e, c::s) = Just (    t, c::e,         s)
step (App t u  ,         e,    s) = Just (    t,    e, Cl u e::s)
step  _                           = Nothing

runKAM : Term -> Maybe State
runKAM t = iter step (t, [], [])

test0 : runKAM Term0 = Just (Lam $ Var Z, [], [])
test0 = Refl

test1 : runKAM Term1 = Just (Lam $ Var Z, [], [])
test1 = Refl

test2 : runKAM Term2 = Just (Lam $ Var Z, [], [])
test2 = Refl
