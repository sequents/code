module Lambda.Untyped.KAM

import Lambda.Untyped.TermDB

%default total
%access public export

-- untyped KAM 

mutual
  Env : Type 
  Env = List Clos

  data Clos = Cl Term Env

Stack : Type
Stack = List Clos

State : Type
State = (Term, Env0, Stack)

step : State -> Maybe State
step (Var  Z   , Cl t e::_,    s) = Just (    t,    e,         s)
step (Var (S n),      _::e,    s) = Just (Var n,    e,         s)
step (Lam t    ,         e, c::s) = Just (    t, c::e,         s)
step (App t u  ,         e,    s) = Just (    t,    e, Cl u e::s)
step  _                           = Nothing

stepIter : State -> Maybe State
stepIter s with (step s)
  | Nothing = Just s
  | Just s1 = assert_total $ stepIter s1

run : Term -> Maybe State
run t = stepIter (t, [], [])

test0 : run Term0 = Just (Lam $ Var Z, [], [])
test0 = Refl

test1 : run Term1 = Just (Lam $ Var Z, [], [])
test1 = Refl

test2 : run Term2 = Just (Lam $ Var Z, [], [])
test2 = Refl
