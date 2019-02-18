module Lambda.Untyped.CEK

import Iter
import Lambda.Untyped.TermDB

%default total
%access public export

-- http://matt.might.net/articles/cek-machines/
-- left-to-right

mutual
  Env : Type 
  Env = List Clos

  data Clos = Cl Term Env  -- ~(\tm,env)

-- non-empty evaluation contexts  
data Frame = Fun Clos      -- an evaluated function, E[(cl[ ])] 
           | Arg Term Env  -- an argument to evaluate, E[([ ]e)] where e ~ (tm,env)

Stack : Type
Stack = List Frame

State : Type
State = (Term, Env, Stack)

step : State -> Maybe State
step (Var  Z   , Cl t e::_,                 s) = Just $ (Lam t,         e ,               s)
step (Var (S n),      _::e,                 s) = Just $ (Var n,         e ,               s)
step (Lam t    ,         e,      Arg t1 e1::s) = Just $ (t1   ,         e1, Fun (Cl t e)::s)
step (Lam t    ,         e, Fun (Cl t1 e1)::s) = Just $ (t1   , Cl t e::e1,               s)
step (App t u  ,         e,                 s) = Just $ (t    ,          e,      Arg u e::s)
step  _                                        = Nothing

runCEK : Term -> (Nat, Maybe State)
runCEK t = iterCount step (t, [], [])

private
test0 : runCEK Term0 = (9, Just $ (Lam $ Var 0, [], []))
test0 = Refl

private
test1 : runCEK Term1 = (8, Just $ (Lam $ Var 0, [], []))
test1 = Refl

private
test2 : runCEK Term2 = (8, Just $ (Lam $ Var 0, [], []))
test2 = Refl
