module Lambda.Untyped.CEK2

import Util
import Lambda.Untyped.TermDB

%default total
%access public export

-- http://matt.might.net/articles/cek-machines/
-- left-to-right

mutual
  Env : Type 
  Env = List Clos

  data Clos = Cl Term Env

-- non-empty evaluation contexts  
data Frame = Fun Term Env  -- E[(v[ ])] where v ~ (t,env)
           | Arg Term Env  -- E[([ ]e)] where e ~ (t,env)

Stack : Type
Stack = List Frame

State : Type
State = (Term, Env, Stack)

step : State -> Maybe State
step (Var  Z   , Cl t e::_,            s) = Just $ (Lam t,         e ,          s)
step (Var (S n),      _::e,            s) = Just $ (Var n,         e ,          s)
step (Lam t    ,         e, Arg t1 e1::s) = Just $ (t1   ,         e1, Fun t e::s)
step (Lam t    ,         e, Fun t1 e1::s) = Just $ (t1   , Cl t e::e1,          s)
step (App t u  ,         e,            s) = Just $ (t    ,          e, Arg u e::s)
step  _                                         = Nothing

runCEK : Term -> (Nat, Maybe State)
runCEK t = iterCount step (t, [], [])

test0 : runCEK Term0 = (9, Just $ (Lam $ Var 0, [], []))
test0 = Refl

test1 : runCEK Term1 = (8, Just $ (Lam $ Var 0, [], []))
test1 = Refl

test2 : runCEK Term2 = (8, Just $ (Lam $ Var 0, [], []))
test2 = Refl
