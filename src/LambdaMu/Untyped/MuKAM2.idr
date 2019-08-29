module LambdaMu.Untyped.MuKAM2

import Iter
import LambdaMu.Untyped.Term

%access public export
%default total

mutual
  Env : Type
  Env = List (Either Stk Clos)

  data Clos = Cl Term Env

  Stk : Type
  Stk = List Clos

State : Type
State = (Term, Env, Stk)

step : State -> Maybe State
step (Var  Z   , Right (Cl t e)::_,        s) = Just (    t,          e,         s)
step (Var (S n),              _::e,        s) = Just (Var n,          e,         s)
step (Lam t    ,                 e,     c::s) = Just (    t, Right c::e,         s)
step (App t u  ,                 e,        s) = Just (    t,          e, Cl u e::s)
step (Mu c     ,                 e,        s) = Just (    c,  Left s::e,        [])
step (Named n t,                 e,       []) = Just (Var n,          e,  [Cl t e]) 
step (Var  Z   ,         Left s::_, [Cl t e]) = Just (    t,          e,         s)
step  _                                       = Nothing

runMK : Term -> (Nat, State)
runMK t = iterCount step (t, [], [])
