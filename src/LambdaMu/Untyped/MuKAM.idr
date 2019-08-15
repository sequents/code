module LambdaMu.Untyped.MuKAM

import Iter
import LambdaMu.Term

%access public export
%default total

mutual
  Env : Type
  Env = (List Clos, List Stk)

  data Clos = Cl Term Env

  Stk : Type
  Stk = List Clos

State : Type
State = (Term, Env, Stk)

step : State -> Maybe State
step (Var  Z   , (Cl t e::_, _),    s) =   Just (    t,              e,         s)
step (Var (S n),     (_::ce,se),    s) =   Just (Var n,    (ce,    se),         s)
step (Lam t    ,        (ce,se), c::s) =   Just (    t, (c::ce,    se),         s)
step (App t u  ,              e,    s) =   Just (    t,              e, Cl u e::s)
step (Mu c     ,        (ce,se),    s) =   Just (    c,     (ce,s::se),        [])
step (Named n t,        (ce,se),   []) = (\s => (    t,     (ce,   se),         s)) <$> index' n se 
step  _                           = Nothing

runMK : Term -> (Nat, State)
runMK t = iterCount step (t, ([], []), [])
