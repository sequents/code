module Lambda.STLC.CEK

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : Term (a::g) b -> Env g -> Clos (a~>b) -- ~(\tm,env)

data Stack : Ty -> Ty -> Type where
  Mt : Stack a a
  Fun : Clos (a~>b) -> Stack b c -> Stack a c
  Arg : Term g a -> Env g -> Stack b c -> Stack (a~>b) c

record State (b : Ty) where
  constructor St 
  tm : Term g a 
  env : Env g 
  stk : Stack a b

step : State a -> Maybe (State a)
step (St (Var  Here     ) (Cl t e::_)                 s ) = Just $ St (Lam t)           e                 s
step (St (Var (There el)) (     _::e)                 s ) = Just $ St (Var el)          e                 s
step (St (Lam t         )          e       (Arg t1 e1 s)) = Just $ St  t1               e1  (Fun (Cl t e) s)
step (St (Lam t         )          e  (Fun (Cl t1 e1) s)) = Just $ St  t1      (Cl t e::e1)               s
step (St (App t u       )          e                  s ) = Just $ St  t                e        (Arg u e s)
step  _                                                   = Nothing   

runCEK : Term [] a -> (Nat, Maybe (State a))
runCEK t = iterCount step $ St t [] Mt
