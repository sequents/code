module PCF.MachineV

import Data.List
import Iter
import PCF.Term

%default total
%access public export

-- call by value

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : Term g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt  : Stack a a
  Fun : Term (a::g) b -> Env g -> Stack b c -> Stack a c
  Arg : Clos a -> Stack b c -> Stack (a~>b) c
  Tst : Term g a -> Term (N::g) a -> Env g -> Stack a c -> Stack N c

record State (b : Ty) where
  constructor St 
  tm  : Term g a 
  env : Env g 
  stk : Stack a b 
  res : Nat

step : State b -> Maybe (State b)
step (St (Var  Here)      (Cl t e::_)                  s  r) = Just $ St t                       e                 s    r
step (St (Var (There el))      (_::e)                  s  r) = Just $ St (Var el)                e                 s    r
step (St (Lam t)                   e   (Arg (Cl t1 e1) s) r) = Just $ St t1                      e1       (Fun t e s)   r
step (St (Lam t)                   e        (Fun t1 e1 s) r) = Just $ St t1       (Cl (Lam t) e::e1)               s    r
step (St (App t u)                 e                   s  r) = Just $ St t                       e   (Arg (Cl u e) s)   r
step (St  Zero                     _       (Tst t _ e1 s) r) = Just $ St t                       e1                s    r
step (St  Zero                     e        (Fun t1 e1 s) r) = Just $ St t1          (Cl Zero e::e1)               s    r
step (St (Succ n)                  e       (Tst _ f e1 s) r) = Just $ St f              (Cl n e::e1)               s    r
step (St (Succ n)                  e                   s  r) = Just $ St n                       e                 s (S r)
step (St (If0 p t f)               e                   s  r) = Just $ St p                       e      (Tst t f e s)   r
step (St (Fix t)                   e                   s  r) = Just $ St t        (Cl (Fix t) e::e)                s    r
step  _                                                      = Nothing  

runMach : Term [] a -> (Nat, Maybe (State a))
runMach t = iterCount step $ St t [] Mt Z
