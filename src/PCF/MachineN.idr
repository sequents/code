module PCF.MachineN

import Data.List
import Iter
import Lambda.STLC.Ty
import PCF.Term

%default total
%access public export

-- call by name

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : Term g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt  : Stack a a
  Arg : Clos a -> Stack b c -> Stack (a~>b) c
  Tst : Term g a -> Term (A::g) a -> Env g -> Stack a c -> Stack A c

record State (b : Ty) where
  constructor St 
  tm  : Term g a 
  env : Env g 
  stk : Stack a b 

step : State b -> Maybe (State b)
step (St (Var  Here)      (Cl t e0::_)             s ) = Just $ St  t                      e0                s 
step (St (Var (There el))       (_::e)             s ) = Just $ St (Var el)                e                 s 
step (St (Lam t)                    e       (Arg c s)) = Just $ St  t                  (c::e)                s 
step (St (App t u)                  e              s ) = Just $ St  t                      e   (Arg (Cl u e) s)
step (St  Zero                      _  (Tst t _ e1 s)) = Just $ St  t                      e1                s 
step (St (Succ n)                   e  (Tst _ f e1 s)) = Just $ St  f             (Cl n e::e1)               s 
step (St (If0 p t f)                e              s ) = Just $ St  p                      e      (Tst t f e s)
step (St (Fix t)                    e              s ) = Just $ St  t       (Cl (Fix t) e::e)                s 
step  _                                                  = Nothing  

runMach : Term [] a -> (Nat, State a)
runMach t = iterCount step $ St t [] Mt
