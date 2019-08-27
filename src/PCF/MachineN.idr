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
  Suc : Stack a c -> Stack a c

data State : Ty -> Type where
  Ev : Term g a -> Env g -> Stack a t -> State t
  Rw : Term g A -> Env g -> Stack A t -> State t

step : State t -> Maybe (State t)
step (Ev (Var  Here)      (Cl t e0::_)             s ) = Just $ Ev  t                      e0                s 
step (Ev (Var (There el))       (_::e)             s ) = Just $ Ev (Var el)                e                 s 
step (Ev (Lam t)                    e       (Arg c s)) = Just $ Ev  t                  (c::e)                s 
step (Ev (App t u)                  e              s ) = Just $ Ev  t                      e   (Arg (Cl u e) s)
step (Ev  Zero                      _  (Tst t _ e1 s)) = Just $ Ev  t                      e1                s 
step (Ev (Succ n)                   e  (Tst _ f e1 s)) = Just $ Ev  f             (Cl n e::e1)               s 
step (Ev  Zero                      e              s ) = Just $ Rw  Zero                   e                 s 
step (Ev (Succ t)                   e              s ) = Just $ Ev  t                      e            (Suc s) 
step (Ev (If0 p t f)                e              s ) = Just $ Ev  p                      e      (Tst t f e s)
step (Ev (Fix t)                    e              s ) = Just $ Ev  t       (Cl (Fix t) e::e)                s 
step (Rw  t                         e         (Suc s)) = Just $ Rw (Succ t)                e                 s 
step  _                                                = Nothing  

runMach : Term [] a -> (Nat, State a)
runMach t = iterCount step $ Ev t [] Mt
