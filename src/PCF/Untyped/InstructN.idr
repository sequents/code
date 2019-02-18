module PCF.Unyped.InstructN

import Data.List
import Iter
import Elem
import Lambda.STLC.Ty
import PCF.Term

%default total
%access public export

-- untyped bytecode

data I : Type where
  Access : Nat -> I 
  Grab   : I 
  Push   : List I -> I
  Nul    : I 
  Inc    : I 
  Case   : List I -> List I -> I 
  Loop   : I

compile : Term g a -> List I
compile (Var e)     = [Access $ elem2Nat e]
compile (Lam t)     = Grab :: compile t
compile (App t u)   = Push (compile u) :: compile t
compile  Zero       = [Nul]
compile (Succ t)    = Inc :: compile t
compile (If0 c t f) = Case (compile t) (compile f) :: compile c
compile (Fix t)     = Loop :: compile t

-- virtual machine

mutual
  Env : Type 
  Env = List Clos
  
  data Clos : Type where
    Cl : List I -> Env -> Clos

data Stack : Type where
  Mt  : Stack
  Arg : Clos -> Stack -> Stack
  Tst : List I -> List I -> Env -> Stack -> Stack

record State where
  constructor St 
  ctr : List I
  env : Env 
  stk : Stack 
  res : Nat

step : State -> Maybe State
step (St (Access n::_) e             s  r) = (\(Cl c0 e0) => St c0                 e0                s    r) <$> index' n e
step (St (    Grab::c) e     (Arg cl s) r) = Just $          St c             (cl::e)                s    r
step (St ( Push c0::c) e             s  r) = Just $          St c                  e  (Arg (Cl c0 e) s)   r
step (St (     Nul::_) _ (Tst t _ e1 s) r) = Just $          St t                  e1                s    r
step (St (     Inc::c) e (Tst _ f e1 s) r) = Just $          St f         (Cl c e::e1)               s    r
step (St (     Inc::c) e             s  r) = Just $          St c                  e                 s (S r)
step (St (Case t f::c) e             s  r) = Just $          St c                  e      (Tst t f e s)   r
step (St (    Loop::c) e             s  r) = Just $          St c (Cl (Loop::c) e::e)                s    r
step  _                                    = Nothing  

init : Term g a -> State
init t = St (compile t) [] Mt Z