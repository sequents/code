module PCF.InstructV

import Data.List
import Iter
import Path
import Elem
import Lambda.STLC.Ty
import PCF.Term
import PCF.Bytecode

import Data.Fuel

%default total
%access public export

-- call-by-value virtual machine

mutual
  data Env : List Ty -> Type where
    NE : Env []
    CE : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : Control g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt  : Stack a a
  Fun : Control (a::g) b -> Env g -> Stack b c -> Stack a c
  Arg : Clos a -> Stack b c -> Stack (a~>b) c
  Tst : Control g a -> Control (A::g) a -> Env g -> Stack a c -> Stack A c

record State (b : Ty) where
  constructor St 
  ctr : Control g a 
  env : Env g 
  stk : Stack a b 
  res : Nat

Show (State b) where
  show (St ctr _ _ res) = "Control: " ++ show ctr ++ ", Accumulator: " ++ show res

indexE : Elem a g -> Env g -> Clos a
indexE Here       (CE e _)  = e
indexE (There el) (CE _ es) = indexE el es

step : State b -> Maybe (State b)  
step (St     (MkCtr _ _ (Access n::_)) e                 s  r) = let Cl c0 e0 = indexE n e in 
                                                                 Just $ St            c0                                  e0                      s    r
step (St     (MkCtr d b     (Grab::i)) e (Arg (Cl c1 e1) s) r) = Just $ St            c1                                  e1 (Fun (MkCtr d b i) e s)   r
step (St     (MkCtr d b     (Grab::i)) e      (Fun c1 e1 s) r) = Just $ St            c1 (CE (Cl (MkCtr d b (Grab::i)) e) e1)                     s    r
step (St     (MkCtr d b  (Push c0::i)) e                 s  r) = Just $ St (MkCtr d b i)                                  e        (Arg (Cl c0 e) s)   r
step (St     (MkCtr _ _      (Nul::_)) _     (Tst t _ e1 s) r) = Just $ St            t                                   e1                      s    r
step (St {g} (MkCtr _ _      (Nul::_)) e      (Fun c1 e1 s) r) = Just $ St            c1     (CE (Cl (MkCtr g A [Nul]) e) e1)                     s    r
step (St     (MkCtr d b      (Inc::i)) e     (Tst _ f e1 s) r) = Just $ St            f          (CE (Cl (MkCtr d b i) e) e1)                     s    r
step (St     (MkCtr d b      (Inc::i)) e                 s  r) = Just $ St (MkCtr d b i)                                  e                       s (S r)
step (St     (MkCtr d b (Case t f::i)) e                 s  r) = Just $ St (MkCtr d b i)                                  e            (Tst t f e s)   r
step (St     (MkCtr d b     (Loop::i)) e                 s  r) = Just $ St (MkCtr d b i) (CE (Cl (MkCtr d b (Loop::i)) e) e)                      s    r
step  _                                                        = Nothing  

init : Control [] a -> State a
init c = St c NE Mt Z
