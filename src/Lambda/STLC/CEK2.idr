module Lambda.STLC.CEK2

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

-- right-to-left

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : Term g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt : Stack a a
  Fun : Clos (a~>b) -> Stack b c -> Stack a c
  Arg : Term g a -> Env g -> Stack b c -> Stack (a~>b) c

data State : Ty -> Type where
  L : Term g a -> Env g -> Stack a b -> State b
  R : Clos a -> Stack a b -> State b

step : State a -> Maybe (State a)
step (L (Var  Here)      (v::_)                 s ) = Just $ R  v                                       s 
step (L (Var (There el)) (_::e)                 s ) = Just $ L (Var el)               e                 s 
step (L (Lam t)              e                  s ) = Just $ R (Cl (Lam t)            e)                s
step (R (Cl (Lam t)          e) (Fun (Cl t1 e1) s)) = Just $ L  t1                    e1 (Arg (Lam t) e s)
step (R (Cl (Lam t)          e)      (Arg t1 e1 s)) = Just $ L  t          (Cl t1 e1::e)                s
step (L (App t u)            e                  s ) = Just $ L  u                     e   (Fun (Cl t e) s)
step  _                                             = Nothing   

runCEK : Term [] a -> (Nat, Maybe (State a))
runCEK t = iterCount step $ L t [] Mt

private
test1 : runCEK TestTm1 = (11, Just $ R (Cl ResultTm []) Mt)
test1 = Refl

private
test2 : runCEK TestTm2 = (11, Just $ R (Cl ResultTm []) Mt)
test2 = Refl
