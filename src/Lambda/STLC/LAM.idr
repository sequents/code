module Lambda.STLC.CEK2

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

-- Leroy Abstract Machine, right-to-left call-by-value

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)

  data Clos : Ty -> Type where
    Cl : Term g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt : Stack a a
  Arg : Clos a -> Stack b c -> Stack (a~>b) c
  Fun : Clos (a~>b) -> Stack b c -> Stack a c

record State (b : Ty) where
  constructor St
  tm  : Term g a
  env : Env g
  stk : Stack a b

step : State a -> Maybe (State a)
step (St (Var  Here)      (Cl t e::_)                 s ) = Just $ St  t            e                s
step (St (Var (There el))      (_::e)                 s ) = Just $ St (Var el)      e                s
step (St (App t u)                 e                  s ) = Just $ St  u            e  (Fun (Cl t e) s)
step (St  t                        e  (Fun (Cl t1 e1) s)) = Just $ St  t1           e1 (Arg (Cl t e) s)
step (St (Lam t)                   e          (Arg cl s)) = Just $ St  t       (cl::e)               s
step  _                                                   = Nothing

runLAM : Term [] a -> (Nat, State a)
runLAM t = iterCount step $ St t [] Mt

private
test1 : runLAM TestTm1 = (8, St ResultTm [] Mt)
test1 = Refl

private
test2 : runLAM TestTm2 = (8, St ResultTm [] Mt)
test2 = Refl
