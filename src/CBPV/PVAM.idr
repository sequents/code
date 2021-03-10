module CBPV.PVAM

import Data.List
import Data.List.Quantifiers
import Subset

import LJ.F.Ty
import CBPV.NJPV

%default total
%access public export

mutual
  Env : List PTy -> Type
  Env = All Clos

  data Clos : PTy -> Type where
    Cl : ValC g a -> Env g -> Clos a

data Stack : NTy -> NTy -> Type where
  Mt  : Stack a a
  Arg : Clos a -> Stack b c -> Stack (a~>b) c
  Fun : TermC (a::g) b -> Env g -> Stack b c -> Stack (U a) c

data Mark : PTy -> NTy -> Type where
  MM : TermC (a::g) b -> Env g -> Mark a b
  FM : Mark (D a) a

data State : NTy -> Type where
  TM : TermS g a -> Env g -> Stack a b -> State b
  VM : ValS g a -> Env g -> Mark a b -> Stack b c -> State c

step : State a -> Maybe (State a)
step (TM (CoeT (Bind t u)) e                 s ) = Just $ TM t e      (Fun u e s)
step (TM (App t u)         e                 s ) = Just $ TM t e (Arg (Cl u e) s)
step (TM (Force v)         e                 s ) = Just $ VM  v        e   FM        s
step (TM (CoeT (Pure v))   e      (Fun t1 e1 s)) = Just $ VM (CoeV v)  e  (MM t1 e1) s
step (TM (CoeT (Lam t))    e (Arg (Cl u1 e1) s)) = Just $ VM (CoeV u1) e1 (MM t e)   s
step (VM (Var  Here)      (Cl u e2::_) (MM t1 e1) s) = Just $ VM (CoeV u) e2 (MM t1 e1) s
step (VM (Var (There el))       (_::e) (MM t1 e1) s) = Just $ VM (Var el) e  (MM t1 e1) s
step (VM (CoeV (Thunk t))           e  (MM t1 e1) s) = Just $ TM (CoeT t1) (Cl (Thunk t) e :: e1) s
step (VM (CoeV (Thunk t))           e   FM        s) = Just $ TM (CoeT t)                     e   s
step _ = Nothing
