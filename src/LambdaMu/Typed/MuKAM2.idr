module LambdaMu.Typed.MuKAM2

import Data.List
import Iter
import LambdaMu.Typed.Term

%access public export
%default total

mutual
  data Env : List Ty -> Ty -> List Ty -> Type where
    NE : Env [] c []
    CE : Clos a c -> Env g c d -> Env (a::g) c d
    SE : Stack a c -> Env g c d -> Env g c (a::d)
  
  data Clos : Ty -> Ty -> Type where
    Cl : Term g a d -> Env g c d -> Clos a c

  data Stack : Ty -> Ty -> Type where
    NS : Stack a a 
    ES : Stack Bot a
    CS : Clos a c -> Stack b c -> Stack (a~>b) c

data State : Ty -> Type where
  St1 : Term g a d -> Env g c d -> Stack a c -> State c
  St2 : Elem x d -> Env g c d -> Stack (x~>Bot) c -> State c

step : State t -> Maybe (State t)
step (St1 (Var  Here)     (CE (Cl t e) _)               s ) = Just $ St1  t            e                  s
step (St1 (Var (There n))        (CE _ e)               s ) = Just $ St1 (Var n)       e                  s
step (St1 (Lam t)                      e          (CS c s)) = Just $ St1  t      (CE c e)                 s
step (St1 (App t u)                    e                s ) = Just $ St1  t            e  ((Cl u e) `CS`  s)
step (St1 (Mu t)                       e                s ) = Just $ St1  t      (SE s e)                ES
step (St1 (Named n t)                  e               ES ) = Just $ St2  n            e  ((Cl t e) `CS` ES)
step (St2 (There n)              (SE _ e)               s ) = Just $ St2  n            e                  s
step (St2  Here                  (SE s _) (CS (Cl t e) ES)) = Just $ St1  t            e                  s
step  _                                                     = Nothing

runMK : Term [] a [] -> (Nat, State a)
runMK t = iterCount step (St1 t NE NS)
