module LambdaMu.Typed.MuKAM2

import Data.List
import Iter
import LambdaMu.Typed.Term

%access public export
%default total

mutual
  data Env : List Ty -> List Ty -> Type where
    NE : Env [] []
    CE : Clos a -> Env g d -> Env (a::g) d
    SE : Stack a -> Env g d -> Env g (a::d)
  
  data Clos : Ty -> Type where
    Cl : Term g a d -> Env g d -> Clos a

  data Stack : Ty -> Type where
     NS : Stack a
     CS : Clos a -> Stack b -> Stack (a~>b)

data State : Type where
  St1 : Term g a d -> Env g d -> Stack a -> State
  St2 : Elem x d -> Env g d -> Stack (x~>Bot) -> State

step : State -> Maybe State
step (St1 (Var  Here)     (CE (Cl t e) _)               s ) = Just $ St1  t            e                  s
step (St1 (Var (There n))        (CE _ e)               s ) = Just $ St1 (Var n)       e                  s
step (St1 (Lam t)                      e          (CS c s)) = Just $ St1  t      (CE c e)                 s
step (St1 (App t u)                    e                s ) = Just $ St1  t            e  ((Cl u e) `CS`  s)
step (St1 (Mu t)                       e                s ) = Just $ St1  t      (SE s e)                NS
step (St1 (Named n t)                  e                NS) = Just $ St2  n            e  ((Cl t e) `CS` NS)
step (St2 (There n)              (SE _ e)               s ) = Just $ St2  n            e                  s
step (St2  Here                  (SE s _) (CS (Cl t e) NS)) = Just $ St1  t            e                  s
step  _                                                     = Nothing

runMK : Term [] a [] -> (Nat, State)
runMK t = iterCount step (St1 t NE NS)
