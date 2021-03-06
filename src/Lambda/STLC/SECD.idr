module Lambda.STLC.SECD

import Data.List
import Data.List.Quantifiers
import Path
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

-- from https://github.com/UlfNorell/agda-summer-school/blob/EJCP-solutions/exercises/SECD/Compiled.agda

mutual
  Env : List Ty -> Type
  Env = All Clos
  
  data Clos : Ty -> Type where
    Cl : Term (a::g) b -> Env g -> Clos (a~>b)

Stack : List Ty -> Type
Stack = All Clos

data Directive : List Ty -> List Ty -> List Ty -> Type where
  Tm : Term g a -> Directive g d (a::d)
  Ap : Directive g ((a~>b)::a::d) (b::d)

Control : List Ty -> List Ty -> List Ty -> Type
Control g = Path (Directive g)

record Snapshot (t : List Ty) (a : Ty) where
  constructor Sn
  stack : Stack d
  env : Env g
  control : Control g (t++d) [a]

Dump : Ty -> Ty -> Type
Dump = Path (\a, b => Snapshot [a] b)  

record State (a : Ty) where
  constructor St
  current : Snapshot [] b
  dump : Dump b a

lup : {g : List a} -> All f g -> Elem x g -> f x
lup (fx::_)  Here      = fx
lup (_::fg) (There el) = lup fg el

step : State a -> Maybe (State a) 
step (St (Sn            [v]  _                  []) (Sn s e c::d)) = Just $ St (Sn       (v::s)     e                      c )            d
step (St (Sn              s  e     (Tm (Var i)::c))            d ) = Just $ St (Sn (lup e i::s)     e                      c )            d
step (St (Sn              s  e     (Tm (Lam t)::c))            d ) = Just $ St (Sn  (Cl t e::s)     e                      c )            d
step (St (Sn              s  e (Tm (App t1 t2)::c))            d ) = Just $ St (Sn           s      e   (Tm t2::Tm t1::Ap::c))            d
step (St (Sn (Cl t e1::v::s) e             (Ap::c))            d ) = Just $ St (Sn          []  (v::e1)                [Tm t]) (Sn s e c::d) 
step _                                                             = Nothing

runSECD : Term [] a -> (Nat, State a)
runSECD t = iterCount step $ St (Sn [] [] [Tm t]) []
