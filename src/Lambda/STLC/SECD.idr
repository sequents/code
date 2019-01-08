module Lambda.STLC.SECD

import Util
import Data.List
import Data.List.Quantifiers
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

-- from https://github.com/Stun17/busido/blob/master/agda/ulaf/Day3.agda

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

-- paths in a graph as a sequence of zero or more edges E i j with source nodes and target nodes matching up domino-style
data Path : (i -> i -> Type) -> i -> i -> Type where
  Nil  : Path e i i
  (::) : e i j -> Path e j k -> Path e i k  

Control : List Ty -> List Ty -> List Ty -> Type
Control g d t = Path (Directive g) d t  

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
step (St (Sn [v]             _ []                 ) (Sn s e c ::d)) = Just $ St (Sn (v      ::s)     e                      c )            d
step (St (Sn              s  e (Tm (Var i    )::c))             d ) = Just $ St (Sn (lup e i::s)     e                      c )            d
step (St (Sn              s  e (Tm (Lam t    )::c))             d ) = Just $ St (Sn (Cl t e ::s)     e                      c )            d
step (St (Sn              s  e (Tm (App t1 t2)::c))             d ) = Just $ St (Sn           s      e   (Tm t2::Tm t1::Ap::c))            d
step (St (Sn (Cl t e1::v::s) e (            Ap::c))             d ) = Just $ St (Sn []           (v::e1) [Tm t]               ) (Sn s e c::d) 
step _ = Nothing

runSECD : Term [] a -> (Nat, Maybe (State a))
runSECD t = iterCount step $ St (Sn [] [] [Tm t]) []
