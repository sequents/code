module LJ.LJQ.QJAM

import Data.List
import Data.List.Quantifiers
import Elem
import Subset
import Iter

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LJ.Q.Term

%default total
%access public export

mutual
  Env : List Ty -> Type
  Env = All Clos

  data Clos : Ty -> Type where
    Cl : ValQ g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt : Stack a a
  Fun : TermQ (a::g) b -> Env g -> Stack b c -> Stack a c

data State : Ty -> Type where
  S1 : TermQ g a -> Env g -> Stack a b -> State b
  S2 : ValQ g a -> Env g -> TermQ (a::d) b -> Env d -> Stack b c -> State c

initState : TermQ [] a -> State a
initState a = S1 a [] Mt

step : State b -> Maybe (State b)
step (S1 (V p)         e (Fun t g c)) = Just $ S2 p e t g c
step (S1 (GApp p t el) e          c ) = case indexAll el e of
                                          Cl (Lam u) f => Just $ S2 p e u f (Fun t e c)
                                          _ => Nothing
step (S1 (Let p t)    e           c ) = Just $ S2 p e t e c
step (S2 (Var el) e t g           c ) = let Cl lu f = indexAll el e in
                                        Just $ S2 lu f t g c
step (S2 (Lam u)  e t g           c ) = Just $ S1 t (Cl (Lam u) e :: g) c
step  _                               = Nothing

runQJAM : Term [] a -> (Nat, State a)
runQJAM = iterCount step . initState . encode
