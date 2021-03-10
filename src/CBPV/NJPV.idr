module CBPV.NJPV

import Data.List
import Subset

import LJ.F.Ty

%default total
%access public export

mutual
  -- synthesized
  data TermS : List PTy -> NTy -> Type where
    App   : TermS g (p~>n) -> ValC g p -> TermS g n       -- impl elim
    Force : ValS g (D n) -> TermS g n                     -- D elim
    CoeT  : TermC g n -> TermS g n                        -- coerce checked term

  data ValS : List PTy -> PTy -> Type where
    Var  : Elem p g -> ValS g p                           -- axiom
    CoeV : ValC g p -> ValS g p                           -- coerce checked val

  -- checked
  data TermC : List PTy -> NTy -> Type where
    Pure  : ValC g p -> TermC g (U p)                     -- U intro
    Lam   : TermC (p::g) n -> TermC g (p~>n)              -- impl intro
    Bind  : TermS g (U p) -> TermC (p::g) m -> TermC g m  -- U elim
    MeetT : TermS g n -> UN n -> TermC g n

  data ValC : List PTy -> PTy -> Type where
    Thunk : TermC g n -> ValC g (D n)                     -- D intro
    MeetV : ValS g p -> ValC g p

lt : ValC g p -> TermC (p::g) n -> TermC g n
lt v t = Bind (CoeT $ Pure v) t

mutual
  renameTS : Subset g d -> TermS g a -> TermS d a
  renameTS s (App t u) = App (renameTS s t) (renameVC s u)
  renameTS s (Force v) = Force $ renameVS s v
  renameTS s (CoeT t)  = CoeT $ renameTC s t

  renameVS : Subset g d -> ValS g a -> ValS d a
  renameVS s (Var el) = Var $ s el
  renameVS s (CoeV v) = CoeV $ renameVC s v

  renameTC : Subset g d -> TermC g a -> TermC d a
  renameTC s (Pure v)    = Pure $ renameVC s v
  renameTC s (Lam t)     = Lam $ renameTC (ext s) t
  renameTC s (Bind t u)  = Bind (renameTS s t) (renameTC (ext s) u)
  renameTC s (MeetT t p) = MeetT (renameTS s t) p

  renameVC : Subset g d -> ValC g a -> ValC d a
  renameVC s (Thunk t) = Thunk $ renameTC s t
  renameVC s (MeetV v) = MeetV $ renameVS s v
