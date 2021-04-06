module CBPV.NJPV

import Data.List
import Subset

import LJ.F.Ty

%default total

mutual
  -- synthesized
  public export
  data TermS : List PTy -> NTy -> Type where
    App  : TermS g (p~>n) -> ValC g p -> TermS g n       -- impl elim
    Fce  : ValS g (D n) -> TermS g n                     -- D elim, force
    CoeT : TermC g n -> TermS g n                        -- coerce checked term

  public export
  data ValS : List PTy -> PTy -> Type where
    Var  : Elem p g -> ValS g p                           -- axiom
    CoeV : ValC g p -> ValS g p                           -- coerce checked val

  -- checked
  public export
  data TermC : List PTy -> NTy -> Type where
    Pure  : ValC g p -> TermC g (U p)                     -- U intro
    Lam   : TermC (p::g) n -> TermC g (p~>n)              -- impl intro
    Bind  : TermS g (U p) -> TermC (p::g) m -> TermC g m  -- U elim
    MeetT : TermS g n -> UN n -> TermC g n

  public export
  data ValC : List PTy -> PTy -> Type where
    Thunk : TermC g n -> ValC g (D n)                     -- D intro
    MeetV : ValS g p -> ValC g p

lt : ValC g p -> TermC (p::g) n -> TermC g n
lt v t = Bind (CoeT $ Pure v) t

mutual
  export
  renameTS : Subset g d -> TermS g a -> TermS d a
  renameTS s (App t u) = App (renameTS s t) (renameVC s u)
  renameTS s (Fce v)   = Fce $ renameVS s v
  renameTS s (CoeT t)  = CoeT $ renameTC s t

  export
  renameVS : Subset g d -> ValS g a -> ValS d a
  renameVS s (Var el) = Var $ s el
  renameVS s (CoeV v) = CoeV $ renameVC s v

  export
  renameTC : Subset g d -> TermC g a -> TermC d a
  renameTC s (Pure v)    = Pure $ renameVC s v
  renameTC s (Lam t)     = Lam $ renameTC (ext s) t
  renameTC s (Bind t u)  = Bind (renameTS s t) (renameTC (ext s) u)
  renameTC s (MeetT t p) = MeetT (renameTS s t) p

  export
  renameVC : Subset g d -> ValC g a -> ValC d a
  renameVC s (Thunk t) = Thunk $ renameTC s t
  renameVC s (MeetV v) = MeetV $ renameVS s v

mutual
  export
  subst1TS : ValC g p -> TermS (p::g) b -> TermS g b
  subst1TS v (App t u) = App (subst1TS v t) (subst1VC v u)
  subst1TS v (Fce u)   = Fce $ subst1VS v u
  subst1TS v (CoeT t)  = CoeT $ subst1TC v t

  export
  subst1VS : ValC g p -> ValS (p::g) b -> ValS g b
  subst1VS v (Var  Here)      = CoeV v
  subst1VS _ (Var (There el)) = Var el
  subst1VS v (CoeV u)         = CoeV $ subst1VC v u

  export
  subst1VC : ValC g p -> ValC (p::g) b -> ValC g b
  subst1VC v (Thunk t) = Thunk $ subst1TC v t
  subst1VC v (MeetV u) = MeetV $ subst1VS v u

  export
  subst1TC : ValC g p -> TermC (p::g) b -> TermC g b
  subst1TC v (Pure u)    = Pure $ subst1VC v u
  subst1TC v (Lam t)     = Lam $ assert_total $ subst1TC (renameVC weaken v) (renameTC permute0 t)
  subst1TC v (Bind t u)  = Bind (subst1TS v t) (assert_total $ subst1TC (renameVC weaken v) (renameTC permute0 u))
  subst1TC v (MeetT t p) = MeetT (subst1TS v t) p
