module LJ.Q.PCF.Mod.TyCheck

import Data.List

import Ctx
import Parse
import LJ.Q.PCF.Mod.Ty
import LJ.Q.PCF.Mod.Term
import LJ.Q.PCF.Mod.Parser

%default total

mutual
  public export
  data Val : Ctx Ty -> Val -> Ty -> Type where
    Lam : Neu ((s,a)::g) v b -> Val g (Lam s v) (a~>b)
    Fix : Neu ((s,C a)::g) v a -> Val g (Fix s v) (C a)
    Emb : NeuV g n a -> a = b -> Val g (Emb n) b

  public export
  data NeuV : Ctx Ty -> NeuV -> Ty -> Type where
    Var  : InCtx g s a -> NeuV g (Var s) a
    Zero : NeuV g Zero A
    Succ : NeuV g v A -> NeuV g (Succ v) A
    Cut  : Val g m a -> NeuV g (Cut m a) a

  public export
  data Neu : Ctx Ty -> Neu -> Ty -> Type where
    V    : NeuV g m a -> Neu g (V m) a
    GApp : {a, b : Ty} ->
           InCtx g s (a~>b) -> Val g m a -> Neu ((x,b)::g) n c -> Neu g (GApp x s m n) c
    GIf0 : {a : Ty} ->
           InCtx g s A -> Neu g t a -> Neu ((y,A)::g) f a -> Neu ((x,a)::g) n b -> Neu g (GIf0 x s t y f n) b
    Bnd  : {a : Ty} ->
           InCtx g s (C a) -> Neu ((x,a)::g) n b -> Neu g (Bnd x s n) b
    Let  : {a : Ty} ->
           NeuV g m a -> Neu ((x,a)::g) n b -> Neu g (Let x m n) b

export
Uninhabited (Val _ (Lam _ _) A) where
  uninhabited (Lam _) impossible

export
Uninhabited (Val _ (Lam _ _) (C _)) where
  uninhabited (Lam _) impossible

export
Uninhabited (Val _ (Fix _ _) A) where
  uninhabited (Lam _) impossible

export
Uninhabited (Val _ (Fix _ _) (Imp _ _)) where
  uninhabited (Lam _) impossible

export
neuVUniq : NeuV g n a -> NeuV g n b -> a = b
neuVUniq (Var i1)  (Var i2)  = inCtxUniq i1 i2
neuVUniq  Zero      Zero     = Refl
neuVUniq (Succ v1) (Succ v2) = Refl
neuVUniq (Cut v1)  (Cut v2)  = Refl

export
neuUniq : Neu g n c -> Neu g n d -> c = d
neuUniq (V nv1)          (V nv2)          = neuVUniq nv1 nv2
neuUniq (GApp el1 _ n1)  (GApp el2 _ n2)  =
  case snd $ impInj $ inCtxUniq el1 el2 of
    Refl => neuUniq n1 n2
neuUniq (GIf0 _ _ f1 n1) (GIf0 _ _ f2 n2) =
  case neuUniq f1 f2 of
    Refl => neuUniq n1 n2
neuUniq (Bnd el1 n1)     (Bnd el2 n2)     =
  case cInj $ inCtxUniq el1 el2 of
    Refl => neuUniq n1 n2
neuUniq (Let nv1 n1)     (Let nv2 n2)     =
  case neuVUniq nv1 nv2 of
    Refl => neuUniq n1 n2

mutual
  synth : (g : Ctx Ty) -> (n : Neu) -> Dec (a ** Neu g n a)
  synth g (V nv)             = case synthV g nv of
    Yes (a**t) => Yes (a**V t)
    No ctra    => No $ \(a**V t) => ctra (a**t)
  synth g (GApp x s v n)     = case lookup g s of
    Yes (A**el)       => No $ \(_**GApp el1 _ _) => uninhabited $ inCtxUniq el el1
    Yes (Imp a b**el) => case inherit g v a of
      Yes t   => case synth ((x,b)::g) n of
        Yes (c**u) => Yes (c ** GApp el t u)
        No ctra    => No $ \(c**GApp el0 _ u) =>
                        case snd $ impInj $ inCtxUniq el el0 of
                          Refl => ctra (c ** u)
      No ctra => No $ \(_**GApp el0 t0 _) =>
                  case fst $ impInj $ inCtxUniq el el0 of
                    Refl => ctra t0
    Yes (C _**el)     => No $ \(_**GApp el0 _ _) => uninhabited $ inCtxUniq el0 el
    No ctra           => No $ \(_**GApp {a} {b} el _ _) => ctra (a~>b ** el)
  synth g (GIf0 x s t y f n) = case lookup g s of
    Yes (A**el)       => case synth g t of
      Yes (a**u) => case synth ((y,A)::g) f of
        Yes (a1**v) => case decEq a a1 of
          Yes Refl => case synth ((x,a)::g) n of
            Yes (b**w) => Yes (b**GIf0 el u v w)
            No ctra    => No $ \(b**GIf0 _ u1 _ w) => case neuUniq u u1 of
                            Refl => ctra (b**w)
          No ctra  => No $ \(_**GIf0 _ u1 v1 _) => case neuUniq u u1 of
                        Refl => ctra $ neuUniq v1 v
        No ctra    => No $ \(_**GIf0 {a} _ u1 v _) => case neuUniq u u1 of
                        Refl => ctra (a**v)
      No ctra    => No $ \(_**GIf0 {a} _ u1 _ _) => ctra (a**u1)
    Yes (Imp _ _**el) => No $ \(_**GIf0 el0 _ _ _) => uninhabited $ inCtxUniq el0 el
    Yes (C _**el)     => No $ \(_**GIf0 el0 _ _ _) => uninhabited $ inCtxUniq el0 el
    No ctra           => No $ \(_**GIf0 el _ _ _) => ctra (A ** el)
  synth g (Bnd x s n)        = case lookup g s of
    Yes (A**el)       => No $ \(_**Bnd el1 _) => uninhabited $ inCtxUniq el el1
    Yes (Imp _ _**el) => No $ \(_**Bnd el1 _) => uninhabited $ inCtxUniq el el1
    Yes (C a**el)     => case synth ((x,a)::g) n of
      Yes (b**t) => Yes (b ** Bnd el t)
      No ctra    => No $ \(c**Bnd el1 t1) =>
                      case cInj $ inCtxUniq el el1 of
                        Refl => ctra (c**t1)
    No ctra           => No $ \(_**Bnd {a} el _) => ctra (C a ** el)
  synth g (Let x nv n)       = case synthV g nv of
    Yes (a**t) => case synth ((x,a)::g) n of
      Yes (b**u) => Yes (b**Let t u)
      No ctra    => No $ \(b**Let t0 u) =>
                      case neuVUniq t t0 of
                        Refl => ctra (b ** u)
    No ctra    => No $ \(_**Let {a} t0 _) => ctra (a ** t0)

  synthV : (g : Ctx Ty) -> (n : NeuV) -> Dec (a ** NeuV g n a)
  synthV g (Var s)   = case lookup g s of
    Yes (a**el) => Yes (a**Var el)
    No ctra => No $ \(a**Var el) => ctra (a**el)
  synthV g  Zero     = Yes (A**Zero)
  synthV g (Succ v)  = case synthV g v of
    Yes (A**w)       => Yes (A**Succ w)
    Yes (Imp _ _**w) => No $ \(A**Succ u) => uninhabited $ neuVUniq u w
    Yes (C _**w)     => No $ \(A**Succ u) => uninhabited $ neuVUniq u w
    No ctra          => No $ \(A**Succ w) => ctra (A ** w)
  synthV g (Cut v t) = case inherit g v t of
    Yes u   => Yes (t**Cut u)
    No ctra => No $ \(t**Cut u) => ctra u

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inherit _ (Lam _ _)  A        = No uninhabited
  inherit g (Lam s n) (Imp a b) = case synth ((s,a)::g) n of
    Yes (c**t) => case decEq b c of
      Yes Refl => Yes $ Lam t
      No ctra  => No $ \(Lam t0) => ctra $ neuUniq t0 t
    No ctra    => No $ \(Lam t0) => ctra (b**t0)
  inherit _ (Lam _ _) (C _)     = No uninhabited
  inherit _ (Fix _ _)  A        = No uninhabited
  inherit g (Fix _ _) (Imp _ _) = No uninhabited
  inherit _ (Fix s n) (C a)     = case synth ((s,C a)::g) n of
    Yes (b**m) => case decEq a b of
      Yes Refl => Yes $ Fix m
      No ctra  => No $ \(Fix m0) => ctra $ neuUniq m0 m
    No ctra    => No $ \(Fix m0) => ctra (a ** m0)
  inherit g (Emb nv)   a        = case synthV g nv of
    Yes (b**m) => case decEq a b of
      Yes prf => Yes $ Emb m (sym prf)
      No ctra => No $ \(Emb m0 prf) => ctra $ trans (sym prf) (neuVUniq m0 m)
    No ctra    => No $ \(Emb m0 Refl) => ctra (a ** m0)

mutual
  val2Term : Val g m a -> ValQ (eraseCtx g) a
  val2Term (Lam n)       = Lam $ neu2Term n
  val2Term (Fix n)       = Fix $ neu2Term n
  val2Term (Emb nv Refl) = neuv2Term nv

  neuv2Term : NeuV g m a -> ValQ (eraseCtx g) a
  neuv2Term (Var el)  = Var $ eraseInCtx el
  neuv2Term  Zero     = Zero
  neuv2Term (Succ nv) = Succ $ neuv2Term nv
  neuv2Term (Cut v)   = val2Term v

  neu2Term : Neu g m a -> TermQ (eraseCtx g) a
  neu2Term (V nv)          = V $ neuv2Term nv
  neu2Term (GApp el v n)   = GApp (eraseInCtx el) (val2Term v) (neu2Term n)
  neu2Term (GIf0 el t f n) = GIf0 (eraseInCtx el) (neu2Term t) (neu2Term f) (neu2Term n)
  neu2Term (Bnd el n)      = Bnd (eraseInCtx el) (neu2Term n)
  neu2Term (Let nv n)      = Let (neuv2Term nv) (neu2Term n)
