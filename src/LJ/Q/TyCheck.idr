module LJ.Q.TyCheck

import Data.List

import Ctx
import Lambda.STLC.Ty
import LJQ.Parser

%default total

mutual
  public export
  data Val : Ctx Ty -> Val -> Ty -> Type where
    Lam : Neu ((s,a)::g) v b -> Val g (Lam s v) (a~>b)
    Emb : NeuV g n a -> a = b -> Val g (Emb n) b

  public export
  data NeuV : Ctx Ty -> NeuV -> Ty -> Type where
    Var : InCtx g s a -> NeuV g (Var s) a
    Cut : Val g m a -> NeuV g (Cut m a) a

  public export
  data Neu : Ctx Ty -> Neu -> Ty -> Type where
    V    : NeuV g m a -> Neu g (V m) a
    GApp : {a, b : Ty} ->
           InCtx g s (a~>b) -> Val g m a -> Neu ((x,b)::g) n c -> Neu g (GApp x s m n) c
    Let  : {a : Ty} ->
           NeuV g m a -> Neu ((x,a)::g) n b -> Neu g (Let x m n) b

export
Uninhabited (Val _ (Lam _ _) A) where
  uninhabited (Lam _) impossible

export
neuVUniq : NeuV g n a -> NeuV g n b -> a = b
neuVUniq (Var i1) (Var i2) = inCtxUniq i1 i2
neuVUniq (Cut v1) (Cut v2) = Refl

export
neuUniq : Neu g n c -> Neu g n d -> c = d
neuUniq (V nv1)         (V nv2)         = neuVUniq nv1 nv2
neuUniq (GApp el1 _ n1) (GApp el2 _ n2) =
  case snd $ impInj $ inCtxUniq el1 el2 of
    Refl => neuUniq n1 n2
neuUniq (Let nv1 n1)    (Let nv2 n2)    =
  case neuVUniq nv1 nv2 of
    Refl => neuUniq n1 n2

mutual
  synth : (g : Ctx Ty) -> (n : Neu) -> Dec (a ** Neu g n a)
  synth g (V nv)          = case synthV g nv of
    Yes (a**t) => Yes (a**V t)
    No ctra    => No \(a**V t) => ctra (a**t)
  synth g (GApp x s v n) = case lookup g s of
    Yes (A**el)       => No \(a**GApp el1 t u) => uninhabited $ inCtxUniq el el1
    Yes (Imp a b**el) => case inherit g v a of
      Yes t   => case synth ((x,b)::g) n of
        Yes (c**u) => Yes (c ** GApp el t u)
        No ctra    => No \(c**GApp el0 _ u) =>
                        case snd $ impInj $ inCtxUniq el el0 of
                          Refl => ctra (c ** u)
      No ctra => No \(_**GApp el0 t0 _) =>
                  case fst $ impInj $ inCtxUniq el el0 of
                    Refl => ctra t0
    No ctra           => No \(_ ** GApp {a} {b} el _ _) => ctra (a~>b ** el)
  synth g (Let x nv n)   = case synthV g nv of
    Yes (a**t) => case synth ((x,a)::g) n of
      Yes (b**u) => Yes (b**Let t u)
      No ctra    => No \(b**Let t0 u) =>
                      case neuVUniq t t0 of
                        Refl => ctra (b ** u)
    No ctra    => No \(_**Let {a} t0 _) => ctra (a ** t0)

  synthV : (g : Ctx Ty) -> (n : NeuV) -> Dec (a ** NeuV g n a)
  synthV g (Var s)   = case lookup g s of
    Yes (a**el) => Yes (a**Var el)
    No ctra => No \(a**Var el) => ctra (a**el)
  synthV g (Cut v t) = case inherit g v t of
    Yes u   => Yes (t**Cut u)
    No ctra => No \(t**Cut u) => ctra u

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inherit _ (Lam _ _)  A        = No uninhabited
  inherit g (Lam s n) (Imp a b) = case synth ((s,a)::g) n of
    Yes (c**t) => case decEq b c of
      Yes Refl => Yes $ Lam t
      No ctra  => No \(Lam t0) => ctra $ neuUniq t0 t
    No ctra    => No \(Lam t0) => ctra (b**t0)
  inherit g (Emb nv)   a        = case synthV g nv of
    Yes (b**m) => case decEq a b of
      Yes prf => Yes $ Emb m (sym prf)
      No ctra => No \(Emb m0 prf) => ctra $ trans (sym prf) (neuVUniq m0 m)
    No ctra    => No \(Emb m0 Refl) => ctra (a ** m0)
