module LJ.T.Bidi.Reforest2

import Data.List
import Ctx
import Lambda.STLC.Ty
import Lambda.STLC.Term
import Lambda.STLC.Parser

%access public export
%default total

mutual
  data Value : Type where
    Lam : String -> Value -> Value
    H   : Head -> Value

  data Spine : Type where
    SEmb : Spine
    SApp : Value -> Spine -> Spine

  data Head : Type where
    HVar : String -> Spine -> Head
    HCut : Value -> Ty -> Spine -> Head

mutual
  revSpine : Neu -> Spine -> Head
  revSpine (Var s)   sp = HVar s sp
  revSpine (App t u) sp = revSpine t (SApp (rev u) sp)
  revSpine (Cut v t) sp = HCut (rev v) t sp

  rev : Val -> Value
  rev (Lam s v) = Lam s (rev v)
  rev (Emb n)   = H $ revSpine n SEmb

mutual
  data Vl : Ctx Ty -> Value -> Ty -> Type where
    VlLam : Vl ((s,a)::g) v b -> Vl g (Lam s v) (a~>b)
    VlHd  : Hd g m a -> a = b -> Vl g (H m) b

  data Spn : Ctx Ty -> Ty -> Spine -> Ty -> Type where
    SpEmb : Spn g a SEmb a
    SpApp : Vl g m a -> Spn g b k c -> Spn g (a~>b) (SApp m k) c

  data Hd : Ctx Ty -> Head -> Ty -> Type where
    HdVar : InCtx g s a -> Spn g a k b -> Hd g (HVar s k) b
    HdCut : Vl g m a -> Spn g a k b -> Hd g (HCut m a k) b

Uninhabited (Vl g (Lam s v) A) where
  uninhabited (VlLam _) impossible

Uninhabited (Spn g A (SApp m k) b) where
  uninhabited (SpApp _ _) impossible

spnUniq : Spn g c k a -> Spn g c k b -> a = b
spnUniq  SpEmb        SpEmb       = Refl
spnUniq (SpApp _ k1) (SpApp _ k2) = spnUniq k1 k2

hdUniq : Hd g m a -> Hd g m b -> a = b
hdUniq (HdVar i1 k1) (HdVar i2 k2) = let Refl = inCtxUniq i1 i2 in spnUniq k1 k2
hdUniq (HdCut _ k1)  (HdCut _ k2) = spnUniq k1 k2

notVarArg : InCtx g s a -> Not (b ** Spn g a k b) -> Not (b ** Hd g (HVar s k) b)
notVarArg el ns (b**HdVar el2 q) = let Refl = inCtxUniq el el2 in ns (b**q)

notSwitch : Hd g m a -> Not (a = b) -> Not (Vl g (H m) b)
notSwitch n neq (VlHd v eq) = let Refl = hdUniq n v in neq eq

mutual
  headR2 : (g : Ctx Ty) -> (n : Head) -> (Dec (b ** Hd g n b) -> Dec (Vl g m a)) -> Dec (Vl g m a)
  headR2 g (HVar x sp)   f = f $ case lookup g x of
    Yes (a**el) => spineR2 g sp a $ \k => case k of
      Yes (b**q) => Yes (b ** HdVar el q)
      No ctra => No $ notVarArg el ctra
    No ctra => No $ \(_ ** HdVar {a} el _) => ctra (a ** el)
  headR2 g (HCut v t sp) f = f $ case inheritR2 g v t of
    Yes val => spineR2 g sp t $ \k => case k of
      Yes (b**q) => Yes (b ** HdCut val q)
      No ctra => No $ \(b ** HdCut _ q) => ctra (b ** q)
    No ctra => No $ \(_ ** HdCut w _) => ctra w

  spineR2 : (g : Ctx Ty) -> (k : Spine) -> (a : Ty) -> (Dec (b ** Spn g a k b) -> Dec (b ** Hd g n b)) -> Dec (b ** Hd g n b)
  spineR2 g  SEmb       a        f = f $ Yes (a ** SpEmb)
  spineR2 g (SApp v s)  A        f = f $ No $ \(_**c) => absurd c
  spineR2 g (SApp v s) (Imp a b) f = spineR2 g s b $ \k => f $ case k of
    Yes (c**q) => case inheritR2 g v a of
      Yes val => Yes (c ** SpApp val q)
      No ctra => No $ \(_**SpApp t _) => ctra t
    No ctra => No $ \(c**SpApp _ q) => ctra (c**q)

  inheritR2 : (g : Ctx Ty) -> (m : Value) -> (a : Ty) -> Dec (Vl g m a)
  inheritR2 _ (Lam _ _)  A        = No uninhabited
  inheritR2 g (Lam x v) (Imp a b) = case inheritR2 ((x,a)::g) v b of
    Yes w => Yes $ VlLam w
    No ctra => No $ \(VlLam w) => ctra w
  inheritR2 g (H h)      a        =
    headR2 g h $ \dh => case dh of
      Yes (b**he) => case decEq a b of
                       Yes prf => Yes $ VlHd he (sym prf)
                       No ctra => No $ notSwitch he (ctra . sym)
      No ctra => No $ \(VlHd m Refl) => ctra (a ** m)
