module LJ.T.Bidi.Reforest1

import Data.List
import Ctx
import Lambda.STLC.Ty
import Lambda.STLC.Term
import Lambda.STLC.Parser
import Lambda.STLC.TyCheck

%access public export
%default total

data Spine : Neu -> Val -> Ty -> Type where
  SEmb : (a : Ty) -> Spine n (Emb n) a
  SApp : (v : Val) -> Spine (App n v) w a -> Spine n w a

data Head : Val -> Ty -> Type where
  HVar : (s : String) -> Spine (Var s) m a -> Head m a
  HCut : (v : Val) -> (t : Ty) -> Spine (Cut v t) m a -> Head m a

synthR1 : (g : Ctx Ty) -> (n : Neu) -> Spine n m a -> Head m a
synthR1 g (Var s)   sp = HVar s sp
synthR1 g (App t u) sp = synthR1 g t (SApp u sp)
synthR1 g (Cut v t) sp = HCut v t sp

mutual
  headR1 : (g : Ctx Ty) -> Head m a -> Dec (Val g m a)
  headR1 g (HVar s sp) = applyR1 g sp $ case lookup g s of
    Yes (b**el) => Yes (b ** Var el)
    No ctra => No $ \(b ** Var el) => ctra (b ** el)
  headR1 g (HCut v t sp) = applyR1 g sp $ case assert_total $ inheritR1 g v t of
    Yes val => Yes (t ** Cut val)
    No ctra => No $ \(_**Cut v) => ctra v

  applyR1 : (g : Ctx Ty) -> Spine n m a -> Dec (b ** Neu g n b) -> Dec (Val g m a)
  applyR1 g (SApp v sp) bne = assert_total $ applyR1 g sp $ case bne of
    No ctra => No $ \(b**App {a} v _) => ctra ((a~>b) ** v)
    Yes (A      **x) => No $ \(_**App v _) => uninhabited $ neuUniq v x
    Yes (Imp a b**x) => case inheritR1 g v a of
      Yes y => Yes (b ** App x y)
      No ctra => No $ notArg x ctra
  applyR1 g (SEmb a)    bne = case bne of
    No ctra    => No $ \(Emb m Refl) => ctra (a ** m)
    Yes (b**n) => case decEq a b of
      Yes prf => Yes (Emb n (sym prf))
      No ctra => No $ notSwitch n (ctra . sym)

  inheritR1 : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inheritR1 _ (Lam _ _)  A        = No uninhabited
  inheritR1 g (Lam s v) (Imp a b) = case inheritR1 ((s,a)::g) v b of
    Yes w => Yes $ Lam w
    No ctra => No $ \(Lam w) => ctra w
  inheritR1 g (Emb n)    a        = headR1 g $ synthR1 g n (SEmb a)
