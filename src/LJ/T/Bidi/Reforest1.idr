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

applyD : (g : Ctx Ty) -> Spine n m a -> Dec (b ** Neu g n b) -> Dec (Val g m a)
applyD g (SApp v sp) bne = applyD g sp $ case bne of
  No ctra => No $ \(b**App {a} v _) => ctra ((a~>b) ** v)
  Yes (A      **x) => No $ \(_**App v _) => uninhabited $ neuUniq v x
  Yes (Imp a b**x) => case inherit g v a of
    Yes y => Yes (b ** App x y)
    No ctra => No $ notArg x ctra
applyD g (SEmb a)    bne = case bne of
  No ctra    => No $ \(Emb m Refl) => ctra (a ** m)
  Yes (b**n) => case decEq a b of
    Yes prf => Yes (Emb n (sym prf))
    No ctra => No $ notSwitch n (ctra . sym)

data Head : Val -> Ty -> Type where
  HVar : (s : String) -> Spine (Var s) m a -> Head m a
  HCut : (v : Val) -> (t : Ty) -> Spine (Cut v t) m a -> Head m a

mutual
  head : (g : Ctx Ty) -> Head m a -> Dec (Val g m a)
  head g (HVar s sp) = applyD g sp $ case lookup g s of
    Yes (b**el) => Yes (b ** Var el)
    No ctra => No $ \(b ** Var el) => ctra (b ** el)
  head g (HCut v t sp) = applyD g sp $ case assert_total $ inheritD g v t of
    Yes val => Yes (t ** Cut val)
    No ctra => No $ \(_**Cut v) => ctra v

  synthD : (g : Ctx Ty) -> (n : Neu) -> Spine n m a -> Head m a
  synthD g (Var s)   sp = HVar s sp
  synthD g (App t u) sp = synthD g t (SApp u sp)
  synthD g (Cut v t) sp = HCut v t sp

  inheritD : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inheritD _ (Lam _ _)  A        = No uninhabited
  inheritD g (Lam s v) (Imp a b) = case inheritD ((s,a)::g) v b of
    Yes w => Yes $ Lam w
    No ctra => No $ \(Lam w) => ctra w
  inheritD g (Emb n)    a        = head g $ synthD g n (SEmb a)
