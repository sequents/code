module LJ.T.Bidi.Defun

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

applyD : (g : Ctx Ty) -> Spine m n a -> Dec (b ** Neu g m b) -> Dec (Val g n a)
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

mutual
  synthD : (g : Ctx Ty) -> (m : Neu) -> Spine m n a -> Dec (Val g n a)
  synthD g (Var s)   sp = applyD g sp $ case lookup g s of
    Yes (b**el) => Yes (b ** Var el)
    No ctra => No $ \(b ** Var el) => ctra (b ** el)
  synthD g (App t u) sp = synthD g t (SApp u sp)
  synthD g (Cut v t) sp = applyD g sp $ case inheritD g v t of
    Yes val => Yes (t**Cut val)
    No ctra => No $ \(_**Cut v) => ctra v

  inheritD : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inheritD _ (Lam _ _)  A        = No uninhabited
  inheritD g (Lam s v) (Imp a b) = case inheritD ((s,a)::g) v b of
    Yes w => Yes $ Lam w
    No ctra => No $ \(Lam w) => ctra w
  inheritD g (Emb n)    a        = synthD g n (SEmb a)
