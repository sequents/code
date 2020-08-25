module LJ.T.Bidi.CPS

import Data.List
import Ctx
import Lambda.STLC.Ty
import Lambda.STLC.Term
import Lambda.STLC.Parser
import Lambda.STLC.TyCheck

%access public export
%default total

mutual
  synthC : (g : Ctx Ty) -> (n : Neu) -> (Dec (b ** Neu g n b) -> Dec (Val g m a)) -> Dec (Val g m a)
  synthC g (Var s)   f = f $ case lookup g s of
                               Yes (b**el) => Yes (b**Var el)
                               No ctra => No $ \(a**Var el) => ctra (a ** el)
  synthC g (App t u) f =
    synthC g t $ \dn => f $ case dn of
      Yes (A**n) => No $ \(_**App v _) => uninhabited $ neuUniq v n
      Yes ((Imp a b)**n) => case inherit g u a of
                              Yes m => Yes (b ** App n m)
                              No ctra => No $ notArg n ctra
      No ctra => No $ \(b**App {a} v _) => ctra ((a~>b) ** v)
  synthC g (Cut v t) f = f $ case inheritC g v t of
     Yes val => Yes (t**Cut val)
     No ctra => No $ \(_**Cut v) => ctra v

  inheritC : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inheritC _ (Lam _ _)  A        = No uninhabited
  inheritC g (Lam s v) (Imp a b) =
    case inheritC ((s,a)::g) v b of
      Yes w => Yes $ Lam w
      No ctra => No $ \(Lam w) => ctra w
  inheritC g (Emb n)    a        =
    synthC g n $ \dn => case dn of
      Yes (b**ne) => case decEq a b of
                       Yes prf => Yes $ Emb ne (sym prf)
                       No ctra => No $ notSwitch ne (ctra . sym)
      No ctra => No $ \(Emb m Refl) => ctra (a ** m)
