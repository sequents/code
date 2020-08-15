module LambdaMu.PCF.TyCheck

import Data.List
import TParsec
import Ctx
import Parse
import LambdaMu.Ty
import LambdaMu.PCF.Term
import LambdaMu.PCF.Parser

%access public export
%default total

-- bidirectional typechecker

mutual
  data Val : Ctx Ty -> Val -> Ty -> Ctx Ty -> Type where
    Lam : Val ((s,a)::g) v b d -> Val g (Lam s v) (a~>b) d
    Mu : Val g v Bot ((s,a)::d) -> Val g (Mu s v) a d
    Named : InCtx d s a -> Val g v a d -> Val g (Named s v) Bot d
    Zero : Val g Zero A d
    Succ : Val g m A d -> Val g (Succ m) A d
    If0 : Neu g l A d -> Val g m a d -> Val ((s,A)::g) n a d -> Val g (If0 l m s n) a d
    Fix : Val ((s,a)::g) n a d -> Val g (Fix s n) a d
    Emb : Neu g m a d -> a = b -> Val g (Emb m) b d

  data Neu : Ctx Ty -> Neu -> Ty -> Ctx Ty -> Type where
    Var : InCtx g s a -> Neu g (Var s) a d
    App : Neu g l (a~>b) d -> Val g m a d -> Neu g (App l m) b d
    Cut : Val g m a d -> Neu g (Cut m a) a d

Uninhabited (Val _ (Lam _ _) A _) where
  uninhabited (Lam _) impossible
  uninhabited (Emb _ _) impossible

Uninhabited (Val _ (Lam _ _) Bot _) where
  uninhabited (Lam _) impossible
  uninhabited (Emb _ _) impossible

Uninhabited (Val _ Zero Bot _) where
  uninhabited  Zero impossible

Uninhabited (Val _ Zero (Imp _ _) _) where
  uninhabited  Zero impossible

Uninhabited (Val _ (Succ _) Bot _) where
  uninhabited (Succ _) impossible

Uninhabited (Val _ (Succ _) (Imp _ _) _) where
  uninhabited (Succ _) impossible

Uninhabited (Val _ (Named _ _) A _) where
  uninhabited (Named _ _) impossible
  uninhabited (Emb _ _) impossible

Uninhabited (Val _ (Named _ _) (Imp _ _) _) where
  uninhabited (Named _ _) impossible
  uninhabited (Emb _ _) impossible

neuUniq : Neu g m a d -> Neu g m b d -> a = b
neuUniq (Var i1)   (Var i2)   = inCtxUniq i1 i2
neuUniq (App t1 _) (App t2 _) = snd $ impInj $ neuUniq t1 t2
neuUniq (Cut v1)   (Cut v2)   = Refl

notArg : Neu g l (a~>b) d -> Not (Val g m a d) -> Not (c ** Neu g (App l m) c d)
notArg n nv (c**App t u) = let Refl = fst $ impInj $ neuUniq n t in nv u

notSwitch : Neu g m a d -> Not (a = b) -> Not (Val g (Emb m) b d)
notSwitch n neq (Emb v eq) = let Refl = neuUniq n v in neq eq

notNamed : InCtx d s a -> Not (Val g v a d) -> Not (Val g (Named s v) Bot d)
notNamed ic nv (Named ic2 v) = let Refl = inCtxUniq ic ic2 in nv v

mutual
  synth : (g : Ctx Ty) -> (m : Neu) -> (d : Ctx Ty) -> Dec (a ** Neu g m a d)
  synth g (Var s)   d = case lookup g s of
    Yes (a**el) => Yes (a ** Var el)
    No ctra => No $ \(a**Var el) => ctra (a ** el)
  synth g (App t u) d = case synth g t d of
    Yes (A**n) => No $ \(_**App v _) => uninhabited $ neuUniq v n
    Yes (Bot**n) => No $ \(_**App v _) => uninhabited $ neuUniq v n
    Yes ((Imp a b)**n) => case inherit g u a d of
      Yes m => Yes (b ** App n m)
      No ctra => No $ notArg n ctra
    No ctra => No $ \(b**App {a} v _) => ctra ((a~>b) ** v)
  synth g (Cut v t) d = case inherit g v t d of
    Yes val => Yes (t ** Cut val)
    No ctra => No $ \(_**Cut v) => ctra v

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> (d : Ctx Ty) -> Dec (Val g m a d)
  inherit g (Lam s v)      A        d = No uninhabited
  inherit g (Lam s v)      Bot      d = No uninhabited
  inherit g (Lam s v)     (Imp a b) d = case inherit ((s,a)::g) v b d of
    Yes w => Yes $ Lam w
    No ctra => No $ \(Lam w) => ctra w
  inherit g (Mu s v)       a        d = case inherit g v Bot ((s,a)::d) of
    Yes w => Yes $ Mu w
    No ctra => No $ \(Mu w) => ctra w
  inherit g (Named s v)    A        d = No uninhabited
  inherit g (Named s v)    Bot      d = case lookup d s of
    Yes (a**el) => case inherit g v a d of
      Yes w => Yes $ Named el w
      No ctra => No $ notNamed el ctra
    No ctra => No $ \(Named {a} e _) => ctra (a ** e)
  inherit g (Named s v) (Imp a b) d = No uninhabited
  inherit g  Zero          A        d = Yes Zero
  inherit g  Zero          Bot      d = No uninhabited
  inherit g  Zero         (Imp a b) d = No uninhabited
  inherit g (Succ m)       A        d = case inherit g m A d of
    Yes w => Yes $ Succ w
    No ctra => No $ \(Succ w) => ctra w
  inherit g (Succ m)       Bot      d = No uninhabited
  inherit g (Succ m)      (Imp a b) d = No uninhabited
  inherit g (If0 l m x n)  a        d = case synth g l d of
    Yes (A**u) => case inherit g m a d of
      Yes v => case inherit ((x, A) :: g) n a d of
        Yes w => Yes $ If0 u v w
        No ctra => No $ \(If0 _ _ r) => ctra r
      No ctra => No $ \(If0 _ q _) => ctra q
    Yes (Bot**u) => No $ \(If0 p _ _) => uninhabited $ neuUniq u p
    Yes ((Imp _ _)**w) => No $ \(If0 p _ _) => uninhabited $ neuUniq w p
    No ctra => No $ \(If0 p _ _) => ctra (A ** p)
  inherit g (Fix x n)       a       d = case inherit ((x,a)::g) n a d of
    Yes u => Yes $ Fix u
    No ctra => No $ \(Fix u) => ctra u
  inherit g (Emb n)         a       d = case synth g n d of
    Yes (b ** m) => case decEq a b of
      Yes prf => Yes $ Emb m (sym prf)
      No ctra => No $ notSwitch m (ctra . sym)
    No ctra => No $ \(Emb m Refl) => ctra (a ** m)

mutual
  val2Term : Val g m a d -> Term (eraseCtx g) a (eraseCtx d)
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term (Mu v)       = Mu $ val2Term v
  val2Term (Named e v)  = Named (eraseInCtx e) (val2Term v)
  val2Term  Zero        = Zero
  val2Term (Succ v)     = Succ $ val2Term v
  val2Term (If0 p t f)  = If0 (neu2Term p) (val2Term t) (val2Term f)
  val2Term (Fix v)      = Fix $ val2Term v
  val2Term (Emb v Refl) = neu2Term v

  neu2Term : Neu g m a d -> Term (eraseCtx g) a (eraseCtx d)
  neu2Term (Var i)   = Var $ eraseInCtx i
  neu2Term (Cut v)   = val2Term v
  neu2Term (App t u) = App (neu2Term t) (val2Term u)

parseCheckTerm : String -> Either Error (a ** Term [] a [])
parseCheckTerm s = do b <- parseNeu s
                      case synth [] b [] of
                        Yes (a ** n) => Right (a ** neu2Term n)
                        No _ => Left $ TypeError ""
