module LambdaMu.PCF.Top.TyCheck

import Data.List
import TParsec
import Ctx
import Parse
import LambdaMu.Ty
import LambdaMu.PCF.Top.Term
import LambdaMu.PCF.Top.Parser

%access public export
%default total

-- bidirectional typechecker

mutual
  data Val : Ctx Ty -> Val -> Ty -> Ctx Ty -> Type where
    Lam : Val ((s,a)::g) v b d -> Val g (Lam s v) (a~>b) d
    Mu : ValC g v ((s,a)::d) -> Val g (Mu s v) a d
    Zero : Val g Zero A d
    Succ : Val g m A d -> Val g (Succ m) A d
    If0 : Neu g l A d -> Val g m a d -> Val ((s,A)::g) n a d -> Val g (If0 l m s n) a d
    Fix : Val ((s,a)::g) n a d -> Val g (Fix s n) a d
    Emb : Neu g m a d -> a = b -> Val g (Emb m) b d

  data ValC : Ctx Ty -> Val -> Ctx Ty -> Type where
    Named : InCtx d s a -> Val g v a d -> ValC g (Named s v) d
    Top : Val g v Bot d -> ValC g (Top v) d

  data Neu : Ctx Ty -> Neu -> Ty -> Ctx Ty -> Type where
    Var : InCtx g s a -> Neu g (Var s) a d
    App : Neu g l (a~>b) d -> Val g m a d -> Neu g (App l m) b d
    Cut : Val g m a d -> Neu g (Cut m a) a d

Uninhabited (Val g (Lam s t) A d) where
  uninhabited (Lam _) impossible

Uninhabited (Val g (Lam s t) Bot d) where
  uninhabited (Lam _) impossible

Uninhabited (Val g (Named s t) a d) where
  uninhabited (Lam _) impossible
  uninhabited (Mu _) impossible
  uninhabited (Emb _ _) impossible

Uninhabited (Val g Zero Bot d) where
  uninhabited  Zero impossible

Uninhabited (Val g Zero (Imp a b) d) where
  uninhabited  Zero impossible

Uninhabited (Val g (Succ s) Bot d) where
  uninhabited (Succ _) impossible

Uninhabited (Val g (Succ s) (Imp a b) d) where
  uninhabited (Succ _) impossible

Uninhabited (Val g (Top t) a d) where
  uninhabited (Lam _) impossible
  uninhabited (Mu _) impossible
  uninhabited (Emb _ _) impossible

Uninhabited (ValC g (Lam s t) d) where
  uninhabited (Named _ _) impossible
  uninhabited (Top _) impossible

Uninhabited (ValC g (Mu s t) d) where
  uninhabited (Named _ _) impossible
  uninhabited (Top _) impossible

Uninhabited (ValC g Zero d) where
  uninhabited (Named _ _) impossible
  uninhabited (Top _) impossible

Uninhabited (ValC g (Succ t) d) where
  uninhabited (Named _ _) impossible
  uninhabited (Top _) impossible

Uninhabited (ValC g (If0 p t x f) d) where
  uninhabited (Named _ _) impossible
  uninhabited (Top _) impossible

Uninhabited (ValC g (Fix x t) d) where
  uninhabited (Named _ _) impossible
  uninhabited (Top _) impossible

Uninhabited (ValC g (Emb t) d) where
  uninhabited (Named _ _) impossible
  uninhabited (Top _) impossible

neuUniq : Neu g m a d -> Neu g m b d -> a = b
neuUniq (Var i1)   (Var i2)   = inCtxUniq i1 i2
neuUniq (App t1 _) (App t2 _) = snd $ impInj $ neuUniq t1 t2
neuUniq (Cut v1)   (Cut v2)   = Refl

notArg : Neu g l (a~>b) d -> Not (Val g m a d) -> Not (c ** Neu g (App l m) c d)
notArg n nv (c**App t u) = let Refl = fst $ impInj $ neuUniq n t in nv u

notSwitch : Neu g m a d -> Not (a = b) -> Not (Val g (Emb m) b d)
notSwitch n neq (Emb v eq) = let Refl = neuUniq n v in neq eq

notNamed : InCtx d s a -> Not (Val g v a d) -> Not (ValC g (Named s v) d)
notNamed ic nv (Named ic2 v) = let Refl = inCtxUniq ic ic2 in nv v

notTop : Not (Val g v Bot d) -> Not (ValC g (Top v) d)
notTop nv (Top v) = nv v

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
  inherit g (Mu s v)       a        d = case inheritC g v ((s,a)::d) of
    Yes w => Yes $ Mu w
    No ctra => No $ \(Mu w) => ctra w
  inherit g (Named s v)    a        d = No uninhabited
  inherit g (Top v)        a        d = No uninhabited
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
  inherit g (Emb n)         a        d = case synth g n d of
    Yes (b ** m) => case decEq a b of
      Yes prf => Yes $ Emb m (sym prf)
      No ctra => No $ notSwitch m (ctra . sym)
    No ctra => No $ \(Emb m Refl) => ctra (a ** m)

  inheritC : (g : Ctx Ty) -> (m : Val) -> (d : Ctx Ty) -> Dec (ValC g m d)
  inheritC g (Lam s v)     d = No uninhabited
  inheritC g (Mu s v)      d = No uninhabited
  inheritC g (Emb n)       d = No uninhabited
  inheritC g  Zero         d = No uninhabited
  inheritC g (Succ s)      d = No uninhabited
  inheritC g (If0 p t x f) d = No uninhabited
  inheritC g (Fix s v)     d = No uninhabited
  inheritC g (Named s v)   d = case lookup d s of
    Yes (a**el) => case inherit g v a d of
      Yes w => Yes $ Named el w
      No ctra => No $ notNamed el ctra
    No ctra => No $ \(Named {a} e _) => ctra (a ** e)
  inheritC g (Top v)       d = case inherit g v Bot d of
    Yes w => Yes $ Top w
    No ctra => No $ notTop ctra

mutual
  val2Term : Val g m a d -> Term (eraseCtx g) a (eraseCtx d)
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term (Mu v)       = Mu $ valc2Cmd v
  val2Term  Zero        = Zero
  val2Term (Succ v)     = Succ $ val2Term v
  val2Term (If0 p t f)  = If0 (neu2Term p) (val2Term t) (val2Term f)
  val2Term (Fix v)      = Fix $ val2Term v
  val2Term (Emb v Refl) = neu2Term v

  valc2Cmd : ValC g m d -> Cmd (eraseCtx g) (eraseCtx d)
  valc2Cmd (Named e v) = Named (eraseInCtx e) (val2Term v)
  valc2Cmd (Top v)     = Top (val2Term v)

  neu2Term : Neu g m a d -> Term (eraseCtx g) a (eraseCtx d)
  neu2Term (Var i)   = Var $ eraseInCtx i
  neu2Term (Cut v)   = val2Term v
  neu2Term (App t u) = App (neu2Term t) (val2Term u)

parseCheckTerm : String -> Either Error (a ** Term [] a [])
parseCheckTerm s = do b <- parseNeu s
                      case synth [] b [] of
                        Yes (a ** n) => Right (a ** neu2Term n)
                        No _ => Left TypeError
