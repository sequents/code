module Lambda.PCF.TyCheck

import Data.List
import TParsec
import Ctx
import Parse
import Lambda.STLC.Ty
import Lambda.PCF.Term
import Lambda.PCF.Parser

%access public export
%default total

-- bidirectional typechecker

-- terms indexed with raw terms

mutual
  data Val : Ctx Ty -> Val -> Ty -> Type where
    Lam : Val ((s,a)::g) v b -> Val g (Lam s v) (a~>b)
    Zero : Val g Zero A
    Succ : Val g m A -> Val g (Succ m) A
    If0 : Neu g l A -> Val g m a -> Val ((s,A)::g) n a -> Val g (If0 l m s n) a
    Fix : Val ((s,a)::g) n a -> Val g (Fix s n) a
    Emb : Neu g m a -> a = b -> Val g (Emb m) b

  data Neu : Ctx Ty -> Neu -> Ty -> Type where
    Var : InCtx g s a -> Neu g (Var s) a
    App : Neu g l (a~>b) -> Val g m a -> Neu g (App l m) b
    Cut : Val g m a -> Neu g (Cut m a) a

Uninhabited (Val _ (Lam _ _) A) where
  uninhabited (Lam _) impossible

Uninhabited (Val _ Zero (Imp _ _)) where
  uninhabited  Zero impossible

Uninhabited (Val _ (Succ _) (Imp _ _)) where
  uninhabited (Succ _) impossible

neuUniq : Neu g m a -> Neu g m b -> a = b
neuUniq (Var i1)   (Var i2)   = inCtxUniq i1 i2
neuUniq (App t1 _) (App t2 _) = snd $ impInj $ neuUniq t1 t2
neuUniq (Cut v1)   (Cut v2)   = Refl

notArg : Neu g l (a~>b) -> Not (Val g m a) -> Not (c ** Neu g (App l m) c)
notArg n nv (c**App t u) = let Refl = fst $ impInj $ neuUniq n t in nv u

notSwitch : Neu g m a -> Not (a = b) -> Not (Val g (Emb m) b)
notSwitch n neq (Emb v eq) = let Refl = neuUniq n v in neq eq

mutual
  synth : (g : Ctx Ty) -> (m : Neu) -> Dec (a ** Neu g m a)
  synth g (Var s)   = case lookup g s of
    Yes (a**el) => Yes (a ** Var el)
    No ctra => No $ \(a**Var el) => ctra (a ** el)
  synth g (App t u) = case synth g t of
    Yes (A**n) => No $ \(_**App v _) => uninhabited $ neuUniq v n
    Yes ((Imp a b)**n) => case inherit g u a of
      Yes m => Yes (b ** App n m)
      No ctra => No $ notArg n ctra
    No ctra => No $ \(b**App {a} v _) => ctra ((a~>b) ** v)
  synth g (Cut v t) = case inherit g v t of
    Yes val => Yes (t ** Cut val)
    No ctra => No $ \(_**Cut v) => ctra v

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inherit g (Lam s v)       A        = No uninhabited
  inherit g (Lam s v)      (Imp a b) = case inherit ((s,a)::g) v b of
    Yes w => Yes $ Lam w
    No ctra => No $ \(Lam w) => ctra w
  inherit g  Zero           A        = Yes Zero
  inherit g  Zero          (Imp a b) = No uninhabited
  inherit g (Succ m)        A        = case inherit g m A of
    Yes w => Yes $ Succ w
    No ctra => No $ \(Succ w) => ctra w
  inherit g (Succ m)       (Imp a b) = No uninhabited
  inherit g (If0 l m x n)  a        = case synth g l of
    Yes (A**u) => case inherit g m a of
      Yes v => case inherit ((x, A) :: g) n a of
        Yes w => Yes $ If0 u v w
        No ctra => No $ \(If0 _ _ r) => ctra r
      No ctra => No $ \(If0 _ q _) => ctra q
    Yes ((Imp _ _)**w) => No $ \(If0 p _ _) => uninhabited $ neuUniq w p
    No ctra => No $ \(If0 p _ _) => ctra (A ** p)
  inherit g (Fix x n)       a        = case inherit ((x,a)::g) n a of
    Yes u => Yes $ Fix u
    No ctra => No $ \(Fix u) => ctra u
  inherit g (Emb n)         a        = case synth g n of
    Yes (b ** m) => case decEq a b of
      Yes prf => Yes $ Emb m (sym prf)
      No ctra => No $ notSwitch m (ctra . sym)
    No ctra => No $ \(Emb m Refl) => ctra (a ** m)

-- projecting to PCF terms
mutual
  val2Term : Val g m a -> Term (eraseCtx g) a
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term  Zero        = Zero
  val2Term (Succ v)     = Succ $ val2Term v
  val2Term (If0 p t f)  = If0 (neu2Term p) (val2Term t) (val2Term f)
  val2Term (Fix v)      = Fix $ val2Term v
  val2Term (Emb v Refl) = neu2Term v

  neu2Term : Neu g m a -> Term (eraseCtx g) a
  neu2Term (Var i)   = Var $ eraseInCtx i
  neu2Term (App t u) = App (neu2Term t) (val2Term u)
  neu2Term (Cut v)   = val2Term v

parseCheckTerm : String -> Either Error (a ** Term [] a)
parseCheckTerm s = do b <- parseNeu s
                      case synth [] b of
                        Yes (a ** n) => Right (a ** neu2Term n)
                        No _ => Left $ TypeError ""
{-
private
test0 : parseCheckTerm "(\\x.x : *->*)" = Right (TestTy ** ResultTm)
test0 = Refl

--private
--test1 : parseCheckTerm "(\\x.x : ((*->*)->(*->*))->((*->*)->(*->*))) (\\x.x) (\\x.x)" = Right (TestTy ** TestTm1)
--test1 = Refl

--private
--test2 : parseCheckTerm "(\\x.x : ((*->*)->(*->*))) ((\\x.x : (*->*)->(*->*)) (\\x.x))" = Right (TestTy ** TestTm2)
--test2 = Refl
-}