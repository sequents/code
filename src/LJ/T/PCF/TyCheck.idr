module LJ.T.PCF.TyCheck

import Data.List
import TParsec
import Ctx
import Parse
import Lambda.STLC.Ty
import LJ.T.PCF.Term
import LJ.T.PCF.Parser

%access public export
%default total

-- bidirectional typechecker

mutual
  data Val : Ctx Ty -> Val -> Ty -> Type where
    Lam  : Val ((s,a)::g) v b -> Val g (Lam s v) (a~>b)
    Zero : Val g Zero A
    Succ : Val g m A -> Val g (Succ m) A
    Fix  : Val ((s,a)::g) n a -> Val g (Fix s n) a
    Emb  : Neu g m a -> a = b -> Val g (Emb m) b

  data Spn : Ctx Ty -> Ty -> Spn -> Ty -> Type where
    Nil  : Spn g a Nil a
    Cons : Val g m a -> Spn g b k c -> Spn g (a~>b) (Cons m k) c
    Tst  : Neu g t a -> Val ((s,A)::g) f a -> Spn g a k b -> Spn g A (Tst t s f k) b
    Inc  : Spn g A k b -> Spn g A (Inc k) b

  data Neu : Ctx Ty -> Neu -> Ty -> Type where
    Var : InCtx g s a -> Spn g a k b -> Neu g (Var s k) b
    Cut : Neu g m a -> Spn g a k b -> Neu g (Cut m k) b
    Ann : Val g m a -> Neu g (Ann m a) a

Uninhabited (Val g (Lam s v) A) where
  uninhabited (Lam _) impossible

Uninhabited (Val g Zero (Imp a b)) where
  uninhabited  Zero impossible

Uninhabited (Val g (Succ s) (Imp a b)) where
  uninhabited (Succ _) impossible

Uninhabited (Spn g A (Cons m k) b) where
  uninhabited (Cons _ _) impossible

Uninhabited (Spn g (Imp a b) (Tst t s f k) c) where
  uninhabited (Tst _ _ _) impossible

Uninhabited (Spn g (Imp a b) (Inc k) c) where
  uninhabited (Inc _) impossible

mutual
  spnUniq : Spn g c k a -> Spn g c k b -> a = b
  spnUniq  Nil           Nil          = Refl
  spnUniq (Cons _ k1)   (Cons _ k2)   = spnUniq k1 k2
  spnUniq (Tst t1 _ k1) (Tst t2 _ k2) = let Refl = neuUniq t1 t2 in spnUniq k1 k2
  spnUniq (Inc k1)      (Inc k2)      = spnUniq k1 k2

  neuUniq : Neu g m a -> Neu g m b -> a = b
  neuUniq (Var i1 k1) (Var i2 k2) = let Refl = inCtxUniq i1 i2 in spnUniq k1 k2
  neuUniq (Cut n1 k1) (Cut n2 k2) = let Refl = neuUniq n1 n2 in spnUniq k1 k2
  neuUniq (Ann v1)    (Ann v2)    = Refl

notVarArg : InCtx g s a -> Not (b ** Spn g a k b) -> Not (b ** Neu g (Var s k) b)
notVarArg el ns (b**Var el2 q) = let Refl = inCtxUniq el el2 in ns (b**q)

notCutArg : Neu g m a -> Not (b ** Spn g a k b) -> Not (b ** Neu g (Cut m k) b)
notCutArg n ns (b**Cut t q) = let Refl = neuUniq n t in ns (b**q)

notTstElse : Neu g t a -> Not (Val ((s,A)::g) f a) -> Not (b ** Spn g A (Tst t s f k) b)
notTstElse n nv (b**Tst t f _) = let Refl = neuUniq n t in nv f

notTstArg : Neu g t a -> Not (b ** Spn g a k b) -> Not (b ** Spn g A (Tst t s f k) b)
notTstArg n ns (b**Tst t _ q) = let Refl = neuUniq n t in ns (b**q)

notSwitch : Neu g m a -> Not (a = b) -> Not (Val g (Emb m) b)
notSwitch n neq (Emb v eq) = let Refl = neuUniq n v in neq eq

mutual
  synth : (g : Ctx Ty) -> (m : Neu) -> Dec (a ** Neu g m a)
  synth g (Var s k) = case lookup g s of
    Yes (a**el) => case synthS g a k of
      Yes (b**q) => Yes (b ** Var el q)
      No ctra => No $ notVarArg el ctra
    No ctra => No $ \(_**Var {a} el _) => ctra (a**el)
  synth g (Cut m k) = case synth g m of
    Yes (a**t) => case synthS g a k of
      Yes (b**q) => Yes (b ** Cut t q)
      No ctra => No $ notCutArg t ctra
    No ctra => No $ \(_**Cut {a} t _) => ctra (a**t)
  synth g (Ann v t) = case inherit g v t of
    Yes val => Yes (t ** Ann val)
    No ctra => No $ \(_**Ann v) => ctra v

  synthS : (g : Ctx Ty) -> (a : Ty) -> (k : Spn) -> Dec (b ** Spn g a k b)
  synthS g  a         Nil          = Yes (a ** Nil)
  synthS g  A        (Cons m k)    = No $ \(_**c) => absurd c
  synthS g (Imp a b) (Cons m k)    = case inherit g m a of
    Yes t => case synthS g b k of
      Yes (c**q) => Yes (c ** Cons t q)
      No ctra => No $ \(c**Cons _ q) => ctra (c**q)
    No ctra => No $ \(_**Cons t _) => ctra t
  synthS g  A        (Tst t s f k) = case synth g t of
    Yes (a**t1) => case inherit ((s,A)::g) f a of
      Yes f1 => case synthS g a k of
        Yes (b**q) => Yes (b ** Tst t1 f1 q)
        No ctra => No $ notTstArg t1 ctra
      No ctra => No $ notTstElse t1 ctra
    No ctra => No $ \(_**Tst {a} t2 _ _) => ctra (a**t2)
  synthS g (Imp a b) (Tst t s f k) = No $ \(_**c) => absurd c
  synthS g  A        (Inc k)      = case synthS g A k of
    Yes (b**q) => Yes (b**Inc q)
    No ctra => No $ \(b**Inc q) => ctra (b**q)
  synthS g (Imp a b) (Inc k)      = No $ \(_**c) => absurd c

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inherit _ (Lam _ _)      A        = No uninhabited
  inherit g (Lam s v)     (Imp a b) = case inherit ((s,a)::g) v b of
    Yes w => Yes $ Lam w
    No ctra => No $ \(Lam w) => ctra w
  inherit g  Zero           A        = Yes Zero
  inherit g  Zero          (Imp a b) = No uninhabited
  inherit g (Succ m)        A        = case inherit g m A of
    Yes w => Yes $ Succ w
    No ctra => No $ \(Succ w) => ctra w
  inherit g (Succ m)       (Imp a b) = No uninhabited
  inherit g (Fix x n)       a        = case inherit ((x,a)::g) n a of
    Yes u => Yes $ Fix u
    No ctra => No $ \(Fix u) => ctra u
  inherit g (Emb n)        a        = case synth g n of
    Yes (b**m) => case decEq a b of
      Yes prf => Yes $ Emb m (sym prf)
      No ctra => No $ notSwitch m (ctra . sym)
    No ctra => No $ \(Emb m Refl) => ctra (a ** m)

mutual
  val2Term : Val g m a -> TermJ (eraseCtx g) a
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term  Zero        = Zero
  val2Term (Succ v)     = Succ $ val2Term v
  val2Term (Fix v)      = Fix $ val2Term v
  val2Term (Emb v Refl) = neu2Term v

  spn2Spine : Spn g a k b -> Spine (eraseCtx g) a b
  spn2Spine  Nil        = Nil
  spn2Spine (Cons v k)  = Cons (val2Term v) (spn2Spine k)
  spn2Spine (Tst t f k) = Tst (neu2Term t) (val2Term f) (spn2Spine k)
  spn2Spine (Inc k)     = Inc $ spn2Spine k

  neu2Term : Neu g m a -> TermJ (eraseCtx g) a
  neu2Term (Var el k) = Var (eraseInCtx el) (spn2Spine k)
  neu2Term (Cut t k)  = Cut (neu2Term t) (spn2Spine k)
  neu2Term (Ann v)    = val2Term v

parseCheckTerm : String -> Either Error (a ** TermJ [] a)
parseCheckTerm s = do b <- parseNeu s
                      case synth [] b of
                        Yes (a ** n) => Right (a ** neu2Term n)
                        No _ => Left $ TypeError ""
