module LJ.T.TyCheck

import Data.List
import TParsec
import Ctx
import Parse
import Lambda.STLC.Ty
import LJ.T.Term
import LJ.T.Parser

%access public export
%default total

-- bidirectional typechecker

mutual
  data Val : Ctx Ty -> Val -> Ty -> Type where
    Lam  : Val ((s,a)::g) v b -> Val g (Lam s v) (a~>b)
    Emb  : Neu g m a -> a = b -> Val g (Emb m) b

  data Spn : Ctx Ty -> Ty -> Spn -> Ty -> Type where
    Nil  : Spn g a Nil a
    Cons : Val g m a -> Spn g b k c -> Spn g (a~>b) (Cons m k) c

  data Neu : Ctx Ty -> Neu -> Ty -> Type where
    Var : InCtx g s a -> Spn g a k b -> Neu g (Var s k) b
    Cut : Neu g m a -> Spn g a k b -> Neu g (Cut m k) b
    Ann : Val g m a -> Neu g (Ann m a) a

Uninhabited (Val g (Lam s v) A) where
  uninhabited (Lam _) impossible

Uninhabited (Spn g A (Cons m k) b) where
  uninhabited (Cons _ _) impossible

spnUniq : Spn g c k a -> Spn g c k b -> a = b
spnUniq  Nil            Nil           = Refl
spnUniq (Cons _ k1)    (Cons _ k2)    = spnUniq k1 k2

neuUniq : Neu g m a -> Neu g m b -> a = b
neuUniq {g} {a} (Var {k} i1 k1) (Var i2 k2) = spnUniq (replace {P=\z=>Spn g z k a} (inCtxUniq i1 i2) k1) k2
neuUniq {g} {a} (Cut {k} n1 k1) (Cut n2 k2) = spnUniq (replace {P=\z=>Spn g z k a} (neuUniq n1 n2) k1) k2
neuUniq         (Ann v1)        (Ann v2)    = Refl

notVarArg : InCtx g s a -> Not (b ** Spn g a k b) -> Not (b ** Neu g (Var s k) b)
notVarArg el ns (b**Var el2 q) = let Refl = inCtxUniq el el2 in ns (b**q)

notCutArg : Neu g m a -> Not (b ** Spn g a k b) -> Not (b ** Neu g (Cut m k) b)
notCutArg n ns (b**Cut t q) = let Refl = neuUniq n t in ns (b**q)

notSwitch : Neu g m a -> Not (a = b) -> Not (Val g (Emb m) b)
notSwitch n neq (Emb v eq) = let Refl = neuUniq n v in neq eq

mutual
  synth : (g : Ctx Ty) -> (m : Neu) -> Dec (a ** Neu g m a)
  synth g (Var s k) = case lookup g s of
    Yes (a**el) => case synthS g a k of
      Yes (b**q) => Yes (b ** Var el q)
      No ctra => No $ notVarArg el ctra
    No ctra => No $ \(x ** Var {a} el k) => ctra (a**el)
  synth g (Cut m k) = case synth g m of
    Yes (a ** t) => case synthS g a k of
      Yes (b ** q) => Yes (b ** Cut t q)
      No ctra => No $ notCutArg t ctra
    No ctra => No $ \(_**Cut {a} t _) => ctra (a**t)
  synth g (Ann v t) = case inherit g v t of
    Yes val => Yes (t ** Ann val)
    No ctra => No $ \(_**Ann v) => ctra v

  synthS : (g : Ctx Ty) -> (a : Ty) -> (k : Spn) -> Dec (b ** Spn g a k b)
  synthS g  a         Nil       = Yes (a ** Nil)
  synthS g  A        (Cons m k) = No $ \(_**c) => absurd c
  synthS g (Imp a b) (Cons m k) = case inherit g m a of
    Yes t => case synthS g b k of
      Yes (c ** q) => Yes (c ** Cons t q)
      No ctra => No $ \(c**Cons _ q) => ctra (c ** q)
    No ctra => No $ \(a**Cons t _) => ctra t

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inherit g (Lam s v)      A        = No uninhabited
  inherit g (Lam s v)     (Imp a b) = case inherit ((s,a)::g) v b of
    Yes w => Yes $ Lam w
    No ctra => No $ \(Lam w) => ctra w
  inherit g (Emb n)        a        = case synth g n of
    Yes (b ** m) => case decEq a b of
      Yes prf => Yes $ Emb m (sym prf)
      No ctra => No $ notSwitch m (ctra . sym)
    No ctra => No $ \(Emb m Refl) => ctra (a ** m)

mutual
  val2Term : Val g m a -> TermJ (eraseCtx g) a
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term (Emb v Refl) = neu2Term v

  spn2Spine : Spn g a k b -> Spine (eraseCtx g) a b
  spn2Spine  Nil       = Nil
  spn2Spine (Cons v k) = Cons (val2Term v) (spn2Spine k)

  neu2Term : Neu g m a -> TermJ (eraseCtx g) a
  neu2Term (Var el k) = Var (eraseInCtx el) (spn2Spine k)
  neu2Term (Cut t k)  = Cut (neu2Term t) (spn2Spine k)
  neu2Term (Ann v)    = val2Term v

parseCheckTerm : String -> Either Error (a ** TermJ [] a)
parseCheckTerm s = do b <- parseNeu s
                      case synth [] b of
                        Yes (a ** n) => Right (a ** neu2Term n)
                        No _ => Left TypeError
