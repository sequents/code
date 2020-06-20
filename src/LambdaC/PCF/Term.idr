module LambdaC.PCF.Term

import Data.List
--import Iter
import Subset

import Lambda.STLC.Ty
import Lambda.PCF.Term

%default total
%access public export

-- Moggi's lambda-C

mutual
  data Val : List Ty -> Ty -> Type where
    Var  : Elem a g -> Val g a
    Lam  : Tm (a::g) b -> Val g (a~>b)
    Zero : Val g A
    Succ : Tm g A -> Val g A

  data Tm : List Ty -> Ty -> Type where
    V   : Val g a -> Tm g a
    App : Tm g (a~>b) -> Tm g a -> Tm g b
    Let : Tm g a -> Tm (a::g) b -> Tm g b
    If0 : Tm g A -> Tm g a -> Tm (A::g) a -> Tm g a
    Fix : Tm (a::g) a -> Tm g a

-- structural rules

mutual
  renameVal : Subset g d -> Val g a -> Val d a
  renameVal sub (Var el) = Var $ sub el
  renameVal sub (Lam t)  = Lam $ renameTm (ext sub) t
  renameVal sub  Zero    = Zero
  renameVal sub (Succ n) = Succ $ renameTm sub n

  renameTm : Subset g d -> Tm g a -> Tm d a
  renameTm sub (V v)       = V $ renameVal sub v
  renameTm sub (App t u)   = App (renameTm sub t) (renameTm sub u)
  renameTm sub (Let m n)   = Let (renameTm sub m) (renameTm (ext sub) n)
  renameTm sub (If0 p t f) = If0 (renameTm sub p) (renameTm sub t) (renameTm (ext sub) f)
  renameTm sub (Fix f)     = Fix $ renameTm (ext sub) f

shiftVal : {auto is : IsSubset g d} -> Val g a -> Val d a
shiftVal {is} = renameVal (shift is)

shiftTm : {auto is : IsSubset g d} -> Tm g a -> Tm d a
shiftTm {is} = renameTm (shift is)

-- STLC conversion

encodePCF : Term g a -> Tm g a
encodePCF (Var e)     = V $ Var e
encodePCF (Lam t)     = V $ Lam $ encodePCF t
encodePCF (App t u)   = App (encodePCF t) (encodePCF u)
encodePCF  Zero       = V Zero
encodePCF (Succ n)    = V $ Succ $ encodePCF n
encodePCF (If0 p t f) = If0 (encodePCF p) (encodePCF t) (encodePCF f)
encodePCF (Fix f)     = Fix $ encodePCF f

mutual
  forgetVal : Val g a -> Term g a
  forgetVal (Var el) = Var el
  forgetVal (Lam t)  = Lam $ forgetTm t
  forgetVal  Zero    = Zero
  forgetVal (Succ n) = Succ $ forgetTm n

  forgetTm : Tm g a -> Term g a
  forgetTm (V v)       = forgetVal v
  forgetTm (App m n)   = App (forgetTm m) (forgetTm n)
  forgetTm (Let n m)   = App (Lam $ forgetTm m) (forgetTm n)
  forgetTm (If0 p t f) = If0 (forgetTm p) (forgetTm t) (forgetTm f)
  forgetTm (Fix f)     = Fix $ forgetTm f
