module Lambda.STLC.Term

import Data.List

import Lambda.STLC.Ty
import Lambda.Untyped.TermDB

%default total
%access public export

elem2Nat : Elem a g -> Nat
elem2Nat  Here      = Z
elem2Nat (There el) = S (elem2Nat el)

data Term : List Ty -> Ty -> Type where
  Var : Elem a g -> Term g a 
  Lam : Term (a::g) b -> Term g (a~>b)
  App : Term g (a~>b) -> Term g a -> Term g b

forget : Term g a -> Term
forget (Var el)    = Var $ elem2Nat el
forget (Lam t)     = Lam $ forget t
forget (App t1 t2) = App (forget t1) (forget t2)

TestTy : Ty
TestTy = A~>A

TestTm1 : Term [] TestTy
TestTm1 = App (App (Lam $ Var Here) (Lam $ Var Here)) (Lam $ Var Here)

test1 : forget TestTm1 = Term1
test1 = Refl

TestTm2 : Term [] TestTy
TestTm2 = App (Lam $ Var Here) (App (Lam $ Var Here) (Lam $ Var Here))

test2 : forget TestTm2 = Term2
test2 = Refl

ResultTm : Term [] TestTy
ResultTm = Lam $ Var Here  
