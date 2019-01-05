module Lambda.STLC.Term

import Data.List

import Lambda.STLC.Ty

%default total
%access public export

data Term : List Ty -> Ty -> Type where
  Var : Elem a g -> Term g a 
  Lam : Term (a::g) b -> Term g (a~>b)
  App : Term g (a~>b) -> Term g a -> Term g b
  
TestTy : Ty
TestTy = A~>A

TestTm1 : Term [] TestTy
TestTm1 = App (App (Lam $ Var Here) (Lam $ Var Here)) (Lam $ Var Here)

TestTm2 : Term [] TestTy
TestTm2 = App (Lam $ Var Here) (App (Lam $ Var Here) (Lam $ Var Here))

ResultTm : Term [] TestTy
ResultTm = Lam $ Var Here  