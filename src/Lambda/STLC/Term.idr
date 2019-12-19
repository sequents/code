module Lambda.STLC.Term

import Data.Fin
import Data.List
import Control.Isomorphism
import Elem
import Lambda.STLC.Ty
import Lambda.Untyped.TermDB
import Lambda.Untyped.Scoped.Term

%default total
%access public export

isoNatUnits : Iso Nat (List ())
isoNatUnits =
  MkIso
    (\n => replicate n ())
    length
    lem1
    lem2
  where
  lem1 : (y : List ()) -> replicate (length y) () = y
  lem1 [] = Refl
  lem1 (()::xs) = cong $ lem1 xs
  lem2 : (x : Nat) -> length (replicate x ()) = x
  lem2 Z = Refl
  lem2 (S x) = cong $ lem2 x

data Term : List Ty -> Ty -> Type where
  Var : Elem a g -> Term g a
  Lam : Term (a::g) b -> Term g (a~>b)
  App : Term g (a~>b) -> Term g a -> Term g b

-- map to untyped by forgetting type indices

forget : Term g a -> TermDB.Term
forget (Var el)    = Var $ elem2Nat el
forget (Lam t)     = Lam $ forget t
forget (App t1 t2) = App (forget t1) (forget t2)

forgetSco : Term g a -> Term (length g)
forgetSco (Var el)    = Var $ elem2Fin el
forgetSco (Lam t)     = Lam $ forgetSco t
forgetSco (App t1 t2) = App (forgetSco t1) (forgetSco t2)

-- print

Show (Term g a) where
  show (Var n) = show $ elem2Nat n
  show (Lam t) = "\\" ++ show t
  show (App t u) = "(" ++ show t ++ ")(" ++ show u ++ ")"

-- test terms

TestTy : Ty
TestTy = A~>A

ResultTm : Term [] TestTy
ResultTm = Lam $ Var Here

TestTm0 : Term [] TestTy
TestTm0 = App (Lam $ Var Here) (Lam $ Var Here)

TestTm1 : Term [] TestTy
TestTm1 = App (App (Lam $ Var Here) (Lam $ Var Here)) (Lam $ Var Here)

private
test1 : forget TestTm1 = Term1
test1 = Refl

TestTm2 : Term [] TestTy
TestTm2 = App (Lam $ Var Here) (App (Lam $ Var Here) (Lam $ Var Here))

private
test2 : forget TestTm2 = Term2
test2 = Refl

-- scott?

NumTy : Ty
NumTy = A~>(A~>A)~>A

zero : Term [] NumTy
zero = Lam $ Lam $ Var $ There Here

succ : Term [] (NumTy~>A~>(NumTy~>NumTy)~>NumTy)
succ = Lam $ Lam $ Lam $ App (Var Here) (Var $ There $ There Here)

one : Term [] (A~>(NumTy~>NumTy)~>NumTy)
one = App succ zero

-- church

NumTy' : Ty
NumTy' = (A~>A)~>(A~>A)

zero' : Term [] NumTy'
zero' = Lam $ Lam $ Var Here

one' : Term [] NumTy'
one' = Lam $ Lam $ App (Var $ There Here) (Var Here)

succ' : Term [] (NumTy' ~> NumTy')
succ' = Lam $ Lam $ Lam $ App (Var $ There Here) (App (App (Var $ There $ There Here) (Var $ There Here)) (Var Here))
