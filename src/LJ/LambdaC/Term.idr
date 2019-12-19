module LJ.LambdaC.Term

import Data.List
--import Iter
import Subset

import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

-- Moggi's lambda-C

mutual
  data Val : List Ty -> Ty -> Type where
    Var : Elem a g -> Val g a
    Lam : Tm (a::g) b -> Val g (a~>b)

  data Tm : List Ty -> Ty -> Type where
    V   : Val g a -> Tm g a
    App : Tm g (a~>b) -> Tm g a -> Tm g b
    Let : Tm g a -> Tm (a::g) b -> Tm g b

-- structural rules

mutual
  renameVal : Subset g d -> Val g a -> Val d a
  renameVal sub (Var el) = Var $ sub el
  renameVal sub (Lam t)  = Lam $ renameTm (ext sub) t

  renameTm : Subset g d -> Tm g a -> Tm d a
  renameTm sub (V v)     = V $ renameVal sub v
  renameTm sub (App t u) = App (renameTm sub t) (renameTm sub u)
  renameTm sub (Let m n) = Let (renameTm sub m) (renameTm (ext sub) n)

shiftVal : {auto is : IsSubset g d} -> Val g a -> Val d a
shiftVal {is} = renameVal (shift is)

shiftTm : {auto is : IsSubset g d} -> Tm g a -> Tm d a
shiftTm {is} = renameTm (shift is)

-- STLC conversion

encodeLC : Term g a -> Tm g a
encodeLC (Var e)     = V $ Var e
encodeLC (Lam t)     = V $ Lam $ encodeLC t
encodeLC (App t1 t2) = App (encodeLC t1) (encodeLC t2)

mutual
  forgetVal : Val g a -> Term g a
  forgetVal (Var el) = Var el
  forgetVal (Lam t)  = Lam $ forgetTm t

  forgetTm : Tm g a -> Term g a
  forgetTm (V v)     = forgetVal v
  forgetTm (App m n) = App (forgetTm m) (forgetTm n)
  forgetTm (Let n m) = App (Lam $ forgetTm m) (forgetTm n)
