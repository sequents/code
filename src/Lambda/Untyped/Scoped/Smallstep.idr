module Lambda.Untyped.Scoped.Smallstep

import Data.Fin
import Iter
import Lambda.Untyped.Scoped.Term

%default total
%access public export

Ren : Nat -> Nat -> Type
Ren n m = Fin n -> Fin m

ext : Ren n m -> Ren (S n) (S m)
ext s  FZ    = FZ
ext s (FS x) = FS (s x)

rename : Ren n m -> Term n -> Term m
rename r (Var f)     = Var (r f)
rename r (Lam t)     = Lam $ rename (ext r) t
rename r (App t1 t2) = App (rename r t1) (rename r t2)

Sub : Nat -> Nat -> Type
Sub n m = Fin n -> Term m

exts : Sub n m -> Sub (S n) (S m)
exts s  FZ    = Var FZ
exts s (FS f) = rename FS (s f)

subst : Sub n m -> Term n -> Term m
subst s (Var f)     = s f
subst s (Lam t)     = Lam $ subst (exts s) t
subst s (App t1 t2) = App (subst s t1) (subst s t2)

subst1 : Term (S n) -> Term n -> Term n
subst1 {n} b s = subst {n=S n} go b
  where 
  go : Sub (S n) n
  go  FZ    = s
  go (FS f) = Var f

mutual  
  isNeutral : Term n -> Bool
  isNeutral (Var _)   = True
  isNeutral (App l m) = isNeutral l && isNormal m
  isNeutral  _        = False
  
  isNormal : Term n -> Bool
  isNormal (Lam t) = isNormal t
  isNormal  n      = isNeutral n

stepStr : Term n -> Maybe (Term n)
stepStr (App (Lam body) sub) = Just $ subst1 body sub
stepStr (App  t1        t2 ) = 
  if isNeutral t1 
    then App     t1           <$> (stepStr t2) 
    else App <$> (stepStr t1) <*> Just t2
stepStr (Lam t)              = Lam <$> stepStr t
stepStr  _                   = Nothing  

iterStr : Term n -> Maybe (Term n)
iterStr = iter stepStr