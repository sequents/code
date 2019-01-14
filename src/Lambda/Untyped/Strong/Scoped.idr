module Lambda.Untyped.Strong.Scoped

import Data.Fin
import Data.List

%default total
%access public export

data Term : Nat -> Type where
  Var : Fin n -> Term n
  Lam : Term (S n) -> Term n
  App : Term n -> Term n -> Term n

V0 : Term (S n)     
V0 = Var FZ       
                    
V1 : Term (2+n)     
V1 = Var $ FS FZ  

V2 : Term (3+n)     
V2 = Var $ FS $ FS FZ  

V3 : Term (4+n)     
V3 = Var $ FS $ FS $ FS FZ  

two : Term n
two = Lam $ Lam $ App V1 (App V1 V0)

four : Term n
four = Lam $ Lam $ App V1 (App V1 (App V1 (App V1 V0)))

plus : Term n
plus = Lam $ Lam $ Lam $ Lam $ App (App V3 V1) (App (App V2 V1) V0)

twotwo : Term Z
twotwo = App (App plus two) two

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

step : Term n -> Maybe (Term n)
step (App (Lam body) sub) = Just $ subst1 body sub
step (App  t1        t2 ) = 
  if isNeutral t1 
    then App     t1        <$> (step t2) 
    else App <$> (step t1) <*> Just t2
step (Lam t)              = Lam <$> step t
step  _ = Nothing  

stepIter : Term n -> Maybe (Term n)
stepIter t with (step t)
  | Nothing = Just t
  | Just t2 = assert_total $ stepIter t2
