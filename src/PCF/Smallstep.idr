module PCF.Smallstep

import Data.List
import Iter
import Subset
import Lambda.STLC.Ty
import PCF.Term

%access public export
%default total

rename : Subset g d -> Term g a -> Term d a
rename r (Var el)    = Var $ r el
rename r (Lam t)     = Lam $ rename (ext r) t
rename r (App t1 t2) = App (rename r t1) (rename r t2)
rename r  Zero       = Zero
rename r (Succ n)    = Succ $ rename r n
rename r (If0 p t f) = If0 (rename r p) (rename r t) (rename (ext r) f)
rename r (Fix f)     = Fix $ rename (ext r) f

Subst : List Ty -> List Ty -> Type
Subst g d = {x : Ty} -> Elem x g -> Term d x

exts : Subst g d -> Subst (b::g) (b::d)
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

subst : Subst g d -> Term g a -> Term d a
subst s (Var el)    = s el
subst s (Lam t)     = Lam $ subst (exts s) t
subst s (App t1 t2) = App (subst s t1) (subst s t2)
subst s  Zero       = Zero
subst s (Succ n)    = Succ $ subst s n
subst s (If0 p t f) = If0 (subst s p) (subst s t) (subst (exts s) f)
subst s (Fix f)     = Fix $ subst (exts s) f

subst1 : Term (b::g) a -> Term g b -> Term g a 
subst1 {g} {b} t s = subst {g=b::g} go t
  where
  go : Subst (b::g) g
  go  Here      = s
  go (There el) = Var el

isVal : Term g a -> Bool
isVal (Lam _)  = True
isVal (Var _)  = True
isVal  Zero    = True
isVal (Succ n) = isVal n
isVal  _       = False  

step : Term g a -> Maybe (Term g a)
step (App (Lam body) sub) = Just $ subst1 body sub
step (App  t1        t2 ) = 
  if isVal t1 
    then App     t1        <$> (step t2) 
    else App <$> (step t1) <*> pure t2
step (Succ m)             = Succ <$> step m
step (If0 Zero t f)       = Just t
step (If0 (Succ n) t f)   = Just $ subst1 f n
step (If0 p t f)          = (\q => If0 q t f) <$> step p
step (Fix f)              = Just $ subst1 f (Fix f)
step  _                   = Nothing

stepIter : Term g a -> (Nat, Term g a)
stepIter = iterCount step
