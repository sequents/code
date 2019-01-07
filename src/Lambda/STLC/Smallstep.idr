module Lambda.STLC.Smallstep

import Data.List
import Lambda.STLC.Ty
import Lambda.STLC.Term

%access public export
%default total

Subset : List Ty -> List Ty -> Type
Subset g d = {x : Ty} -> Elem x g -> Elem x d

ext : Subset g d -> Subset (b::g) (b::d)
ext _  Here      = Here
ext r (There el) = There (r el)

rename : Subset g d -> Term g a -> Term d a
rename r (Var el)    = Var $ r el
rename r (Lam t)     = Lam $ rename (ext r) t
rename r (App t1 t2) = App (rename r t1) (rename r t2)

exts : ({x : Ty} -> Elem x g -> Term d x) -> Elem a (b::g) -> Term (b::d) a
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

subst : ({x : Ty} -> Elem x g -> Term d x) -> Term g a -> Term d a
subst s (Var el)    = s el
subst s (Lam t)     = Lam $ subst (exts s) t
subst s (App t1 t2) = App (subst s t1) (subst s t2)

subst1 : Term (b::g) a -> Term g b -> Term g a 
subst1 {g} {b} t s = subst {g=b::g} go t
  where
  go : Elem x (b::g) -> Term g x
  go  Here      = s
  go (There el) = Var el

isVal : Term g a -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

step : Term g a -> Maybe (Term g a)
step (App (Lam body) sub) = Just $ subst1 body sub
step (App  t1        t2 ) = 
  if isVal t1 
    then App     t1        <$> (step t2) 
    else App <$> (step t1) <*> pure t2
step  _ = Nothing

stepIter : Term g a -> Maybe (Term g a)
stepIter t with (step t)
  | Nothing = Just t
  | Just t2 = assert_total $ stepIter t2
