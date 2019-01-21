module LambdaMu.Typed.Smallstep

import Data.List
import Iter
import LambdaMu.Typed.Term

%access public export
%default total

Subset : List Ty -> List Ty -> Type
Subset g d = {x : Ty} -> Elem x g -> Elem x d

ext : Subset g d -> Subset (b::g) (b::d)
ext _  Here      = Here
ext r (There el) = There (r el)

contract : Elem x d -> Subset (x::d) d
contract el  Here     = el
contract el (There s) = s

permute : Subset (a::b::g) (b::a::g)
permute  Here              = There Here
permute (There  Here     ) = Here
permute (There (There el)) = There (There el)

rename : Subset g d -> Term g a s -> Term d a s
rename r (Var el)     = Var $ r el
rename r (Lam t)      = Lam $ rename (ext r) t
rename r (App t1 t2)  = App (rename r t1) (rename r t2)
rename r (Mu t)       = Mu $ rename r t
rename r (Named el t) = Named el (rename r t)

renameN : Subset d s -> Term g a d -> Term g a s
renameN r (Var el)     = Var el
renameN r (Lam t)      = Lam $ renameN r t
renameN r (App t1 t2)  = App (renameN r t1) (renameN r t2)
renameN r (Mu t)       = Mu $ renameN (ext r) t
renameN r (Named el t) = Named (r el) (renameN r t)

Subst : List Ty -> List Ty -> List Ty -> Type
Subst g d s = {x : Ty} -> Elem x g -> Term d x s

exts : Subst g d s -> Subst (b::g) (b::d) s
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

exts' : Subst g d s -> Subst g d (a::s)
exts' s = renameN There . s

subst : Subst g d s -> Term g a s -> Term d a s
subst s (Var el)     = s el
subst s (Lam t)      = Lam $ subst (exts s) t
subst s (App t1 t2)  = App (subst s t1) (subst s t2)
subst s (Mu t)       = Mu $ subst (exts' s) t
subst s (Named el t) = Named el (subst s t)

subst1 : Term (b::g) a s -> Term g b s -> Term g a s
subst1 {g} {b} {s} t sub = subst {g=b::g} go t
  where
  go : Subst (b::g) g s
  go  Here      = sub
  go (There el) = Var el

appN : Term g c ((a~>b)::d) -> Term g a d -> Term g c (b::d)
appN (Var e)             v = Var e
appN (Lam t)             v = Lam $ appN t (rename There v)
appN (App t u)           v = App (appN t v) (appN u v)
appN (Mu t)              v = Mu $ renameN permute $ assert_total $ appN (renameN permute t) (renameN There v)
appN (Named  Here     t) v = Named Here (App (appN t v) (renameN There v))
appN (Named (There e) t) v = Named (There e) (appN t v)

isVal : Term g a d -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

step : Term g a d -> Maybe (Term g a d)
step (App (Lam u) v) = Just $ subst1 u v
step (App (Mu u)  v) = Just $ Mu $ appN u v
step (App  t1        t2 ) = 
  if isVal t1 
    then App     t1        <$> (step t2) 
    else App <$> (step t1) <*> pure t2
step (Named a (Mu u)) = Just $ renameN (contract a) u
step  _ = Nothing
  
iterStep : Term g a d -> Maybe (Term g a d)
iterStep = iter step