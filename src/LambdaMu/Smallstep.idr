module LambdaMu.Smallstep

import Data.List
import Iter
import Subset
import LambdaMu.Ty
import LambdaMu.Term

%access public export
%default total

rename : Subset g d -> Term g a s -> Term d a s
rename r (Var el)     = Var $ r el
rename r (Lam t)      = Lam $ rename (ext r) t
rename r (App t u)    = App (rename r t) (rename r u)
rename r (Mu t)       = Mu $ rename r t
rename r (Named el t) = Named el (rename r t)

renameN : Subset d s -> Term g a d -> Term g a s
renameN r (Var el)     = Var el
renameN r (Lam t)      = Lam $ renameN r t
renameN r (App t u)    = App (renameN r t) (renameN r u)
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
subst s (App t u)    = App (subst s t) (subst s u)
subst s (Mu t)       = Mu $ subst (exts' s) t
subst s (Named el t) = Named el (subst s t)

subst1 : Term (b::g) a s -> Term g b s -> Term g a s
subst1 {g} {b} {s} t sub = subst {g=b::g} go t
  where
  go : Subst (b::g) g s
  go  Here      = sub
  go (There el) = Var el

-- commuting conversion / structural reduction
appN : Term g c ((a~>b)::d) -> Term g a d -> Term g c (b::d)
appN (Var e)             v = Var e
appN (Lam t)             v = Lam $ appN t (rename There v)
appN (App t u)           v = App (appN t v) (appN u v)
appN (Mu t)              v = Mu $ renameN permute $ assert_total $ appN (renameN permute t) (renameN There v)
appN (Named  Here     t) v = Named Here (App (appN t v) (renameN There v))
appN (Named (There e) t) v = Named (There e) (appN t v)

appNR : Term g c (a::d) -> Term g (a~>b) d -> Term g c (b::d)
appNR (Var e)             v = Var e
appNR (Lam t)             v = Lam $ appNR t (rename There v)
appNR (App t u)           v = App (appNR t v) (appNR u v)
appNR (Mu t)              v = Mu $ renameN permute $ assert_total $ appNR (renameN permute t) (renameN There v)
appNR (Named  Here     t) v = Named Here $ App (renameN There v) (appNR t v)
appNR (Named (There e) t) v = Named (There e) $ appNR t v

isVal : Term g a d -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

step : Term g a d -> Maybe (Term g a d)
step (App (Lam u) v) = Just $ subst1 u v
step (App (Mu u)  v) = Just $ Mu $ appN u v
step (App  t      u) = 
  if isVal t 
    then Nothing
    else [| App (step t) (pure u) |]
step (Named a (Mu u)) = Just $ renameN (contract a) u
step  _ = Nothing

stepV : Term g a d -> Maybe (Term g a d)
stepV (App (Mu u)  v    )   = Just $ Mu $ appN u v
stepV (App u      (Mu v))   = Just $ Mu $ appNR v u
stepV (App t1 t2) = 
  if isVal t1 
    then 
      if isVal t2
      then
        case t1 of
          Lam u => Just $ subst1 u t2
          _ => Nothing
      else App t1 <$> (stepV t2)           
    else [| App (stepV t1) (pure t2) |]
stepV (Named a (Mu u)) = Just $ renameN (contract a) u
stepV  _                    = Nothing

iterStep : Term g a d -> Term g a d
iterStep = iter step
