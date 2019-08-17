module Lambda.STLC.Smallstep

import Data.List
import Iter
import Subset
import Lambda.STLC.Ty
import Lambda.STLC.Term

%access public export
%default total

rename : Subset g d -> Term g a -> Term d a
rename r (Var el)    = Var $ r el
rename r (Lam t)     = Lam $ rename (ext r) t
rename r (App t1 t2) = App (rename r t1) (rename r t2)

Subst : List Ty -> List Ty -> Type
Subst g d = {x : Ty} -> Elem x g -> Term d x

exts : Subst g d -> Subst (b::g) (b::d)
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

subst : Subst g d -> Term g a -> Term d a
subst s (Var el)    = s el
subst s (Lam t)     = Lam $ subst (exts s) t
subst s (App t1 t2) = App (subst s t1) (subst s t2)

subst1 : Term (b::g) a -> Term g b -> Term g a 
subst1 {g} {b} t s = subst {g=b::g} go t
  where
  go : Subst (b::g) g
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
    then Nothing
    else [| App (step t1) (pure t2) |]
step  _                   = Nothing

stepV : Term g a -> Maybe (Term g a)
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
stepV  _          = Nothing  

stepIter : Term g a -> Term g a
stepIter = iter step
