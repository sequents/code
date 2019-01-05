module Lambda.Untyped.SmallstepNam

import Control.Monad.State
import Lambda.Untyped.TermNam

%default total
%access public export

fresh : List Name -> Name
fresh []      = X
fresh (v::vs) = map S $ foldr max v vs

freeVars : Term -> List Name
freeVars (Var x)     = [x]
freeVars (Lam x t)   = filter (/= x) $ freeVars t
freeVars (App t1 t2) = freeVars t1 `union` freeVars t2

allVars : Term -> List Name
allVars (Var x)   = [x]
allVars (Lam _ t) = allVars t
allVars (App t1 t2) = allVars t1 `union` allVars t2

{-
boundVars : Term -> List Name
boundVars (Var x)     = []
boundVars (Lam x t)   = x :: boundVars t
boundVars (App t1 t2) = boundVars t1 `union` boundVars t2

renameVar : Name -> Name -> Term -> Term
renameVar old new (Var x)     = 
  if x == old 
    then Var new 
    else Var x
renameVar old new (App t1 t2) = App (renameVar old new t1) (renameVar old new t2)
renameVar old new (Lam x t)   = 
  if x == old 
    then Lam new (renameVar old new t) 
    else Lam x (renameVar old new t)

--           |-- term we are substituting into
--           |
--           |       |-- term we are substituting
--           |       |    
cleanVars : Term -> Term -> Term
cleanVars tm v@(Var x) = 
  let bnd = boundVars tm in
  if elem x bnd
    then Var (fresh bnd)
    else v
cleanVars tm (App t1 t2) = App (cleanVars tm t1) (cleanVars tm t2)
cleanVars tm l@(Lam x t) = 
  let 
    free = freeVars tm    
    new = fresh free
   in
  if elem x free 
    then assert_total $ cleanVars tm (renameVar x new l)
    else Lam x (cleanVars tm t)

-- [name -> sub] term
naiveSubst : Name -> Term -> Term -> Term
naiveSubst name sub (Var x) = if x == name then sub else Var x
naiveSubst name sub (Lam x t) = Lam x (naiveSubst x sub t)    
naiveSubst name sub (App t1 t2) = App (naiveSubst name sub t1) (naiveSubst name sub t2)

subst : Name -> Term -> Term -> Term
subst name sub term = 
  let sub1 = cleanVars term sub in
  naiveSubst name sub1 term
-}

subst : Name -> Term -> Term -> Term
subst x s b = sub b
  where
  sub : Term -> Term
  sub e@(Var v) = if v == x then s else e
  sub e@(Lam v t) = 
    if v == x then e else 
      let fvs = freeVars s in
      if v `elem` fvs 
        then 
          let v1 = fresh $ fvs `union` allVars b in
          Lam v1 (assert_total $ sub $ subst v (Var v1) t)
        else Lam v (sub t)
  sub (App t1 t2) = App (sub t1) (sub t2)

isVal : Term -> Bool
isVal (Lam _ _) = True
isVal (Var _)   = True
isVal  _        = False

step : Term -> Maybe Term
step (App (Lam x t) sub) = pure $ subst x sub t
step (App  t1       t2 ) = 
  if isVal t1 
    then App     t1        <$> (step t2) 
    else App <$> (step t1) <*> pure t2
step  _ = Nothing  

stepIter : Term -> Maybe Term
stepIter t with (step t)
  | Nothing = Just t
  | Just t2 = assert_total $ stepIter t2