module Lambda.Untyped.SmallstepNam

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

-- substituting `s` for variable `x` inside `b`
subst : Name -> Term -> Term -> Term
subst x s b = sub b
  where
  sub : Term -> Term
  sub e@(Var v) = if v == x then s else e
  sub e@(Lam v t) = 
    if v == x 
      then e 
      else 
        let fvs = freeVars s in
        if v `elem` fvs 
          then 
            let 
              v1 = fresh $ fvs `union` allVars b 
              t2 = subst v (Var v1) t -- rename bound variable in body
             in
            Lam v1 (assert_total $ sub t2) -- safe because `t2` is isomorphic to `t`, thus smaller than `Lam v t`
          else Lam v (sub t)
  sub (App t1 t2) = App (sub t1) (sub t2)

isVal : Term -> Bool
isVal (Lam _ _) = True
isVal (Var _)   = True
isVal  _        = False

step : Term -> Maybe Term
step (App (Lam x t) sub) = Just $ subst x sub t
step (App  t1       t2 ) = 
  if isVal t1 
    then App     t1        <$> (step t2) 
    else App <$> (step t1) <*> Just t2
step  _                  = Nothing  

stepIter : Term -> Maybe Term
stepIter t with (step t)
  | Nothing = Just t
  | Just t2 = assert_total $ stepIter t2
