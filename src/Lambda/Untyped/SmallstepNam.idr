module Lambda.Untyped.SmallstepNam

import Iter
import Lambda.Untyped.TermNam

%default total
%access public export

freeVars : Term -> List Name
freeVars (Var x)     = [x]
freeVars (Lam x t)   = filter (/= x) $ freeVars t
freeVars (App t1 t2) = freeVars t1 `union` freeVars t2

allVars : Term -> List Name
allVars (Var x)     = [x]
allVars (Lam _ t)   = allVars t
allVars (App t1 t2) = allVars t1 `union` allVars t2

-- substituting `s` for variable `x` inside `b`
subst : Name -> Term -> Term -> Term
subst x s b = sub b
  where
  sub : Term -> Term
  sub e@(Var v)   = if v == x then s else e
  sub e@(Lam v t) = 
    if v == x 
      then e 
      else 
        let fvs = freeVars s in
        if v `elem` fvs 
          then 
            let 
              v1 = fresh $ fvs `union` allVars b 
              t2 = subst v (Var v1) t -- rename bound variable in body by substituting a fresh var
             in
            Lam v1 (assert_total $ sub t2) -- safe because `t2` is isomorphic to `t`, thus smaller than `Lam v t`
          else Lam v (sub t)
  sub (App t1 t2) = App (sub t1) (sub t2)

isVal : Term -> Bool
isVal (Lam _ _) = True
isVal (Var _)   = True
isVal  _        = False

-- search for a single redex and reduce it, call-by-name
step : Term -> Maybe Term
step (App (Lam x t) sub) = Just $ subst x sub t  -- beta-reduction
step (App  t1       t2 ) = 
  if isVal t1 
    then Nothing
    else App <$> (step t1) <*> Just t2
step  _                  = Nothing  

-- left-to-right call-by-value  
stepV : Term -> Maybe Term
stepV (App t1 t2) = 
  if isVal t1 
    then 
      if isVal t2
      then
        case t1 of
          Lam x t => Just $ subst x t2 t  -- beta-reduction
          _ => Nothing
      else App t1 <$> (stepV t2)           
    else App <$> (stepV t1) <*> Just t2
stepV  _          = Nothing  

-- right-to-left call-by-value  
stepVR : Term -> Maybe Term
stepVR (App t1 t2) = 
  if isVal t2 
    then 
      case t1 of
        Lam x t => Just $ subst x t2 t  -- beta-reduction
        _ => App <$> (stepVR t1) <*> Just t2
    else App     t1         <$> (stepVR t2) 
stepVR  _          = Nothing  

iterN : Term -> Term
iterN = iter step

runN : Term -> (Nat, Term)
runN = iterCount step

iterV : Term -> Term
iterV = iter stepV

runV : Term -> (Nat, Term)
runV = iterCount stepV

iterVR : Term -> Term
iterVR = iter stepVR

runVR : Term -> (Nat, Term)
runVR = iterCount stepVR
