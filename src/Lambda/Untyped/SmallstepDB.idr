module Lambda.Untyped.SmallstepDB

import Util
import Lambda.Untyped.TermDB

%access public export
%default total

shift : Bool -> Nat -> Nat -> Nat
shift b k arg = if arg < k then arg else if b then S arg else pred arg

-- This cycles every term above a threshold by a given amount
-- taking into consideration how far our term is within a binding
-- tree.
--
--       - increase or decrease
--       |
--       |      - cycle threshold
--       |      |
cycle : Bool -> Nat -> Term -> Term
cycle b k (Var v)     = Var $ shift b k v
cycle b k (App l1 l2) = App (cycle b k l1) (cycle b k l2)
cycle b k (Lam l1)    = Lam $ cycle b (S k) l1

cycleSucc : Term -> Term
cycleSucc = cycle True 0

cyclePred : Term -> Term
cyclePred = cycle False 0

substitute : (Nat, Term) -> Term -> Term
substitute (n, sub) (Var m)     = if n == m then sub else Var m
substitute (n, sub) (Lam t)     = Lam $ substitute (S n, cycleSucc sub) t
substitute (n, sub) (App t1 t2) = App (substitute (n, sub) t1) (substitute (n, sub) t2)

topSubst : Term -> Term -> Term
topSubst sub body =
  cyclePred $ substitute (0, cycleSucc sub) body

isVal : Term -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

-- call-by-name
step : Term -> Maybe Term
step (App (Lam body) sub) = Just $ topSubst sub body
step (App  t1        t2 ) = 
  if isVal t1 
    then App     t1        <$> (step t2) 
    else App <$> (step t1) <*> Just t2
step  _ = Nothing

-- call-by-value
stepV : Term -> Maybe Term
stepV (App t1 t2) = 
  if isVal t2 
    then 
      case t1 of
        Lam t => Just $ topSubst t2 t  -- beta-reduction
        _ => App <$> (stepV t1) <*> Just t2
    else App     t1         <$> (stepV t2) 
stepV  _          = Nothing  

iterN : Term -> Maybe Term
iterN = iter step

countN : Term -> (Nat, Maybe Term)
countN = iterCount step

iterV : Term -> Maybe Term
iterV = iter stepV

countV : Term -> (Nat, Maybe Term)
countV = iterCount stepV
