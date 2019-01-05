module Lambda.STLC.Smallstep

import Lambda.STLC.Term

%access public export
%default total

{-
shift : Bool -> Nat -> Nat -> Nat
shift b k arg = if arg < k then arg else if b then S arg else pred arg

-- This is cycles every term above a threshold by a given amount
-- taking into consideration how far our term is within a binding
-- tree.
--
--       - increase or decrease
--       |
--       |      - cycle threshold
--       |      |
cycle : Bool -> Nat -> Tm0 -> Tm0
cycle b k (Vr0 v)     = Vr0 $ shift b k v
cycle b k (Ap0 l1 l2) = Ap0 (cycle b k l1) (cycle b k l2)
cycle b k (Lm0 l1)    = Lm0 $ cycle b (S k) l1

mutual
  substitute : (Nat, Tm0) -> Tm0 -> Tm0
  substitute (n, sub) (Vr0 m)     = if n == m then sub else Vr0 m
  substitute (n, sub) (Lm0 t)     = Lm0 $ substitute (S n, cycleSucc sub) t
  substitute (n, sub) (Ap0 t1 t2) = Ap0 (substitute (n, sub) t1) (substitute (n, sub) t2)
  
  cycleSucc : Tm0 -> Tm0
  cycleSucc = cycle True 0

cyclePred : Tm0 -> Tm0
cyclePred = cycle False 0

--          -- term to be substituted
--          |
topSubst : Tm0 -> Tm0 -> Tm0
topSubst sub body =
  cyclePred $ substitute (0, cycleSucc sub) body

isVal : Tm0 -> Bool
isVal (Lm0 _) = True
isVal (Vr0 _) = True
isVal  _      = False

smallStep : Tm0 -> Maybe Tm0
smallStep (Ap0 (Lm0 body) sub) = pure $ topSubst sub body
smallStep (Ap0  t1        t2 ) = 
  if isVal t1 
    then Ap0     t1             <$> (smallStep t2) 
    else Ap0 <$> (smallStep t1) <*> pure t2
smallStep  _ = Nothing
  -}