module Lambda.STLC.CK

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term
import Lambda.STLC.Smallstep

%default total
%access public export

-- left-to-right, no environment

-- evaluation contexts  
data Stack : List Ty -> Ty -> Ty -> Type where
  NS : Stack g a a
  FS : Term (a::g) b -> Stack g b c -> Stack g a c
  AS : Term g a -> Stack g b c -> Stack g (a~>b) c

record State (g : List Ty) (b : Ty) where
  constructor St 
  tm : Term g a 
  stk : Stack g a b

step : State g a -> Maybe (State g a)  
step (St (App t u)        s ) = Just $ St  t                  (AS u s)
step (St (Lam t)   (AS t1 s)) = Just $ St  t1                 (FS t s)
step (St (Lam t)   (FS t1 s)) = Just $ St (subst1 t1 (Lam t))       s
step  _                       = Nothing

runCK : Term g a -> (Nat, Maybe (State g a))
runCK t = iterCount step (St t NS)
