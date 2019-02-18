module LambdaMu.Typed.MuKAM0

import Data.List
import Subset
import Iter
import LambdaMu.Typed.Term
import LambdaMu.Typed.Smallstep

%access public export
%default total

data Stack : List Ty -> Ty -> List Ty -> Type where
  NS : Stack g a d
  CS : Term g a d -> Stack g b d -> Stack g (a~>b) d

record State (g : List Ty) (d : List Ty) where
  constructor St 
  tm : Term g a d
  stk : Stack g a d

step : State g d -> Maybe (State g d)  
step (St (App t u)              s ) = Just $ St  t                       (CS u s)
step (St (Lam t)          (CS u s)) = Just $ St (subst1 t u)                   s
step (St (Mu t)           (CS u s)) = Just $ St (Mu $ appN t u)                s
step (St (Named n (Mu t))       s ) = Just $ St (renameN (contract n) t)       s
step  _                             = Nothing
