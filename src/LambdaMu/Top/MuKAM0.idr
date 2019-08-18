module LambdaMu.MuKAM0

import Data.List
import Subset
import Iter
import LambdaMu.Ty
import LambdaMu.Top.Term
import LambdaMu.Top.Smallstep

%access public export
%default total

data Stack : List Ty -> Ty -> Ty -> List Ty -> Type where
  NS : Stack g a a d
  CS : Term g a d -> Stack g b c d -> Stack g (a~>b) c d

record State (g : List Ty) (b : Ty) (d : List Ty) where
  constructor St 
  tm : Term g a d
  stk : Stack g a b d

step : State g b d -> Maybe (State g b d)  
step (St (App t u)                  s ) = Just $ St  t                           (CS u s)
step (St (Lam t)              (CS u s)) = Just $ St (subst1 t u)                       s
step (St (Mu t)               (CS u s)) = Just $ St (Mu $ appCmdN t u)                 s
step (St (Mu (Named a (Mu u)))      s ) = Just $ St (Mu $ renameCmdN (contract a) u)   s
step  _                                 = Nothing

runMK0 : Term g a d -> (Nat, State g a d)
runMK0 t = iterCount step (St t NS)