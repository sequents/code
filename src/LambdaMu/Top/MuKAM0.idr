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
  Mt  : Stack g a a d
  Arg : Term g a d -> Stack g b c d -> Stack g (a~>b) c d
  MuN : Stack g a b d -> Stack g a b (a::d)

data State : List Ty -> Ty -> Type where
  St : Term g a d -> Stack g a b d -> State g b
  Rw : Term g a d -> Stack g a b d -> State g b

step : State g b -> Maybe (State g b)  
step (St (App t u)                    s ) = Just $ St  t                               (Arg u s)
step (St (Lam t)               (Arg u s)) = Just $ St (subst1 t u)                             s
step (St (Mu c)                (Arg u s)) = Just $ St (Mu $ appCmdN c u)                       s
step (St (Mu (Named n (Mu c)))        s ) = Just $ St (Mu $ renameCmdN (contract n) c)         s
step (St (Mu (Top (Mu c)))            s ) = Just $ St (Mu $ substTopCmd c)                     s
step (St (Mu (Named Here t))          s ) =   
               case renameMN contractM t of  
                 Just t =>                  Just $ St  t                                       s
                 Nothing =>                 Just $ St  t                                  (MuN s)
step (St  t                      (MuN s)) = Just $ Rw  t                                  (MuN s)
step (Rw  t                      (MuN s)) = Just $ Rw (Mu (Named Here t))                      s
step (Rw  t                           s ) = Just $ St  t                                       s
step  _                                   = Nothing

runMK0 : Term g a [] -> (Nat, State g a)
runMK0 t = iterCount step (St t Mt)