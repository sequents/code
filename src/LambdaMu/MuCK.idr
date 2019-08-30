module LambdaMu.MuCK

import Data.List
import Iter
import Subset
import LambdaMu.Ty
import LambdaMu.Term
import LambdaMu.Smallstep

%default total
%access public export

data Stack : List Ty -> Ty -> Ty -> List Ty -> Type where
  Mt : Stack g a a d
  Arg : Term g a d -> Stack g b c d -> Stack g (a~>b) c d
  Fun : Term (a::g) b d -> Stack g b c d -> Stack g a c d
  Con : Term g Bot ((a~>b)::d) -> Stack g b c d -> Stack g a c d
  MuN : Stack g a b d -> Stack g a b (a::d)

data State : List Ty -> Ty -> Type where
  St : Term g a d -> Stack g a b d -> State g b
  Rw : Term g a d -> Stack g a b d -> State g b

step : State g a -> Maybe (State g a)
step (St (App t u)                          s ) = Just $ St  t                            (Arg u s)
step (St (Lam t)                (Arg  u     s)) = Just $ St  u                            (Fun t s)
step (St (Mu t)                 (Arg  u     s)) = Just $ St  u                            (Con t s)
step (St (Lam t)                (Fun  u     s)) = Just $ St (subst1 u (Lam t))                   s
step (St (Lam t)                (Con  u     s)) = Just $ St (Mu $ appN u (Lam t))                s
step (St  t                     (Arg (Mu u) s)) = Just $ St (Mu $ appNR u t)                     s
step (St (Mu (Named n (Mu t)))              s ) = Just $ St (Mu $ renameN (contract n) t)        s
step (St (Mu (Named Here t))                s ) =
                     case renameMN contractM t of
                       Just t =>                  Just $ St  t                                   s
                       Nothing =>                 Just $ St  t                              (MuN s)
step (St  t                            (MuN s)) = Just $ Rw  t                              (MuN s)
step (Rw  t                            (MuN s)) = Just $ Rw (Mu (Named Here t))                  s
step (Rw  t                                 s ) = Just $ St  t                                   s
step  _                                         = Nothing

runCK : Term g a [] -> (Nat, State g a)
runCK t = iterCount step (St t Mt)
