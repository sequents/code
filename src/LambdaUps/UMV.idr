module LambdaUps.UMV

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term
import LambdaUps.Term

%access public export
%default total

data Stack : List Ty -> Ty -> Ty -> Type where
  NS : Stack g a a
  AS : TermU g a -> Stack g b c -> Stack g (a~>b) c
  FS : TermU (a::g) b -> Stack g b c -> Stack g a c

record State (b : Ty) where
  constructor St
  tm : TermU g a
  stk : Stack g a b

step : State b -> Maybe (State b)
step (St (App t u)                              s ) = Just $ St  t                            (AS u s)
step (St (Lam t)                          (AS u s)) = Just $ St  u                            (FS t s)
step (St  t                               (FS u s)) = Just $ St (Let u (Slash t))                   s
step (St (Let (App t u)         sb      )       s ) = Just $ St (App (Let t sb) (Let u sb))         s
step (St (Let (Lam t)           sb      )       s ) = Just $ St (Lam (Let t (Lift sb)))             s
step (St (Let (Var  Here)      (Slash t))       s ) = Just $ St  t                                  s
step (St (Let (Var (There el)) (Slash _))       s ) = Just $ St (Var el)                            s
step (St (Let (Var  Here)      (Lift _) )       s ) = Just $ St (Var Here)                          s
step (St (Let (Var (There el)) (Lift sb))       s ) = Just $ St (Let (Let (Var el) sb) Shift)       s
step (St (Let (Var  el)         Shift   )       s ) = Just $ St (Var (There el))                    s
step  _                                             = Nothing

stepIter : Term [] a -> (Nat, State a)
stepIter t = iterCount step (St (encode t) NS)
