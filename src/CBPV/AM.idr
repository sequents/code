module CBPV.AM

import Data.List
import Subset

import LJ.F.Ty
import CBPV.NJPV

%default total

data Stack : List PTy -> NTy -> NTy -> Type where
  Mt  : Stack g a a                                       -- left axiom
  Arg : ValC g a -> Stack g b c -> Stack g (a~>b) c       -- left impl
  Fun : TermC (a::g) b -> Stack g b c -> Stack g (U a) c  -- cut

record State (g : List PTy) (b : NTy) where
  constructor St
  tm : TermS g a
  stk : Stack g a b

step : State g a -> Maybe (State g a)
step (St (CoeT (Bind t u))               s ) = Just $ St t                      (Fun u s)
step (St (CoeT (Pure v))          (Fun t s)) = Just $ St (CoeT (subst1TC v t))         s
step (St (Fce (CoeV (Thunk t)))          s ) = Just $ St (CoeT t)                      s
step (St (App t u)                       s ) = Just $ St t                      (Arg u s)
step (St (CoeT (Lam t))           (Arg u s)) = Just $ St (CoeT (subst1TC u t))         s
step  _                                      = Nothing
