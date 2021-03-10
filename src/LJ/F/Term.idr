module LJ.F.Term

import Data.List
import Subset

import LJ.F.Ty

%default total
%access public export

mutual
  -- asynchronous
  data Term : List PTy -> NTy -> Type where
    Cont : Elem (D n) g -> Stack g n m -> Term g m     -- left focus, continuation
    Foc  : Val g p -> Term g (U p)                     -- right focus, value
    Lam  : Term (p::g) n -> Term g (p~>n)              -- right implication
    Cut  : Term g n -> Stack g n m -> Term g m         -- left head cut, stack
    Let  : Val g p -> Term (p::g) n -> Term g n        -- right head cut, let

  -- left synchronous, context + stoup
  data Stack : List PTy -> NTy -> NTy -> Type where
    Nil  : UN n -> Stack g n n                         -- left axiom
    Cons : Val g p -> Stack g n m -> Stack g (p~>n) m  -- left implication
    C    : Term (p::g) m -> Stack g (U p) m            -- left blur

  -- right-synchronous
  data Val : List PTy -> PTy -> Type where
    Var : Elem p g -> Val g p                          -- right axiom
    V   : Term g n -> Val g (D n)                      -- right blur

mutual
  renameTerm : Subset g d -> Term g a -> Term d a
  renameTerm s (Cont el k) = Cont (s el) (renameStack s k)
  renameTerm s (Foc r)     = Foc $ renameVal s r
  renameTerm s (Lam t)     = Lam $ renameTerm (ext s) t
  renameTerm s (Cut t c)   = Cut (renameTerm s t) (renameStack s c)
  renameTerm s (Let r a)   = Let (renameVal s r) (renameTerm (ext s) a)

  renameStack : Subset g d -> Stack g a b -> Stack d a b
  renameStack s (Nil prf)  = Nil prf
  renameStack s (Cons t c) = Cons (renameVal s t) (renameStack s c)
  renameStack s (C a)      = C $ renameTerm (ext s) a

  renameVal : Subset g d -> Val g a -> Val d a
  renameVal s (Var el) = Var $ s el
  renameVal s (V a)    = V $ renameTerm s a
