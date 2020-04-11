module LJ.T.ES.Term

import Data.List
import Subset

import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

mutual
  -- asynchronous, cut-free (i.e. not Cut/Sub) terms are values
  data TermJ : List Ty -> Ty -> Type where
    Var : Elem a g -> Spine g a b -> TermJ g b      -- contraction / focus
    Lam : TermJ (a::g) b -> TermJ g (a~>b)          -- implication right intro
    Cut : TermJ g a -> Spine g a b -> TermJ g b     -- head cut, beta-redex / generalized application
    Sub : TermJ g a -> TermJ (a::g) b -> TermJ g b  -- mid cut, term explicit substitution

  -- left synchronous, context + stoup
  data Spine : List Ty -> Ty -> Ty -> Type where
    Nil  : Spine g a a                                   -- axiom
    Cons : TermJ g a -> Spine g b c -> Spine g (a~>b) c  -- implication left intro
    Cat  : Spine g a b -> Spine g b c -> Spine g a c     -- focused head cut, concatenating contexts
    SubL : TermJ g a -> Spine (a::g) b c -> Spine g b c  -- focused mid cut, list explicit substitution

-- STLC embedding
encode : Term g a -> TermJ g a
encode (Var e)   = Var e Nil
encode (Lam t)   = Lam $ encode t
encode (App t u) = Cut (encode t) (Cons (encode u) Nil)
