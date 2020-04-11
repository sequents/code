module LJ.T.Term

import Data.List
import Subset

import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

mutual
  -- asynchronous, cut-free (i.e. not Cut) terms are values
  data TermJ : List Ty -> Ty -> Type where
    Var : Elem a g -> Spine g a b -> TermJ g b   -- contraction / focus
    Lam : TermJ (a::g) b -> TermJ g (a~>b)       -- implication right intro
    Cut : TermJ g a -> Spine g a b -> TermJ g b  -- head cut, beta-redex / generalized application

  -- left synchronous, context + stoup
  data Spine : List Ty -> Ty -> Ty -> Type where
    Nil  : Spine g a a                                   -- axiom
    Cons : TermJ g a -> Spine g b c -> Spine g (a~>b) c  -- implication left intro

concat : Spine g a b -> Spine g b c -> Spine g a c
concat  Nil        s2 = s2
concat (Cons t s1) s2 = Cons t (concat s1 s2)

-- STLC embedding
encode : Term g a -> TermJ g a
encode (Var e)   = Var e Nil
encode (Lam t)   = Lam $ encode t
encode (App t u) = Cut (encode t) (Cons (encode u) Nil)
