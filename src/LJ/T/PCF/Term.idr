module LJ.T.PCF.Term

import Data.List
import Subset

import Lambda.STLC.Ty
import Lambda.PCF.Term

%default total
%access public export

mutual
  -- asynchronous
  data TermJ : List Ty -> Ty -> Type where
    Var  : Elem a g -> Spine g a b -> TermJ g b   -- contraction / focus
    Lam  : TermJ (a::g) b -> TermJ g (a~>b)       -- implication right intro
    Cut  : TermJ g a -> Spine g a b -> TermJ g b  -- head cut, beta-redex / generalized application
    Zero : TermJ g A
    Succ : TermJ g A -> TermJ g A
    Fix  : TermJ (a::g) a -> TermJ g a

  -- left synchronous, context + stoup
  data Spine : List Ty -> Ty -> Ty -> Type where
    Nil  : Spine g a a                                   -- axiom
    Cons : TermJ g a -> Spine g b c -> Spine g (a~>b) c  -- implication left intro
    Tst  : TermJ g a -> TermJ (A::g) a -> Spine g a b -> Spine g A b
    Inc  : Spine g A b -> Spine g A b

concat : Spine g a b -> Spine g b c -> Spine g a c
concat  Nil         s2 = s2
concat (Cons t s1)  s2 = Cons t (concat s1 s2)
concat (Tst t f s1) s2 = Tst t f (concat s1 s2)
concat (Inc s1)     s2 = Inc $ concat s1 s2

-- PCF embedding
encode : Term g a -> TermJ g a
encode (Var e)     = Var e Nil
encode (Lam t)     = Lam $ encode t
encode (App t u)   = Cut (encode t) (Cons (encode u) Nil)
encode  Zero       = Zero
encode (Succ t)    = Succ $ encode t
encode (If0 b t f) = Cut (encode b) (Tst (encode t) (encode f) Nil)
encode (Fix f)     = Fix $ encode f
