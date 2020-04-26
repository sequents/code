module LJ.T.PCF.Term

import Data.List
import Elem
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

mutual
  showTerm : TermJ g a -> String
  showTerm (Var n k)   = "(" ++ show (elem2Nat n) ++ " " ++ showSpine k ++ ")"
  showTerm (Lam t)     = "\\." ++ showTerm t
  showTerm (Cut t k)   = "<" ++ showTerm t ++ "|" ++ showSpine k ++ ">"
  showTerm  Zero       = "Z"
  showTerm (Succ n)    = "S" ++ showTerm n
  showTerm (Fix t)     = "FIX." ++ showTerm t

  showSpine : Spine g a b -> String
  showSpine k = "[" ++ concat (intersperse "," (reverse $ go k [])) ++ "]"
    where
    go : Spine g a b -> List String -> List String
    go  Nil        s = s
    go (Cons t k)  s = showTerm t :: go k s
    go (Tst t f k) s = ("TST(" ++ showTerm t ++ ") ELSE (" ++ showTerm f ++ ")") :: go k s
    go (Inc k)     s = "$" :: go k s

Show (TermJ g a) where
  show = showTerm

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
