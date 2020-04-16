module LambdaUps.Term

import Lambda.STLC.Ty
import Lambda.STLC.Term
import Data.List

%access public export
%default total

mutual
  data TermU : List Ty -> Ty -> Type where
    Var : Elem a g -> TermU g a
    Lam : TermU (a::g) b -> TermU g (a~>b)
    App : TermU g (a~>b) -> TermU g a -> TermU g b
    Let : TermU g a -> Subs d g -> TermU d a

  data Subs : List Ty -> List Ty -> Type where
    Lift  : Subs g d -> Subs (a::g) (a::d)
    Slash : TermU g a -> Subs g (a::g)
    Shift : Subs (a::g) g

encode : Term g a -> TermU g a
encode (Var el)  = Var el
encode (Lam t)   = Lam $ encode t
encode (App t u) = App (encode t) (encode u)