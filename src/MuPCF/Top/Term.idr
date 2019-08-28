module MuPCF.Top.Term

import Data.List
import LambdaMu.Ty

%access public export
%default total

mutual
  data Term : List Ty -> Ty -> List Ty -> Type where
    Var   : Elem a g -> Term g a d
    Lam   : Term (a::g) b d -> Term g (a~>b) d
    App   : Term g (a~>b) d -> Term g a d -> Term g b d
    Mu    : Cmd g (a::d) -> Term g a d
    Zero  : Term g A d
    Succ  : Term g A d -> Term g A d
    If0   : Term g A d -> Term g a d -> Term (A::g) a d -> Term g a d
    Fix   : Term (a::g) a d -> Term g a d
  
  data Cmd : List Ty -> List Ty -> Type where  
    Named : Elem a d -> Term g a d -> Cmd g d
    Top   : Term g Bot d -> Cmd g d             

fromN : Nat -> Term g A d
fromN  Z    = Zero
fromN (S n) = Succ $ fromN n

raise : Term g a (b::a::d) -> Term g b (a::d)
raise = Mu . Named (There Here)

handle : Term g (a~>b) (b::d) -> Term g b (a::b::d) -> Term g b d
handle m n = Mu $ Named Here $ App m (Mu $ Named (There Here) n)