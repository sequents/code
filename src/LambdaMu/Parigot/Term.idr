module LambdaMu.Parigot.Term

import Data.List
import Lambda.STLC.Ty

%access public export
%default total

mutual
  data Term : List Ty -> Ty -> List Ty -> Type where
    Var   : Elem a g -> Term g a d
    Lam   : Term (a::g) b d -> Term g (a~>b) d
    App   : Term g (a~>b) d -> Term g a d -> Term g b d
    Mu    : Cmd g (a::d) -> Term g a d
  
  data Cmd : List Ty -> List Ty -> Type where  
    Named : Elem a d -> Term g a d -> Cmd g d

lift : Elem a d -> Term g (a~>b) d   -- since we don't have `Bot`, we "implicitly" use `exfalso`
lift el = Lam $ Mu $ Named (There el) (Var Here)

pierce : Term g (((a~>b)~>a)~>a) d
pierce = Lam $ Mu $ Named Here $ App (Var Here) (Lam $ Mu $ Named (There Here) (Var Here))

-- continuations

callcc : Term g ((a~>b)~>a) (a::d) -> Term g a d
callcc f =     Mu $ Named Here $ App f          (Lam $ Mu $ Named (There Here) (Var Here))

abort : Elem a d -> Term g a (b::d) -> Term g b d
abort el = Mu . Named (There el)

set : Term g a (a::d) -> Term g a d 
set = Mu . Named Here

-- exceptions

raise : Elem a d -> Term g a d -> Term g b d
raise el = App (Lam $ Mu $ Named (There el) (Var Here))

handle : Term g (a~>b) (b::d) -> Term g b (a::b::d) -> Term g b d
handle m n = Mu $ Named Here $ App m (Mu $ Named (There Here) n)