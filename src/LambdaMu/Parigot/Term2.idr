module LambdaMu.Parigot.Term2

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
  
  data Cmd : List Ty -> List Ty -> Type where  
    Named : Elem a d -> Term g a d -> Cmd g d

lift : Elem a d -> Term g (a~>Bot) d 
lift el = Lam $ Mu $ Named (There el) (Var Here)

pierce : Term g (((a~>b)~>a)~>a) d
pierce = Lam $ Mu $ Named Here $ App (Var Here) (Lam $ Mu $ Named (There Here) (Var Here))

-- not closed
dne : Elem Bot d -> Term g ((NOT (NOT a))~>a) d
dne b = Lam $ Mu $ Named (There b) $ App (Var Here) (lift Here)