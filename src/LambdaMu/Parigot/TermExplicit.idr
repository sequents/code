module LambdaMu.Parigot.TermExplicit

import Data.List
import Elem
import LambdaMu.Ty

%access public export
%default total

mutual
  data Term : List Ty -> Ty -> List Ty -> Type where
    Var   : Elem a g -> Term g a d
    Lam   : Term (a::g) b d -> Term g (a~>b) d
    App   : Term g (a~>b) d -> Term g a d -> Term g b d
    Mu    : Cmd g (a::d) -> Term g a d

  data Cont : List Ty -> Ty -> List Ty -> Type where
    CoVar : Elem a d -> Cont g a d

  data Cmd : List Ty -> List Ty -> Type where
    Named : Cont g a d -> Term g a d -> Cmd g d

lift : Cont g a d -> Term g (a~>Bot) d
lift (CoVar el) = Lam $ Mu $ Named (CoVar $ There el) (Var Here)

pierce : Term g (((a~>b)~>a)~>a) d
pierce = Lam $ Mu $ Named (CoVar Here) $ App (Var Here) (Lam $ Mu $ Named (CoVar $ There Here) (Var Here))

-- not closed
dne : Cont g Bot d -> Term g ((NOT (NOT a))~>a) d
dne (CoVar b) = Lam $ Mu $ Named (CoVar $ There b) $ App (Var Here) (lift $ CoVar Here)