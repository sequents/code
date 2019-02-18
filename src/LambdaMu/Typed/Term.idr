module LambdaMu.Typed.Term

import Data.List

%access public export
%default total
%hide Language.Reflection.Var

data Ty = A | Bot | Imp Ty Ty
infix 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

data Term : List Ty -> Ty -> List Ty -> Type where
  Var   : Elem a g -> Term g a d
  Lam   : Term (a::g) b d -> Term g (a~>b) d
  App   : Term g (a~>b) d -> Term g a d -> Term g b d
  Mu    : Term g Bot (a::d) -> Term g a d              -- activate
  Named : Elem a d -> Term g a d -> Term g Bot d       -- passivate

dne : Term g (((a~>Bot)~>Bot)~>a) d
dne = Lam $ Mu $ App (Var Here) (Lam $ Named Here (Var Here))
   
contra : Term g ((a~>Bot)~>(a~>b)) (Bot::d)
contra = Lam $ Lam $ Mu $ Named (There Here) (App (Var $ There Here) (Var Here))

pierce : Term g (((a~>b)~>a)~>a) d
pierce = Lam $ Mu $ Named Here $ App (Var Here) (Lam $ Mu $ Named (There Here) (Var Here))

callcc : Term g ((a~>b)~>a) (a::d) -> Term g a d
callcc f =     Mu $ Named Here $ App f          (Lam $ Mu $ Named (There Here) (Var Here))

contrapos : Term g (((q~>Bot)~>(p~>Bot))~>(p~>q)) d
contrapos = Lam $ Lam $ Mu $ App (App (Var $ There Here) 
                                      (Lam $ Named Here (Var Here))) 
                                 (Var Here)
