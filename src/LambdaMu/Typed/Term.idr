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
  Mu    : Term g Bot (a::d) -> Term g a d              -- activate / catch / bottom elimination / proof by contradiction (a != Bot)
  Named : Elem a d -> Term g a d -> Term g Bot d       -- passivate / throw / bottom introduction / non-contradiction

dne : Term g (((a~>Bot)~>Bot)~>a) d
dne = Lam $ Mu $ App (Var Here) (Lam $ Named Here (Var Here))

dne' : Term g (((a~>Bot)~>Bot)~>a) d
dne' = Lam $ Mu $ App (Var Here) (Lam $ App (Var $ There Here) (Lam $ Named Here (Var $ There Here)))

contra : Term g ((a~>Bot)~>(a~>b)) (Bot::d)
contra = Lam $ Lam $ Mu $ Named (There Here) (App (Var $ There Here) (Var Here))

pierce : Term g (((a~>b)~>a)~>a) d
pierce = Lam $ Mu $ Named Here $ App (Var Here) (Lam $ Mu $ Named (There Here) (Var Here))

callcc : Term g ((a~>b)~>a) (a::d) -> Term g a d
callcc f =     Mu $ Named Here $ App f          (Lam $ Mu $ Named (There Here) (Var Here))

abort : Term g a (b::a::d) -> Term g b (a::d)
abort t = Mu $ Named (There Here) t

set : Term g a (a::d) -> Term g a d 
set t = Mu $ Named Here t

raise : Term g a (a::d) -> Term g b (a::d)
raise t = App (Lam $ Mu $ Named (There Here) (Var Here)) t

handle : Term g (a~>b) (b::d) -> Term g b (a::b::d) -> Term g b d
handle m n = Mu $ Named Here $ App m (Mu $ Named (There Here) n)

contrapos : Term g (((q~>Bot)~>(p~>Bot))~>(p~>q)) d
contrapos = Lam $ Lam $ Mu $ App (App (Var $ There Here) 
                                      (Lam $ Named Here (Var Here))) 
                                 (Var Here)
