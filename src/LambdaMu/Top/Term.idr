module LambdaMu.Top.Term

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
    Top : Term g Bot d -> Cmd g d

lift : Elem a d -> Term g (NOT a) d
lift el = Lam $ Mu $ Named (There el) (Var Here)

exfalso : Term g (Bot ~> a) d
exfalso = Lam $ Mu $ Top $ Var Here

orL : Term g (a ~> OR a b) d
orL = Lam $ Lam $ Mu $ Top $ App (Var Here) (Var $ There Here)

orR : Term g (b ~> OR a b) d
orR = Lam $ Lam $ Var $ There Here

orElim : Term g ((a ~> c) ~> (b ~> c) ~> OR a b ~> c) d
orElim = Lam $ Lam $ Lam $ Mu $ Named Here $ 
           App (Var $ There $ There Here) 
               (Mu $ Named (There Here) $ 
                  App (Var $ There Here) 
                      (App (Var Here) (lift Here)))

pair : Term g (a ~> b ~> AND a b) d
pair = Lam $ Lam $ Lam $ App (App (Var Here) 
                                  (Var $ There $ There Here)) 
                             (Var $ There Here)

andFst : Term g (AND a b ~> a) d
andFst = Lam $ Mu $ Top $ App (Var Here) 
                              (Lam $ Lam $ Mu $ Named (There Here) (Var $ There Here))

andSnd : Term g (AND a b ~> b) d
andSnd = Lam $ Mu $ Top $ App (Var Here) 
                              (Lam $ lift Here)

noncontradiction : Term g (NOT (AND (NOT a) a)) d 
noncontradiction = Lam $ App (Var Here) (Lam $ Var Here)

dne : Term g ((NOT (NOT a))~>a) d
dne = Lam $ Mu $ Top $ App (Var Here) (lift Here)

lem : Term g (OR (NOT a) a) d
lem = dne

contrapos : Term g (((NOT q)~>(NOT p))~>(p~>q)) d
contrapos = Lam $ Lam $ Mu $ Top $ App (App (Var $ There Here) 
                                            (Lam $ Mu $ Named (There Here) (Var Here)))
                                       (Var Here) 

pierce : Term g (((a~>b)~>a)~>a) d
pierce = Lam $ Mu $ Named Here $ App (Var Here) (Lam $ Mu $ Named (There Here) (Var Here))

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