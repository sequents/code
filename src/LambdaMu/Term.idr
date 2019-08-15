module LambdaMu.Term

import Data.List
import Elem
import LambdaMu.Ty

%access public export
%default total
%hide Language.Reflection.Var

data Term : List Ty -> Ty -> List Ty -> Type where
  Var   : Elem a g -> Term g a d
  Lam   : Term (a::g) b d -> Term g (a~>b) d
  App   : Term g (a~>b) d -> Term g a d -> Term g b d
  Mu    : Term g Bot (a::d) -> Term g a d              -- activate / catch / bottom elimination / proof by contradiction (a != Bot)
  Named : Elem a d -> Term g a d -> Term g Bot d       -- passivate / throw / bottom introduction / non-contradiction

Show (Term g a d) where
  show (Var n) = show $ elem2Nat n
  show (Lam t) = "\\" ++ show t
  show (App t u) = "(" ++ show t ++ ")(" ++ show u ++ ")"
  show (Mu t) = "MU" ++ show t
  show (Named n t) = "[" ++ show (elem2Nat n) ++ "]" ++ show t

lift : Elem a d -> Term g (NOT a) d
lift el = Lam $ Named el (Var Here)

exfalso : Term g (Bot ~> a) d
exfalso = Lam $ Mu $ Var Here

orL : Term g (a ~> OR a b) d
orL = Lam $ Lam $ Mu $ App (Var Here) (Var $ There Here)

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
andFst = Lam $ Mu $ App (Var Here) 
                        (Lam $ Lam $ Named Here (Var $ There Here))

andSnd : Term g (AND a b ~> b) d
andSnd = Lam $ Mu $ App (Var Here)
                        (Lam $ lift Here)

noncontradiction : Term g (NOT (AND (NOT a) a)) d 
noncontradiction = Lam $ App (Var Here) (Lam $ Var Here)

dne : Term g ((NOT (NOT a))~>a) d
dne = Lam $ Mu $ App (Var Here) (lift Here)

dne' : Term g ((NOT (NOT a))~>a) d
dne' = Lam $ Mu $ App (Var Here) 
                      (Lam $ App (Var $ There Here) 
                                 (Lam $ Named Here (Var $ There Here)))

lem : Term g (OR (NOT a) a) d
lem = dne

contra : Term g (NOT a ~>(a~>b)) (Bot::d)
contra = Lam $ Lam $ Mu $ Named (There Here) (App (Var $ There Here) (Var Here))

contrapos : Term g (((NOT q)~>(NOT p))~>(p~>q)) d
contrapos = Lam $ Lam $ Mu $ App (App (Var $ There Here) 
                                      (Lam $ Named Here (Var Here))) 
                                 (Var Here)

pierce : Term g (((a~>b)~>a)~>a) d
pierce = Lam $ Mu $ Named Here $ App (Var Here) (Lam $ Mu $ Named (There Here) (Var Here))

-- continuations

-- a form of `pierce` above
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