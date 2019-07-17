module LambdaMu.Term

%access public export
%default total

data Term = Var Nat 
          | Lam Term
          | App Term Term
          | Mu Term         -- activation 
          | Named Nat Term  -- passification

dne : Term
dne = Lam $ Mu $ App (Var 0) (Lam $ Named 0 (Var 0))

dne' : Term
dne' = Lam $ Mu $ App (Var 0) (Lam $ App (Var 1) (Lam $ Named 0 (Var 1)))

contra : Term
contra = Lam $ Lam $ Mu $ Named 1 (App (Var 1) (Var 0))

pierce : Term 
pierce = Lam $ Mu $ Named 0 $ App (Var 0) (Lam $ Mu $ Named 1 (Var 0))

callcc : Term -> Term
callcc f =     Mu $ Named 0 $ App f       (Lam $ Mu $ Named 1 (Var 0))

abort : Term -> Term 
abort = Mu . Named 1

set : Term -> Term 
set = Mu . Named 0

raise : Term -> Term 
raise = App . Lam $ Mu $ Named 1 (Var 0)

handle : Term -> Term -> Term
handle m n = Mu $ Named 0 $ App m (Mu $ Named 1 n)

contrapos : Term
contrapos = Lam $ Lam $ Mu $ App (App (Var 1) (Lam $ Named 0 $ Var 0)) (Var 0)          