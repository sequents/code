module LambdaMu.Term

%access public export
%default total

data Term = Var Nat 
          | Lam Term
          | App Term Term
          | Mu Term         -- naming
          | Named Nat Term  -- passification

pierce : Term 
pierce = Lam $ Mu $ Named 0 $ App (Var 0) (Lam $ Mu $ Named 1 (Var 0))

contrapos : Term
contrapos = Lam $ Lam $ Mu $ App (App (Var 1) (Lam $ Named 0 $ Var 0)) (Var 0)          