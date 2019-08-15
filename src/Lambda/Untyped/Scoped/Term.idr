module Lambda.Untyped.Scoped.Term

import Data.Fin

%default total
%access public export

data Term : Nat -> Type where
  Var : Fin n -> Term n
  Lam : Term (S n) -> Term n
  App : Term n -> Term n -> Term n

Show (Term n) where
  show (Var f) = show $ finToNat f
  show (Lam t) = "\\" ++ show t
  show (App t u) = "(" ++ show t ++ ")(" ++ show u ++ ")"

-- convenience  

V0 : Term (S n)     
V0 = Var FZ       
                    
V1 : Term (2+n)     
V1 = Var $ FS FZ  

V2 : Term (3+n)     
V2 = Var $ FS $ FS FZ  

V3 : Term (4+n)     
V3 = Var $ FS $ FS $ FS FZ  

-- Church

two : Term n
two = Lam $ Lam $ App V1 (App V1 V0)

four : Term n
four = Lam $ Lam $ App V1 (App V1 (App V1 (App V1 V0)))

plus : Term n
plus = Lam $ Lam $ Lam $ Lam $ App (App V3 V1) (App (App V2 V1) V0)

twotwo : Term Z
twotwo = App (App plus two) two

-- Scott

zero' : Term n
zero' = Lam $ Lam V1

succ' : Term n
succ' = Lam $ Lam $ Lam $ App V0 V2

one' : Term n
one' = App succ' zero'