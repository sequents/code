module Lambda.STLC.BigstepV

import Data.List
import Data.List.Quantifiers
import Iter
import Subset

import Lambda.STLC.Ty
import Lambda.STLC.Term

%access public export
%default total

mutual
  Env : List Ty -> Type
  Env = All Val

  data Val : Ty -> Type where
    VCl : Env g -> Term (a::g) b -> Val (a~>b)

-- cbv
eval : Term g a -> Env g -> Val a
eval (Var el)  env = indexAll el env
eval (Lam t)   env = VCl env t
eval (App t u) env with (eval t env)
  | VCl env' v = assert_total $ eval v (eval u env :: env')

eval0 : Term [] a -> Val a
eval0 t = eval t []