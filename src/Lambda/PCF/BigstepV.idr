module Lambda.PCF.BigstepV

import Data.List
import Data.List.Quantifiers
import Iter
import Subset

import Lambda.STLC.Ty
import Lambda.PCF.Term

%access public export
%default total

-- call-by-value

mutual
  Env : List Ty -> Type
  Env = All Val

  data Val : Ty -> Type where
    VZ  : Val A
    VS  : Val A -> Val A
    VCl : Env g -> Term (a::g) b -> Val (a~>b)
    VF  : Env g -> Term (a::g) a -> Val a

eval : Term g a -> Env g -> Val a
eval (Var el)        env = indexAll el env
eval (Lam t)         env = VCl env t
eval (App {a=x} t u) env = go (eval t env)
  where
  go : Val (x~>a) -> Val a
  go (VCl env' v) = assert_total $ eval v (eval u env::env')
  go (VF env' v)  = assert_total $ go (eval v (VF env' v :: env'))
eval  Zero           env = VZ
eval (Succ t)        env = VS $ eval t env
eval (If0 {a} c t f) env = go (eval c env)
  where
  go : Val A -> Val a
  go  VZ         = eval t env
  go (VS v)      = eval f (v::env)
  go (VF env' v) = assert_total $ go (eval v (VF env' v :: env'))
eval (Fix t)         env = VF env t

eval0 : Term [] a -> Val a
eval0 t = eval t []
