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
eval (Var el)              env = indexAll el env
eval (Lam t)               env = VCl env t
eval (App {a=x} {b=y} t u) env = goF (eval t env)
  where
  goF : Val (x~>y) -> Val y
  goF (VCl env' v) = goA (eval u env)
    where
    goA : Val x -> Val y
    goA (VF env'' w) = assert_total $ goA (eval w (VF env'' w :: env''))
    goA w            = assert_total $ eval v (w :: env')
  goF (VF env' v)  = assert_total $ goF (eval v (VF env' v :: env'))
eval  Zero                 env = VZ
eval (Succ t)              env = goS (eval t env)
  where
  goS : Val A -> Val A
  goS (VF env' w) = assert_total $ goS (eval w (VF env' w :: env'))
  goS  w          = VS w
eval (If0 {a} c t f)       env = goI (eval c env)
  where
  goI : Val A -> Val a
  goI  VZ         = eval t env
  goI (VS v)      = eval f (v::env)
  goI (VF env' v) = assert_total $ goI (eval v (VF env' v :: env'))
eval (Fix t)               env = VF env t

eval0 : Term [] a -> Val a
eval0 t = eval t []
