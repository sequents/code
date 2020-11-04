module Lambda.STLC.BigstepN

import Data.List
import Data.List.Quantifiers
import Iter
import Subset

import Lambda.STLC.Ty
import Lambda.STLC.Term

%access public export
%default total

-- call-by-name

mutual
  Env : List Ty -> Type
  Env = All Val

  data Val : Ty -> Type where
    VCl : Env g -> Term g a -> Val a

eval : Term g a -> Env g -> Val a
eval (Var el)  env = case indexAll el env of
                       VCl env' v => assert_total $ eval v env'
eval (Lam t)   env = VCl env (Lam t)
eval (App t u) env = case eval t env of
                       VCl env' v' =>
                         case v' of
                           Lam v => assert_total $ eval v (VCl env u :: env')
                           _ => VCl env (App t u)

eval0 : Term [] a -> Val a
eval0 t = eval t []
