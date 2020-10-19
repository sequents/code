module Lambda.PCF.BigstepN

import Data.List
import Data.List.Quantifiers
import Iter
import Subset

import Lambda.STLC.Ty
import Lambda.PCF.Term

%access public export
%default total

mutual
  Env : List Ty -> Type
  Env = All Val

  data Val : Ty -> Type where
    VZ  : Val A
    VS  : Val A -> Val A
    VCl : Env g -> Term g a -> Val a

-- cbv
eval : Term g a -> Env g -> Val a
eval (Var el)  env = case indexAll el env of
                       VCl env' v => assert_total $ eval v env'
                       vl => vl
eval (Lam t)   env = VCl env (Lam t)
eval (App t u) env = case eval t env of
                       VCl env' vv => case vv of
                                        Lam v => assert_total $ eval v (VCl env u :: env')
                                        _ => VCl env (App t u)
eval  Zero       env = VZ
eval (Succ t)    env = VS $ eval t env
eval (If0 {a} c t f) env = choose $ eval c env
  where
  choose : Val A -> Val a
  choose  VZ          = eval t env
  choose (VS v)       = eval f (v::env)
  choose (VCl env' v) = assert_total $ choose $ eval v env'
eval (Fix t)     env = assert_total $ eval t (VCl env (Fix t)::env)


eval0 : Term [] a -> Val a
eval0 t = eval t []