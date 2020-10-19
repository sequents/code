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

toNV : Val A -> Nat
toNV  VZ    = Z
toNV (VS v) = S $ toNV v

mutual
  Show (Val a) where
    show  VZ = "Z"
    show (VS v) = "S" ++ show v
    show (VCl e t) = "{" ++ showAll e ++ "}: " ++ show t

  showAll : All Val l -> String
  showAll [] = ""
  showAll (v::vs) = show v ++ " " ++ showAll vs

eval : Term g a -> Env g -> Val a
eval (Var el)    env = indexAll el env
eval (Lam t)     env = VCl env t
eval (App t u)   env = case eval t env of
  VCl env' v => let w = eval u env in
                assert_total $ eval v (w::env')
eval  Zero       env = VZ
eval (Succ t)    env = VS $ eval t env
eval (If0 c t f) env = case eval c env of
  VZ   => eval t env
  VS v => eval f (v::env)
eval (Fix t)     env = assert_total $ eval t (eval (Fix t) env::env)

eval0 : Term [] a -> Val a
eval0 t = eval t []