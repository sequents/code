module Lambda.PCF.V.Mod.Bigstep

import Data.List
import Data.List.Quantifiers
import Lambda.PCF.V.Mod.Term

import System

%default total

mutual
  Env : List Ty -> Type
  Env = All Res

  data Res : Ty -> Type where
    RZ  : Res A
    RS  : Res A -> Res A
    RC  : Res a -> Res (C a)
    RF  : Env g -> Comp (C a::g) a -> Res (C a)
    RCl : Env g -> Comp (a::g) b -> Res (a~>b)

mutual
  Show (Res a) where
    show  RZ = "Z"
    show (RS v) = "S" ++ show v
    show (RC v) = "{" ++ show v ++ "}"
    show (RF e t) = "<" ++ assert_total (showAll e) ++ ">: " ++ show t
    show (RCl e t) = "{" ++ assert_total (showAll e) ++ "}: " ++ show t

  showAll : All Res l -> String
  showAll [] = ""
  showAll (v::vs) = show v ++ " " ++ assert_total (showAll vs)

mutual
  evalV : Val g a -> Env g -> Res a
  evalV (Var el) env = indexAll el env
  evalV  Zero    _   = RZ
  evalV (Succ v) env = RS $ evalV v env
  evalV (Lam t)  env = RCl env t
  evalV (Fix t)  env = RF env t
  evalV (Wrap t) env = RC $ evalC t env

  evalC : Comp g a -> Env g -> Res a
  evalC (V v)       env = evalV v env
  evalC (App t u)   env = case evalV t env of
    RCl env' c => assert_total $
                  evalC c (evalV u env :: env')
  evalC (If0 t u v) env = case evalV t env of
    RZ   => evalC u env
    RS r => evalC v (r :: env)
  evalC (Bnd v c)   env = case evalV v env of
                            RC r => evalC c (r :: env)
                            RF env' t => assert_total $
                                         evalC c (evalC t (RF env' t :: env') :: env)

partial
main : IO ()
main = printLn $ evalC bam []