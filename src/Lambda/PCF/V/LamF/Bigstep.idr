module Lambda.PCF.V.LamF.Bigstep

import Data.List
import Data.List.Quantifiers
import Lambda.PCF.V.LamF.Term
import Lambda.STLC.Ty

import System

%default total

mutual
  Env : List Ty -> Type
  Env = All Res

  data Res : Ty -> Type where
    RZ  : Res A
    RS  : Res A -> Res A
    RCl : Env g -> Comp (a::(a~>b)::g) b -> Res (a~>b)

mutual
  Show (Res a) where
    show  RZ = "Z"
    show (RS v) = "S" ++ show v
    show (RCl e t) = "{" ++ assert_total (showAll e) ++ "}: " ++ show t

  showAll : All Res l -> String
  showAll [] = ""
  showAll (v::vs) = show v ++ " " ++ assert_total (showAll vs)

mutual
  evalV : Val g a -> Env g -> Res a
  evalV (Var el) env = indexAll el env
  evalV  Zero    _   = RZ
  evalV (Succ v) env = RS $ evalV v env
  evalV (LamF t) env = RCl env t

  evalC : Comp g a -> Env g -> Res a
  evalC (V v)       env = evalV v env
  evalC (App t u)   env = case evalC t env of
    RCl env' c => assert_total $
                  evalC c (evalC u env :: RCl env' c :: env')
  evalC (If0 t u v) env = case evalC t env of
    RZ   => evalC u env
    RS r => evalC v (r :: env)

partial
main : IO ()
main = printLn $ evalC bam []