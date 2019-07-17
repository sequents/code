module LambdaMu.Typed.MuKAM

import Data.List
import Iter
import LambdaMu.Typed.Term
import Subset

%access public export
%default total

mutual
  data CEnv : List Ty -> Type where
    NCE : CEnv []
    CCE : Clos a -> CEnv g -> CEnv (a::g)

  data SEnv : List Ty -> Type where
    NSE : SEnv []
    CSE : Stack a -> SEnv d -> SEnv (a::d)
  
  data Clos : Ty -> Type where
    Cl : Term g a d -> CEnv g -> SEnv d -> Clos a

  data Stack : Ty -> Type where
     NS : Stack a
     CS : Clos a -> Stack b -> Stack (a~>b)

findStack : Elem a d -> SEnv d -> Stack a
findStack Here      (CSE st _) = st
findStack (There e) (CSE _ se) = findStack e se 

record State where
  constructor St 
  tm : Term g a d
  сenv : CEnv g
  senv : SEnv d 
  stk : Stack a

step : State -> Maybe State
step (St (Var  Here)     (CCE (Cl t ce se) _)  _         s ) = Just $ St  t             ce         se                     s
step (St (Var (There n))           (CCE _ ce)  se        s ) = Just $ St (Var n)        ce         se                     s
step (St (Lam t)                          ce   se  (CS c s)) = Just $ St  t      (CCE c ce)        se                     s
step (St (App t u)                        ce   se        s ) = Just $ St  t             ce         se  ((Cl u ce se) `CS` s)
step (St (Mu t)                           ce   se        s ) = Just $ St  t             ce  (CSE s se)                   NS
step (St (Named n t)                      ce   se       NS ) = Just $ St  t             ce         se       (findStack n se)
step  _                                                      = Nothing

runMK : Term [] a [] -> (Nat, State)
runMK t = iterCount step $ St t NCE NSE NS
