module LambdaMu.MuKAM

import Data.List
import Iter
import LambdaMu.Typed.Term
import Subset

%access public export
%default total

mutual
  data CEnv : List Ty -> Ty -> Type where
    NCE : CEnv [] c
    CCE : Clos a c -> CEnv g c -> CEnv (a::g) c

  data SEnv : List Ty -> Ty -> Type where
    NSE : SEnv [] c
    CSE : Stack a c -> SEnv d c -> SEnv (a::d) c
  
  data Clos : Ty -> Ty -> Type where
    Cl : Term g a d -> CEnv g c -> SEnv d c -> Clos a c

  data Stack : Ty -> Ty -> Type where
    NS : Stack a a
    ES : Stack Bot a
    CS : Clos a c -> Stack b c -> Stack (a~>b) c

findStack : Elem a d -> SEnv d c -> Stack a c
findStack  Here     (CSE st _) = st
findStack (There e) (CSE _ se) = findStack e se 

record State (t : Ty) where
  constructor St 
  tm : Term g a d
  сenv : CEnv g t
  senv : SEnv d t
  stk : Stack a t

step : State t -> Maybe (State t)
step (St (Var  Here)     (CCE (Cl t ce se) _)  _         s ) = Just $ St  t             ce         se                     s
step (St (Var (There n))           (CCE _ ce)  se        s ) = Just $ St (Var n)        ce         se                     s
step (St (Lam t)                          ce   se  (CS c s)) = Just $ St  t      (CCE c ce)        se                     s
step (St (App t u)                        ce   se        s ) = Just $ St  t             ce         se  ((Cl u ce se) `CS` s)
step (St (Mu t)                           ce   se        s ) = Just $ St  t             ce  (CSE s se)                   ES
step (St (Named n t)                      ce   se       ES ) = Just $ St  t             ce         se       (findStack n se)
step  _                                                      = Nothing

runMK : Term [] a [] -> (Nat, State a)
runMK t = iterCount step $ St t NCE NSE NS
