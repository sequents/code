module LambdaMu.MuCEK

import Data.List
import Iter
import LambdaMu.Ty
import LambdaMu.Term

%default total
%access public export

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
    Mt : Stack a a
    Tp : Stack Bot a
    Arg : Clos a c -> Stack b c -> Stack (a~>b) c
    Fun : Clos (a~>b) c -> Stack b c -> Stack a c

findStack : Elem a d -> SEnv d c -> Stack a c
findStack  Here     (CSE st _) = st
findStack (There e) (CSE _ se) = findStack e se

record State (t : Ty) where
  constructor St
  tm : Term g a d
  сenv : CEnv g t
  senv : SEnv d t
  stk : Stack a t

step : State b -> Maybe (State b)
step (St (Var  Here)     (CCE (Cl t ce se) _) _                             s ) = Just $ St  t                        ce         se                    s
step (St (Var (There el))          (CCE _ ce) se                            s ) = Just $ St (Var el)                  ce         se                    s
step (St (App t u)                        ce  se                            s ) = Just $ St  t                        ce         se  (Arg (Cl u ce se) s)
step (St  t                               ce  se (Fun (Cl (Lam t1) ce1 se1) s)) = Just $ St  t1     (CCE (Cl t ce se) ce1)       se1                   s
step (St  t                               ce  se       (Arg (Cl t1 ce1 se1) s)) = Just $ St  t1                       ce1        se1 (Fun (Cl t ce se) s)
step (St (Mu t)                           ce  se                            s ) = Just $ St  t                        ce  (CSE s se)                  Tp
step (St (Named n t)                      ce  se                           Tp ) = Just $ St  t                        ce         se      (findStack n se)
step  _                                                                         = Nothing

runMCEK : Term [] a [] -> (Nat, State a)
runMCEK t = iterCount step $ St t NCE NSE Mt
