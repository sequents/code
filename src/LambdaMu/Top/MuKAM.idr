module LambdaMu.Top.MuKAM

import Data.List
import Iter
import Subset
import LambdaMu.Ty
import LambdaMu.Top.Term

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
    Mt : Stack a a
    Tp : Stack Bot a
    Arg : Clos a c -> Stack b c -> Stack (a~>b) c

findStack : Elem a d -> SEnv d c -> Stack a c
findStack  Here     (CSE st _) = st
findStack (There e) (CSE _ se) = findStack e se 

data State : Ty -> Type where
  Ev : Term g a d -> CEnv g t -> SEnv d t -> Stack a t -> State t
  Cm : Cmd g d -> CEnv g t -> SEnv d t -> Stack Bot t -> State t  

step : State t -> Maybe (State t)
step (Ev (Var  Here)     (CCE (Cl t ce se) _)  _         s ) = Just $ Ev  t             ce         se                     s
step (Ev (Var (There n))           (CCE _ ce)  se        s ) = Just $ Ev (Var n)        ce         se                     s
step (Ev (Lam t)                          ce   se (Arg c s)) = Just $ Ev  t      (CCE c ce)        se                     s
step (Ev (App t u)                        ce   se        s ) = Just $ Ev  t             ce         se   (Arg (Cl u ce se) s)
step (Ev (Mu t)                           ce   se        s ) = Just $ Cm  t             ce  (CSE s se)                   Tp
step (Cm (Top t)                          ce   se       Tp ) = Just $ Ev  t             ce         se                    Tp
step (Cm (Named n t)                      ce   se       Tp ) = Just $ Ev  t             ce         se       (findStack n se)
step  _                                                      = Nothing

runMK : Term [] a [] -> (Nat, State a)
runMK t = iterCount step $ Ev t NCE NSE Mt

test1 : Term [] (A~>A) []
test1 = App andFst (App (App pair (Lam {a=A} {b=A} $ Var Here)) (Lam {a=A} $ Lam {a=A} $ Var Here))

test2 : Term [] (A~>A~>A) []
test2 = App andSnd (App (App pair (Lam {a=A} {b=A} $ Var Here)) (Lam {a=A} $ Lam {a=A} $ Var Here))