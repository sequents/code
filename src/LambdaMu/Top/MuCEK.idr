module LambdaMu.Top.MuCEK

import Data.List
import Iter
import LambdaMu.Ty
import LambdaMu.Top.Term

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

data State : Ty -> Type where
  Ev : Term g a d -> CEnv g t -> SEnv d t -> Stack a t -> State t
  Cm : Cmd g d -> CEnv g t -> SEnv d t -> State t

step : State b -> Maybe (State b)
step (Ev (Var  Here)     (CCE (Cl t ce se) _) _                             s ) = Just $ Ev  t                        ce         se                    s
step (Ev (Var (There el))          (CCE _ ce) se                            s ) = Just $ Ev (Var el)                  ce         se                    s
step (Ev (App t u)                        ce  se                            s ) = Just $ Ev  t                        ce         se  (Arg (Cl u ce se) s)
step (Ev (Mu t)                           ce  se                            s ) = Just $ Cm  t                        ce  (CSE s se)
step (Cm (Top t)                          ce  se)                               = Just $ Ev  t             ce         se                              Tp
step (Cm (Named n t)                      ce  se)                               = Just $ Ev  t                        ce         se      (findStack n se)
step (Ev  t                               ce  se (Fun (Cl (Lam t1) ce1 se1) s)) = Just $ Ev  t1     (CCE (Cl t ce se) ce1)       se1                   s
step (Ev  t                               ce  se       (Arg (Cl t1 ce1 se1) s)) = Just $ Ev  t1                       ce1        se1 (Fun (Cl t ce se) s)
step  _                                                                         = Nothing

runMCEK : Term [] a [] -> (Nat, State a)
runMCEK t = iterCount step $ Ev t NCE NSE Mt
