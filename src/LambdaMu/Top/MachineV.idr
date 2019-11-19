module LambdaMu.Top.MachineV

import Data.List
import Iter
import LambdaMu.Ty
import LambdaMu.Top.Term

%default total
%access public export

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
    MS : Elem a d -> SEnv d -> Stack Bot
    CS : Clos a -> Stack b-> Stack (a~>b)
    FS : Term (a::g) b d -> CEnv g -> SEnv d -> Stack b -> Stack a

findStack : Elem a d -> SEnv d c -> Stack a c
findStack  Here     (CSE st _) = st
findStack (There e) (CSE _ se) = findStack e se 

data State : Type where
  StC : Term g a d -> CEnv g -> SEnv d -> Stack a -> State
  StE : Term g a d -> CEnv g -> SEnv d -> Stack a -> State
  StL : Term g a d -> CEnv g -> SEnv d -> Clos a -> Stack a -> State

step : State b -> Maybe (State b)
step (StE (Var  Here)     (CCE (Cl t ce se) _)  _                      s ) = Just $ St  t                              ce         se                   s 
step (StE (Var (There el))          (CCE _ ce)  se                     s ) = Just $ St (Var el)                        ce         se                   s 
step (StE (Lam t)                          ce   se      (FS t1 ce1 se1 s)) = Just $ St  t1     (CCE (Cl (Lam t) ce se) ce1)       se1                  s 
step (StE (Lam t)                          ce   se (CS (Cl t1 ce1 se1) s)) = Just $ St  t1                             ce1        se1      (FS t ce se s)
step (StE (App t u)                        ce   se                     s ) = Just $ St  t                              ce         se  (CS (Cl u ce se) s)
step (StE (Mu t)                           ce   se                     s ) = Just $ St  t                              ce  (CSE s se)                 ES
--step (StE (Named n t)                      ce   se                    ES ) = Just $ St  t                              ce         se     (findStack n se)
step  _                                                                   = Nothing   