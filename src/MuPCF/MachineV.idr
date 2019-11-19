module MuPCF.MachineV

import Data.List
import Iter
import Subset
import LambdaMu.Ty
import MuPCF.Term

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
    Fun : Clos (a~>b) c -> Stack b c -> Stack a c
    Tst : Term g a d -> Term (A::g) a d -> CEnv g c -> SEnv d c -> Stack a c -> Stack A c
    Suc : Stack a c -> Stack a c

findStack : Elem a d -> SEnv d c -> Stack a c
findStack  Here     (CSE st _) = st
findStack (There e) (CSE _ se) = findStack e se

data State : Ty -> Type where
  Ev : Term g a d -> CEnv g t -> SEnv d t -> Stack a t -> State t
  Rw : Term [] A [] -> Stack A t -> State t

step : State a -> Maybe (State a)
step (Ev (Var  Here)     (CCE (Cl t ce se) _)   _                            s ) = Just $ Ev  t                             ce         se                     s
step (Ev (Var (There n))           (CCE _ ce)  se                            s ) = Just $ Ev (Var n)                        ce         se                     s
step (Ev (App t u)                        ce   se                            s ) = Just $ Ev  t                             ce         se   (Arg (Cl u ce se) s)
step (Ev (Fix t)                          ce   se                            s ) = Just $ Ev  t     (CCE (Cl (Fix t) ce se) ce)        se                     s
step (Ev  t                               ce   se (Fun (Cl (Lam t1) ce1 se1) s)) = Just $ Ev  t1          (CCE (Cl t ce se) ce1)       se1                    s
step (Ev  t                               ce   se       (Arg (Cl t1 ce1 se1) s)) = Just $ Ev  t1                            ce1        se1  (Fun (Cl t ce se) s)
step (Ev (Mu t)                           ce   se                            s ) = Just $ Ev  t                             ce  (CSE s se)                   Tp
step (Ev (Named n t)                      ce   se                           Tp ) = Just $ Ev  t                             ce         se       (findStack n se)
step (Ev  Zero                             _    _           (Tst t _ ce1 se1 s)) = Just $ Ev  t                             ce1        se1                    s
step (Ev (Succ n)                         ce   se           (Tst _ f ce1 se1 s)) = Just $ Ev  f           (CCE (Cl n ce se) ce1)       se1                    s
step (Ev  Zero                             _    _                            s ) = Just $ Rw  Zero                                                            s
step (Ev (Succ t)                         ce   se                            s ) = Just $ Ev  t                             ce         se                (Suc s)
step (Ev (If0 p t f)                      ce   se                            s ) = Just $ Ev  p                             ce         se      (Tst t f ce se s)
step (Rw  t                                                             (Suc s)) = Just $ Rw (Succ t)                                                         s
step  _                                                                          = Nothing

runMV : Term [] a [] -> (Nat, State a)
runMV t = iterCount step $ Ev t NCE NSE Mt
