module LambdaMu.PCF.Top.MachineV

import Data.List
import Iter
import Subset
import LambdaMu.Ty
import LambdaMu.PCF.Top.Term

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
    Vl : Term g a d -> CEnv g c -> SEnv d c -> Clos a c

  data Stack : Ty -> Ty -> Type where
    Mt : Stack a a
    Tp : Stack Bot a
    Arg : Clos a c -> Stack b c -> Stack (a~>b) c
    Fun : Clos (a~>b) c -> Stack b c -> Stack a c
    Tst : Term g a d -> Term (A::g) a d -> CEnv g c -> SEnv d c -> Stack a c -> Stack A c
    Suc : Stack A c -> Stack A c

findStack : Elem a d -> SEnv d c -> Stack a c
findStack  Here     (CSE st _) = st
findStack (There e) (CSE _ se) = findStack e se

data State : Ty -> Type where
  Ev : Term g a d -> CEnv g t -> SEnv d t -> Stack a t -> State t
  Cm : Cmd g d -> CEnv g t -> SEnv d t -> State t
  Va : Term g a d -> CEnv g t -> SEnv d t -> Stack a t -> State t

step : State t -> Maybe (State t)
step (Ev (Var  Here)      (CCE cl _)  _                            s ) =
                                                         case cl of
                                                           Cl t ce se => Just $ Ev  t                             ce         se                     s
                                                           Vl t ce se => Just $ Va  t                             ce         se                     s
step (Ev (Var (There el)) (CCE _ ce) se                            s ) = Just $ Ev (Var el)                       ce         se                    s
step (Ev (App t u)               ce  se                            s ) = Just $ Ev  t                             ce         se  (Arg (Cl u ce se) s)
step (Ev (Fix t)                 ce  se                            s ) = Just $ Ev  t     (CCE (Cl (Fix t) ce se) ce)        se                    s
step (Ev (If0 p t f)             ce  se                            s ) = Just $ Ev  p                             ce         se     (Tst t f ce se s)
step (Ev  Zero                    _   _           (Tst t _ ce1 se1 s)) = Just $ Ev  t                             ce1        se1                   s
step (Ev (Succ n)                ce  se           (Tst _ f ce1 se1 s)) = Just $ Ev  f           (CCE (Cl n ce se) ce1)       se1                   s
step (Ev  Zero                   ce  se                            s ) = Just $ Va  Zero                          ce         se                    s
step (Ev (Succ t)                ce  se                            s ) = Just $ Ev  t                             ce         se               (Suc s)
step (Ev (Mu t)                  ce  se                            s ) = Just $ Cm  t                             ce  (CSE s se)
step (Cm (Top t)                 ce  se)                               = Just $ Ev  t                             ce         se                   Tp
step (Cm (Named n t)             ce  se)                               = Just $ Ev  t                             ce         se     (findStack n se)
step (Ev  t                      ce  se       (Arg (Cl t1 ce1 se1) s)) = Just $ Ev  t1                            ce1        se1 (Fun (Vl t ce se) s)
step (Ev  t                      ce  se (Fun (Vl (Lam t1) ce1 se1) s)) = Just $ Ev  t1          (CCE (Cl t ce se) ce1)       se1                   s
step (Va  Zero                    _   _           (Tst t _ ce1 se1 s)) = Just $ Ev  t                             ce1        se1                   s
step (Va (Succ n)                ce  se           (Tst _ f ce1 se1 s)) = Just $ Ev  f           (CCE (Vl n ce se) ce1)       se1                   s
step (Va  t                      ce  se (Fun (Vl (Lam t1) ce1 se1) s)) = Just $ Ev  t1          (CCE (Vl t ce se) ce1)       se1                   s
step (Va  t                      ce  se                       (Suc s)) = Just $ Va (Succ t)                       ce         se                    s
step  _                                                                = Nothing

runMV : Term [] a [] -> (Nat, State a)
runMV t = iterCount step $ Ev t NCE NSE Mt

private
test1 : runMV Term.twotwoN = (62, Va (Term.fromN 4) NCE NSE Mt)
test1 = Refl

private
test2 : runMV Term.twotwoC = (71, Va (Term.fromN 4) NCE NSE Mt)
test2 = Refl

private
test3 : runMV Term.threeMinusTwoN = (94, Va (Term.fromN 1) NCE NSE Mt)
test3 = Refl

private
test4 : runMV Term.twoMinusThreeN = (85, Va (Term.fromN 1) NCE NSE Mt)
test4 = Refl

private
test5 : runMV Term.plusplus = (431, Va (Term.fromN 20) NCE NSE Mt)
test5 = Refl
