module Lambda.PCF.MachineV

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.PCF.Term

%default total
%access public export

-- left-to-right call-by-value

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)

  data Clos : Ty -> Type where
    Cl : Term g a -> Env g -> Clos a
    Vl : Term g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt  : Stack a a
  Arg : Clos a -> Stack b c -> Stack (a~>b) c
  Fun : Clos (a~>b) -> Stack b c -> Stack a c
  Tst : Term g a -> Term (A::g) a -> Env g -> Stack a c -> Stack A c
  Suc : Stack A c -> Stack A c

data State : Ty -> Type where
  Ev : Term g a -> Env g -> Stack a t -> State t
  Va : Term g a -> Env g -> Stack a t -> State t

step : State t -> Maybe (State t)
step (Ev (Var  Here)      (Cl t e::_)                       s ) = Just $ Ev  t                      e                 s
step (Ev (Var  Here)      (Vl t e::_)                       s ) = Just $ Va  t                      e                 s
step (Ev (Var (There el))      (_::e)                       s ) = Just $ Ev (Var el)                e                 s
step (Ev (App t u)                 e                        s ) = Just $ Ev  t                      e   (Arg (Cl u e) s)
step (Ev (Fix t)                   e                        s ) = Just $ Ev  t       (Cl (Fix t) e::e)                s
step (Ev (If0 p t f)               e                        s ) = Just $ Ev  p                      e      (Tst t f e s)
step (Ev  Zero                     _            (Tst t _ e1 s)) = Just $ Ev  t                      e1                s
step (Ev (Succ n)                  e            (Tst _ f e1 s)) = Just $ Ev  f             (Cl n e::e1)               s
step (Ev  Zero                     e                        s ) = Just $ Va  Zero                   e                 s
step (Ev (Succ t)                  e                        s ) = Just $ Ev  t                      e            (Suc s)
step (Ev  t                        e        (Arg (Cl t1 e1) s)) = Just $ Ev  t1                     e1  (Fun (Vl t e) s)
step (Ev  t                        e  (Fun (Vl (Lam t1) e1) s)) = Just $ Ev  t1            (Cl t e::e1)               s
step (Va  Zero                     _            (Tst t _ e1 s)) = Just $ Ev  t                      e1                s
step (Va (Succ n)                  e            (Tst _ f e1 s)) = Just $ Ev  f             (Vl n e::e1)               s
step (Va  t                        e  (Fun (Vl (Lam t1) e1) s)) = Just $ Ev  t1            (Vl t e::e1)               s
step (Va  t                        e                   (Suc s)) = Just $ Va (Succ t)                e                 s
step  _                                                         = Nothing

runMach : Term [] a -> (Nat, State a)
runMach t = iterCount step $ Ev t [] Mt

private
test1 : runMach Term.twotwoN = (62, Va (Term.fromN 4) [] Mt)
test1 = Refl

private
test2 : runMach Term.twotwoC = (71, Va (Term.fromN 4) [] Mt)
test2 = Refl

private
test3 : runMach Term.threeMinusTwoN = (70, Va (Term.fromN 1) [] Mt)
test3 = Refl

private
test4 : runMach Term.plusplus = (431, Va (Term.fromN 20) [] Mt)
test4 = Refl