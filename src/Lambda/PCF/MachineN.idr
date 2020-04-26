module Lambda.PCF.MachineN

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.PCF.Term

%default total
%access public export

-- call by name

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)

  data Clos : Ty -> Type where
    Cl : Term g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt  : Stack a a
  Arg : Clos a -> Stack b c -> Stack (a~>b) c
  Tst : Term g a -> Term (A::g) a -> Env g -> Stack a c -> Stack A c
  Suc : Stack A c -> Stack A c

data State : Ty -> Type where
  Ev : Term g a -> Env g -> Stack a t -> State t
  Va : Term [] A -> Stack A t -> State t

step : State t -> Maybe (State t)
step (Ev (Var  Here)      (Cl t e0::_)             s ) = Just $ Ev  t                      e0                s
step (Ev (Var (There el))       (_::e)             s ) = Just $ Ev (Var el)                e                 s
step (Ev (App t u)                  e              s ) = Just $ Ev  t                      e   (Arg (Cl u e) s)
step (Ev (Fix t)                    e              s ) = Just $ Ev  t       (Cl (Fix t) e::e)                s
step (Ev (If0 p t f)                e              s ) = Just $ Ev  p                      e      (Tst t f e s)
step (Ev  Zero                      _  (Tst t _ e1 s)) = Just $ Ev  t                      e1                s
step (Ev (Succ n)                   e  (Tst _ f e1 s)) = Just $ Ev  f             (Cl n e::e1)               s
step (Ev  Zero                      e              s ) = Just $ Va  Zero                                     s
step (Ev (Succ t)                   e              s ) = Just $ Ev  t                      e            (Suc s)
step (Ev (Lam t)                    e       (Arg c s)) = Just $ Ev  t                  (c::e)                s
step (Va  t                                   (Suc s)) = Just $ Va (Succ t)                                  s
step  _                                                = Nothing

runMach : Term [] a -> (Nat, State a)
runMach t = iterCount step $ Ev t [] Mt

private
test1 : runMach Term.twotwoN = (51, Va (Term.fromN 4) Mt)
test1 = Refl

private
test2 : runMach Term.twotwoC = (63, Va (Term.fromN 4) Mt)
test2 = Refl

private
test3 : runMach Term.threeMinusTwoN = (55, Va (Term.fromN 1) Mt)
test3 = Refl

private
test4 : runMach Term.plusplus = (523, Va (Term.fromN 20) Mt)
test4 = Refl