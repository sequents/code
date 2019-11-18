module PCF.InstructN

import Data.List
import Iter
import Path
import Elem
import Lambda.STLC.Ty
import PCF.Term
import PCF.Bytecode

%default total
%access public export

-- call-by-name virtual machine

mutual
  data Env : List Ty -> Type where
    NE : Env []
    CE : Clos a -> Env g -> Env (a::g)

  data Clos : Ty -> Type where
    Cl : Control g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt  : Stack a a
  Arg : Clos a -> Stack b c -> Stack (a~>b) c
  Tst : Control g a -> Control (A::g) a -> Env g -> Stack a c -> Stack A c
  Suc : Stack a c -> Stack a c

data State : Ty -> Type where
  Ev : Control g a -> Env g -> Stack a b -> State b
  Rw : Control g A -> Stack A b -> State b

Show (State b) where
  show (Ev ctr _ _) = show ctr
  show (Rw ctr _) = show ctr

indexE : Elem a g -> Env g -> Clos a
indexE Here       (CE e _)  = e
indexE (There el) (CE _ es) = indexE el es

step : State b -> Maybe (State b)
step (Ev (MkCtr _ _ (Access n::_)) e             s ) = let Cl c0 e0 = indexE n e in
                                                       Just $ Ev           c0                                          e0                s
step (Ev (MkCtr d b     (Grab::i)) e     (Arg cl s)) = Just $ Ev (MkCtr d b i)                                  (CE cl e)                s
step (Ev (MkCtr d b  (Push c0::i)) e             s ) = Just $ Ev (MkCtr d b i)                                         e  (Arg (Cl c0 e) s)
step (Ev (MkCtr _ _      (Nul::_)) _ (Tst t _ e1 s)) = Just $ Ev            t                                          e1                s
step (Ev (MkCtr d b      (Inc::i)) e (Tst _ f e1 s)) = Just $ Ev            f                 (CE (Cl (MkCtr d b i) e) e1)               s
step (Ev (MkCtr d _      (Nul::_)) _             s ) = Just $ Rw (MkCtr d A [Nul])                                                       s
step (Ev (MkCtr d b      (Inc::i)) e             s ) = Just $ Ev (MkCtr d b i)                                         e            (Suc s)
step (Ev (MkCtr d b (Case t f::i)) e             s ) = Just $ Ev (MkCtr d b i)                                         e      (Tst t f e s)
step (Ev (MkCtr d b     (Loop::i)) e             s ) = Just $ Ev (MkCtr d b i)        (CE (Cl (MkCtr d b (Loop::i)) e) e)                s
step (Rw (MkCtr d b             i)          (Suc s)) = Just $ Rw (MkCtr d b (Inc::i))                                                    s
step  _                                              = Nothing

init : Control [] a -> State a
init c = Ev c NE Mt

runMach : Control [] a -> (Nat, State a)
runMach = iterCount step . init
