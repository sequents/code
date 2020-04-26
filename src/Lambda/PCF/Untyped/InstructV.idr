module Lambda.PCF.InstructV

import Data.List
import Iter
import Elem
import Lambda.STLC.Ty
import Lambda.PCF.Term

%default total
%access public export

-- untyped bytecode

data I : Type where
  Access : Nat -> I
  Grab   : I
  Push   : List I -> I
  Nul    : I
  Inc    : I
  Case   : List I -> List I -> I
  Loop   : I

compile : Term g a -> List I
compile (Var e)     = [Access $ elem2Nat e]
compile (Lam t)     = Grab :: compile t
compile (App t u)   = Push (compile u) :: compile t
compile  Zero       = [Nul]
compile (Succ t)    = Inc :: compile t
compile (If0 c t f) = Case (compile t) (compile f) :: compile c
compile (Fix t)     = Loop :: compile t

-- virtual machine

mutual
  Env : Type
  Env = List Clos

  data Clos : Type where
    Cl : List I -> Env -> Clos
    Vl : List I -> Env -> Clos

data Stack : Type where
  Mt  : Stack
  Arg : Clos -> Stack -> Stack
  Fun : Clos -> Stack -> Stack
  Tst : List I -> List I -> Env -> Stack -> Stack
  Suc : Stack -> Stack

data State : Type where
  Ev : List I -> Env -> Stack -> State
  Va : List I -> Env -> Stack -> State

step : State -> Maybe State
step (Ev (Access n::_) e                        s ) =
                                        (\cl => case cl of
                                                 Cl i0 e0 => Ev i0                        e0                 s
                                                 Vl i0 e0 => Va i0                        e0                 s
                                        ) <$> index' n e
step (Ev  (Push i0::i) e                        s ) = Just $ Ev i                         e   (Arg (Cl i0 e) s)
step (Ev     (Loop::i) e                        s ) = Just $ Ev i        (Cl (Loop::i) e::e)                 s
step (Ev (Case t f::i) e                        s ) = Just $ Ev i                         e       (Tst t f e s)
step (Ev      (Nul::_) _            (Tst t _ e1 s)) = Just $ Ev t                         e1                 s
step (Ev      (Inc::i) e            (Tst _ f e1 s)) = Just $ Ev f                (Cl i e::e1)                s
step (Ev      (Nul::_) e                        s ) = Just $ Va [Nul]                     e                  s
step (Ev      (Inc::i) e                        s ) = Just $ Ev i                         e             (Suc s)
step (Ev            i  e         (Arg (Cl j e1) s)) = Just $ Ev j                         e1   (Fun (Vl i e) s)
step (Ev            i  e (Fun (Vl (Grab::j) e1) s)) = Just $ Ev j                (Cl i e::e1)                s
step (Va      (Nul::_) _            (Tst t _ e1 s)) = Just $ Ev t                         e1                 s
step (Va      (Inc::i) e            (Tst _ f e1 s)) = Just $ Ev f                (Vl i e::e1)                s
step (Va            i  e (Fun (Vl (Grab::j) e1) s)) = Just $ Ev j                (Vl i e::e1)                s
step (Va            i  e                   (Suc s)) = Just $ Va (Inc::i)                  e                  s
step  _                                             = Nothing

init : Term g a -> State
init t = Ev (compile t) [] Mt

runMach : Term g a -> (Nat, State)
runMach = iterCount step . init