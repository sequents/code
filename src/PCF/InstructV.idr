module PCF.InstructV

import Data.List
import Iter
import Path
import Elem
import Lambda.STLC.Ty
import PCF.Term
import PCF.Bytecode

import Data.Fuel

%default total
%access public export

-- call-by-value virtual machine

mutual
  data Env : List Ty -> Type where
    NE : Env []
    CE : Clos a -> Env g -> Env (a::g)

  data Clos : Ty -> Type where
    Cl : Control g a -> Env g -> Clos a
    Vl : Control g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt  : Stack a a
  Arg : Clos a -> Stack b c -> Stack (a~>b) c
  Fun : Clos (a~>b) -> Stack b c -> Stack a c
  Tst : Control g a -> Control (A::g) a -> Env g -> Stack a c -> Stack A c
  Suc : Stack A c -> Stack A c

data State : Ty -> Type where
  Ev : Control g a -> Env g -> Stack a b -> State b
  Va : Control g a -> Env g -> Stack a b -> State b

Show (State b) where
  show (Ev ctr _ _) = show ctr
  show (Va ctr _ _) = show ctr

indexE : Elem a g -> Env g -> Clos a
indexE  Here      (CE e _)  = e
indexE (There el) (CE _ es) = indexE el es

step : State b -> Maybe (State b)
step (Ev     (MkCtr _ _ (Access n::_)) e                                    s ) =
                                                                    case indexE n e of
                                                                      Cl c0 e0 => Just $ Ev            c0                                         e0                  s
                                                                      Vl c0 e0 => Just $ Va            c0                                         e0                  s
step (Ev     (MkCtr d b  (Push c0::i)) e                                    s ) = Just $ Ev (MkCtr d b i)                                         e    (Arg (Cl c0 e) s)
step (Ev     (MkCtr d b     (Loop::i)) e                                    s ) = Just $ Ev (MkCtr d b i)        (CE (Cl (MkCtr d b (Loop::i)) e) e)                  s
step (Ev     (MkCtr d b (Case t f::i)) e                                    s ) = Just $ Ev (MkCtr d b i)                                         e        (Tst t f e s)
step (Ev     (MkCtr _ _      (Nul::_)) _                        (Tst t _ e1 s)) = Just $ Ev            t                                          e1                  s
step (Ev     (MkCtr d b      (Inc::i)) e                        (Tst _ f e1 s)) = Just $ Ev            f                 (CE (Cl (MkCtr d b i) e) e1)                 s
step (Ev {g} (MkCtr _ _      (Nul::_)) e                                    s ) = Just $ Va (MkCtr g A [Nul])                                     e                   s
step (Ev     (MkCtr d b      (Inc::i)) e                                    s ) = Just $ Ev (MkCtr d b i)                                         e              (Suc s)
step (Ev      ctr                      e                     (Arg (Cl j e1) s)) = Just $ Ev            j                                          e1  (Fun (Vl ctr e) s)
step (Ev      ctr                      e (Fun (Vl (MkCtr k c (Grab::j)) e1) s)) = Just $ Ev (MkCtr k c j)                          (CE (Cl ctr e) e1)                 s
step (Va     (MkCtr _ _      (Nul::_)) _                        (Tst t _ e1 s)) = Just $ Ev            t                                          e1                  s
step (Va     (MkCtr d b      (Inc::i)) e                        (Tst _ f e1 s)) = Just $ Ev            f                 (CE (Vl (MkCtr d b i) e) e1)                 s
step (Va      ctr                      e (Fun (Vl (MkCtr k c (Grab::j)) e1) s)) = Just $ Ev (MkCtr k c j)                          (CE (Vl ctr e) e1)                 s
step (Va     (MkCtr d b            i ) e                               (Suc s)) = Just $ Va (MkCtr d b (Inc::i))                                  e                   s
step  _                                                                         = Nothing

init : Control [] a -> State a
init c = Ev c NE Mt

runMach : Control [] a -> (Nat, State a)
runMach = iterCount step . init
