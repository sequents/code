module LJ.T.TJAM

import Data.List
import Data.List.Quantifiers
import Elem
import Iter

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LJ.T.Term

%default total
%access public export

mutual
  Env : List Ty -> Type
  Env = All Clos

  data Clos : Ty -> Type where
    Cl : TermJ g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt  : Stack a a
  Arg : Clos a -> Stack b c -> Stack (a~>b) c

snoc : Stack a (b~>c) -> Clos b -> Stack a c
snoc  Mt       b = Arg b Mt
snoc (Arg a s) b = Arg a (snoc s b)

append : Stack a b -> Stack b c -> Stack a c
append  Mt        s2 = s2
append (Arg c s1) s2 = Arg c (append s1 s2)

data State : Ty -> Type where
  S1 : TermJ g a -> Env g -> Stack a z -> State z
  S2 : TermJ g a -> Env g -> Stack a b -> Spine d b c -> Env d -> Stack c z -> State z

initState : TermJ [] a -> State a
initState a = S1 a [] Mt

step : State b -> Maybe (State b)
step (S1 (Var el k) e         c ) = let Cl t g = indexAll el e in
                                    Just $ S2 t g Mt k e c
step (S1 (Lam t   ) e (Arg ug c)) = Just $ S1 t (ug::e) c
step (S1 (Cut t k ) e         c ) = Just $ S2 t e Mt k e c
step (S2 t e b  Nil       _   c ) = Just $ S1 t e (append b c)
step (S2 t e b (Cons u k) g   c ) = Just $ S2 t e (snoc b (Cl u g)) k g c
step  _                           = Nothing

runTJAM : Term [] a -> (Nat, State a)
runTJAM = iterCount step . initState . encode

-- test

private
test1 : runTJAM TestTm0 = (6, initState $ encode ResultTm)
test1 = Refl

private
test2 : runTJAM TestTm1 = (12, initState $ encode ResultTm)
test2 = Refl

private
test3 : runTJAM TestTm2 = (12, initState $ encode ResultTm)
test3 = Refl
