module MuPCF.InstructN

import Data.List
import Iter
import Path
import Elem
import LambdaMu.Ty
import MuPCF.Term
import MuPCF.Bytecode

%default total
%access public export

-- call-by-name virtual machine

mutual
  data CEnv : List Ty -> Ty -> Type where
    NCE : CEnv [] c
    CCE : Clos a c -> CEnv g c -> CEnv (a::g) c

  data SEnv : List Ty -> Ty -> Type where
    NSE : SEnv [] c
    CSE : Stack a c -> SEnv d c -> SEnv (a::d) c

  data Clos : Ty -> Ty -> Type where
    Cl : Control g a d -> CEnv g c -> SEnv d c -> Clos a c

  data Stack : Ty -> Ty -> Type where
    Mt : Stack a a
    Tp : Stack Bot a
    Arg : Clos a c -> Stack b c -> Stack (a~>b) c
    Tst : Control g a d -> Control (A::g) a d -> CEnv g c -> SEnv d c -> Stack a c -> Stack A c
    Suc : Stack A c -> Stack A c

data State : Ty -> Type where
  Ev : Control g a d -> CEnv g t -> SEnv d t -> Stack a t -> State t
  Va : Control g A d -> Stack A t -> State t

Show (State b) where
  show (Ev ctr _ _ _) = show ctr
  show (Va ctr _) = show ctr

indexE : Elem a g -> CEnv g c -> Clos a c
indexE  Here     (CCE cl _)  = cl
indexE (There e) (CCE _  ce) = indexE e ce

findStack : Elem a d -> SEnv d c -> Stack a c
findStack  Here     (CSE st _) = st
findStack (There e) (CSE _ se) = findStack e se

step : State b -> Maybe (State b)
step (Ev (MkCtr _ _ _ (Access n::_)) ce _                   s ) = let Cl c0 ce0 se0 = indexE n ce in
                                                                  Just $ Ev           c0            ce0        se0                     s
step (Ev (MkCtr d b z  (Push c0::i)) ce se                  s ) = Just $ Ev (MkCtr d b z i)         ce         se   (Arg (Cl c0 ce se) s)
step (Ev (MkCtr d b z     (Loop::i)) ce se                  s ) = let ce2 = CCE (Cl (MkCtr d b z (Loop::i)) ce se) ce in
                                                                  Just $ Ev (MkCtr d b z i)         ce2        se                      s
step (Ev (MkCtr d b z (Case t f::i)) ce se                  s ) = Just $ Ev (MkCtr d b z i)         ce         se       (Tst t f ce se s)
step (Ev (MkCtr d b z    (Catch::i)) ce se                  s ) = Just $ Ev (MkCtr d b z i)         ce  (CSE s se)                    Tp
step (Ev (MkCtr d b z  (Throw n::i)) ce se                 Tp ) = Just $ Ev (MkCtr d b z i)         ce         se        (findStack n se)
step (Ev (MkCtr _ _ _      (Nul::_)) _  _  (Tst t _ ce1 se1 s)) = Just $ Ev              t          ce1        se1                     s
step (Ev (MkCtr d b z      (Inc::i)) ce se (Tst _ f ce1 se1 s)) = let ce2 = CCE (Cl (MkCtr d b z i) ce se) ce1 in
                                                                  Just $ Ev              f          ce2        se1                     s
step (Ev (MkCtr d _ z      (Nul::_)) _  _                   s ) = Just $ Va (MkCtr d A z [Nul])                                        s
step (Ev (MkCtr d b z      (Inc::i)) ce se                  s ) = Just $ Ev (MkCtr d b z i)         ce         se                 (Suc s)
step (Ev (MkCtr d b z     (Grab::i)) ce se          (Arg cl s)) = Just $ Ev (MkCtr d b z i) (CCE cl ce)        se                      s
step (Va (MkCtr d b z             i)                   (Suc s)) = Just $ Va (MkCtr d b z (Inc::i))                                     s
step  _                                                         = Nothing

init : Control [] a [] -> State a
init c = Ev c NCE NSE Mt

runMach : Control [] a [] -> (Nat, State a)
runMach = iterCount step . init
