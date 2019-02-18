module PCF.InstructN

import Data.List
import Iter
import Path
import Elem
import Lambda.STLC.Ty
import PCF.Term

%default total
%access public export

-- typed bytecode

mutual
  data I : (List Ty, Ty) -> (List Ty, Ty) -> Type where
    Access : Elem a g -> I (g,a) (g,a)
    Grab   : I (g,a~>b) (a::g,b) 
    Push   : Control g a -> I (g,b) (g,a~>b)
    Nul    : I (g,A) (g,a)
    Inc    : I (g,A) (g,A)
    Case   : Control g a -> Control (A::g) a -> I (g,a) (g,A)
    Loop   : I (g,a) (a::g,a)
  
  Control : List Ty -> Ty -> Type
  Control g a = (d**b**Path I (g,a) (d,b))

-- compiler  
  
compile : Term g a -> Control g a
compile {g} {a} (Var e)       = (g**a**[Access e])
compile         (Lam t)       = let (d**b**tt) = compile t in 
                                (d**b** Grab :: tt)
compile         (App {b} t u) = let (d**c**tt) = compile t in 
                                (d**c** Push {b} (compile u) :: tt)
compile {g}      Zero         = (g**A**[Nul])
compile         (Succ t)      = let (d**b**tt) = compile t in 
                                (d**b** Inc :: tt)
compile         (If0 c t f)   = let (d**b**tt) = compile c in 
                                (d**b** Case (compile t) (compile f) :: tt)
compile         (Fix t)       = let (d**b**tt) = compile t in 
                                (d**b** Loop :: tt)

-- virtual machine

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

record State (b : Ty) where
  constructor St 
  tm  : Control g a 
  env : Env g 
  stk : Stack a b 
  res : Nat

indexE : Elem a g -> Env g -> Clos a
indexE Here       (CE e _)  = e
indexE (There el) (CE _ es) = indexE el es

step : State b -> Maybe (State b)  
step (St (_**_**Access n::_) e             s  r) = let Cl c0 e0 = indexE n e in 
                                                   Just $ St        c0                            e0                s    r
step (St (d**b**    Grab::c) e     (Arg cl s) r) = Just $ St (d**b**c)                     (CE cl e)                s    r
step (St (d**b** Push c0::c) e             s  r) = Just $ St (d**b**c)                            e  (Arg (Cl c0 e) s)   r
step (St (_**_**     Nul::_) _ (Tst t _ e1 s) r) = Just $ St        t                             e1                s    r
step (St (d**b**     Inc::c) e (Tst _ f e1 s) r) = Just $ St        f        (CE (Cl (d**b**c) e) e1)               s    r
step (St (d**b**     Inc::c) e             s  r) = Just $ St (d**b**c)                            e                 s (S r)
step (St (d**b**Case t f::c) e             s  r) = Just $ St (d**b**c)                            e      (Tst t f e s)   r
step (St (d**b**    Loop::c) e             s  r) = Just $ St (d**b**c) (CE (Cl (d**b**Loop::c) e) e)                s    r
step  _                                          = Nothing  

init : Term [] a -> State a
init t = St (compile t) NE Mt Z
