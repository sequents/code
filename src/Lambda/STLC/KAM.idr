module Lambda.STLC.KAM

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : Term g a -> Env g -> Clos a

-- list of arguments encountered along the spine of a term    
data Stack : Ty -> Ty -> Type where
  NS : Stack a a
  CS : Clos a -> Stack b c -> Stack (a~>b) c

record State (b : Ty) where
  constructor St 
  tm : Term g a 
  env : Env g 
  stk : Stack a b 

step : State b -> Maybe (State b)
step (St (Var  Here     ) (Cl t e0::_)       s ) = Just $ St  t           e0              s
step (St (Var (There el))       (_::e)       s ) = Just $ St (Var el)     e               s
step (St (Lam t         )           e  (CS c s)) = Just $ St  t       (c::e)              s
step (St (App t u       )           e        s ) = Just $ St  t           e  (Cl u e `CS` s)
step  _                                          = Nothing  

runKAM : Term [] a -> (Nat, Maybe (State a))
runKAM t = iterCount step $ St t [] NS

private
test1 : runKAM TestTm1 = (6, Just (St {g=[]} {a=TestTy} ResultTm [] NS))
test1 = Refl

private
test2 : runKAM TestTm2 = (6, Just (St {g=[]} {a=TestTy} ResultTm [] NS))
test2 = Refl

