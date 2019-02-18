module Lambda.Untyped.KAM2

import Iter
import Lambda.Untyped.TermDB

%default total
%access public export

-- stackless

mutual
  Env : Type 
  Env = List Clos

  data Clos = ClTm Term Env 
            | ClApp Clos Clos

step : Clos -> Maybe Clos
step (ClTm  (Var  Z)      (c::_)) = Just c
step (ClTm  (Var (S n))   (_::e)) = assert_total $ step (ClTm (Var n) e)
step (ClTm  (App t0 t1)       e ) = Just $ ClApp (ClTm t0 e) (ClTm t1 e)
step (ClApp (ClTm (Lam t) e) c1) = Just $ ClTm t (c1::e)
step (ClApp  c0              c1) = ClApp <$> (step c0) <*> Just c1
step  _                          = Nothing

runKAM : Term -> Maybe Clos
runKAM t = iter step $ ClTm t []
