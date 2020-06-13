module LJ.Q.Smallstep

import Data.List
import Subset
import Iter

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LJ.Q.Term

%default total
%access public export

-- reduction

subst1V : ValQ (a::g) b -> ValQ g a -> ValQ g b
subst1V  t                  (Var el) = renameVal (contract el) t
subst1V (Var Here)        a@(Lam _)  = a
subst1V (Var (There el))    (Lam _)  = Var el
subst1V (Lam t)           a@(Lam _)  = Lam $ Let (shiftVal a) (shiftTerm t)

subst1T : TermQ (a::g) b -> TermQ g a -> TermQ g b
subst1T t (V v)         = Let v t
subst1T t (GApp el v u) = GApp el v (subst1T (renameTerm (permute0 . weaken) t) u)
subst1T t (Let v u)     = Let v (subst1T (renameTerm (permute0 . weaken) t) u)

stepT : TermQ g a -> Maybe (TermQ g a)
stepT (Let   (Var el)  t                   ) = Just $ renameTerm (contract el) t
stepT (Let a@(Lam _)  (V v)                ) = Just $ V $ subst1V v a
stepT (Let a@(Lam t)  (GApp  Here      v u)) = [| subst1T (assert_total $ stepT (Let (shiftVal a) (shiftTerm u)))
                                                          (pure (Let (subst1V v a) t)) |]
  --Just $ assert_total $ subst1T (Let (shiftVal a) (shiftTerm u))
  --                                                            (Let (subst1V v a) t)
stepT (Let a@(Lam _)  (GApp (There el) v u)) = Just $ GApp el (subst1V v a) (Let (shiftVal a) (shiftTerm u))
stepT (Let v           t                   ) = [| Let (pure v) (stepT t) |]
stepT  _                                     = Nothing

stepIter : Term [] a -> (Nat, TermQ [] a)
stepIter = iterCount stepT . encode
