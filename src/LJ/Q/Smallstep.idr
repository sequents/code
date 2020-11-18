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

subst1T : TermQ g a -> TermQ (a::g) b -> TermQ g b
subst1T (V v)         t = Let v t
subst1T (GApp el v u) t = GApp el v (subst1T u (renameTerm (permute0 . weaken) t))
subst1T (Let v u)     t = Let v (subst1T u (renameTerm (permute0 . weaken) t))

subst1V : ValQ g a -> ValQ (a::g) b -> ValQ g b
subst1V   (Var el)  t               = renameVal (contract el) t
subst1V a@(Lam _)  (Var Here)       = a
subst1V   (Lam _)  (Var (There el)) = Var el
subst1V a@(Lam _)  (Lam t)          = Lam $ Let (shiftVal a) (shiftTerm t)

subst1VT : ValQ g a -> TermQ (a::g) b -> TermQ g b
subst1VT   (Var el)  t                    = renameTerm (contract el) t
subst1VT a@(Lam _)  (V v)                 = V $ subst1V a v
subst1VT a@(Lam t)  (GApp  Here      v u) = subst1T (Let (subst1V a v) t)
                                                    (Let (shiftVal a) (shiftTerm u))
subst1VT a@(Lam _)  (GApp (There el) v u) = GApp el (subst1V a v) (Let (shiftVal a) (shiftTerm u))
subst1VT a@(Lam _)  (Let v u)             = Let a (subst1VT v u)

stepT : TermQ g a -> Maybe (TermQ g a)
stepT (Let v t) = Just $ subst1VT v t
stepT _         = Nothing

stepIter : Term [] a -> (Nat, TermQ [] a)
stepIter = iterCount stepT . encode
