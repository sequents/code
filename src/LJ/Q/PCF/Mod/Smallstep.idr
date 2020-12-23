module LJ.Q.PCF.Smallstep

import Data.List
import Subset
import Iter

import Lambda.PCF.V.Mod.Ty
import LJ.Q.PCF.Mod.Term

%default total
%access public export

-- reduction

subst1T : TermQ g a -> TermQ (a::g) b -> TermQ g b
subst1T (V v)           t = Let v t
subst1T (GApp el v u)   t = GApp el v (subst1T u (renameTerm (permute0 . weaken) t))
subst1T (GIf0 el u v c) t = GIf0 el u v (subst1T c (renameTerm (permute0 . weaken) t))
subst1T (Bnd el v)      t = Bnd el (subst1T v (renameTerm (permute0 . weaken) t))
subst1T (Let v u)       t = Let v (subst1T u (renameTerm (permute0 . weaken) t))

subst1V : ValQ g a -> ValQ (a::g) b -> ValQ g b
subst1V (Var el)  t               = renameVal (contract el) t
subst1V  a       (Var Here)       = a
subst1V  a       (Var (There el)) = Var el
subst1V  a       (Lam t)          = Lam $ Let (shiftVal a) (shiftTerm t)
subst1V  a        Zero            = Zero
subst1V  a       (Succ t)         = Succ (subst1V a t)
subst1V  a       (Fix t)          = Fix $ Let (shiftVal a) (shiftTerm t)

subst1VT : ValQ g a -> TermQ (a::g) b -> TermQ g b
subst1VT    (Var el)  t                      = renameTerm (contract el) t
subst1VT  a          (V v)                   = V $ subst1V a v
subst1VT  a@(Lam t)  (GApp  Here      v c)   = subst1T (Let (subst1V a v) t)
                                                       (Let (shiftVal a) (shiftTerm c))
subst1VT  a          (GApp (There el) v c)   = GApp el (subst1V a v) (Let (shiftVal a) (shiftTerm c))
subst1VT  a@Zero     (GIf0  Here u v c)      = subst1T (Let a u) (Let (shiftVal a) (shiftTerm c))
subst1VT  a@(Succ t) (GIf0  Here u v c)      = subst1T (Let (shiftVal t) (shiftTerm v)) (Let (shiftVal a) (shiftTerm c))
subst1VT  a          (GIf0 (There el) u v c) = GIf0 el (Let a u) (Let (shiftVal a) (shiftTerm v)) (Let (shiftVal a) (shiftTerm c))
subst1VT  a@(Fix t)  (Bnd  Here c)           = subst1T (Let a t) (Let (shiftVal a) (shiftTerm c))
subst1VT  a          (Bnd (There el) c)      = Bnd el (Let (shiftVal a) (shiftTerm c))
subst1VT  a          (Let v c)               = Let a (subst1VT v c)

stepQ : TermQ g a -> Maybe (TermQ g a)
stepQ (Let v t) = Just $ subst1VT v t
stepQ _         = Nothing

stepIter : TermQ [] a -> (Nat, TermQ [] a)
stepIter = iterCount stepQ
