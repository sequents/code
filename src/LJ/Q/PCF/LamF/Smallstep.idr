module LJ.Q.PCF.LamF.Smallstep

import Data.List
import Subset
import Iter
import Lambda.STLC.Ty

--import Lambda.PCF.V.Mod.Ty
--import Lambda.PCF.Term
import LJ.Q.PCF.LamF.Term

%default total
%access public export

-- reduction

subst1T : TermQ g a -> TermQ (a::g) b -> TermQ g b
subst1T (V v)           t = Let v t
subst1T (GApp el v u)   t = GApp el v (subst1T u (renameTerm (permute0 . weaken) t))
subst1T (GIf0 el u v c) t = GIf0 el u v (subst1T c (renameTerm (permute0 . weaken) t))
subst1T (Let v u)       t = Let v (subst1T u (renameTerm (permute0 . weaken) t))

subst1V : ValQ g a -> ValQ (a::g) b -> ValQ g b
subst1V (Var el)  t               = renameVal (contract el) t
subst1V  a       (Var Here)       = a
subst1V  a       (Var (There el)) = Var el
subst1V  a       (LamF t)         = LamF $ Let (shiftVal a) (shiftTerm t)
subst1V  a        Zero            = Zero
subst1V  a       (Succ t)         = Succ (subst1V a t)

subst1VT : ValQ g a -> TermQ (a::g) b -> TermQ g b
subst1VT    (Var el)  t                      = renameTerm (contract el) t
subst1VT  a          (V v)                   = V $ subst1V a v
subst1VT  a@(LamF t) (GApp  Here      v c)   = Let a $ subst1T (Let v t) c
                                               --subst1T (Let a $ Let (shiftVal $ subst1V a v) t)
                                               --        (Let (shiftVal a) (shiftTerm c))
subst1VT  a          (GApp (There el) v c)   = GApp el (subst1V a v) (Let (shiftVal a) (shiftTerm c))
subst1VT  a@Zero     (GIf0  Here u v c)      = Let a $ subst1T u c
                                               --subst1T (Let a u) (Let (shiftVal a) (shiftTerm c))
subst1VT  a@(Succ t) (GIf0  Here u v c)      = subst1T (Let (shiftVal t) (shiftTerm v)) (Let (shiftVal a) (shiftTerm c))
subst1VT  a          (GIf0 (There el) u v c) = GIf0 el (Let a u) (Let (shiftVal a) (shiftTerm v)) (Let (shiftVal a) (shiftTerm c))
subst1VT  a          (Let v c)               = Let a (subst1VT v c)

stepQ : TermQ g a -> Maybe (TermQ g a)
stepQ (Let v t) = Just $ subst1VT v t
stepQ _         = Nothing

stepIter : TermQ [] a -> (Nat, TermQ [] a)
stepIter = iterCount stepQ
