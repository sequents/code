module Lambda.PCF.V.Mod.Smallstep

import Data.List
import Subset
import Iter
import Lambda.PCF.V.Mod.Term

%default total

SubstV : List Ty -> List Ty -> Type
SubstV g d = {x : Ty} -> Elem x g -> Val d x

extsV : SubstV g d -> SubstV (b::g) (b::d)
extsV _  Here      = Var Here
extsV s (There el) = renameV There (s el)

mutual
  substVV : SubstV g d -> Val g a -> Val d a
  substVV s (Var el) = s el
  substVV s  Zero    = Zero
  substVV s (Succ v) = Succ $ substVV s v
  substVV s (Lam c)  = Lam $ substVC (extsV s) c
  substVV s (Fix c)  = Fix $ substVC (extsV s) c
  substVV s (Wrap c) = Wrap $ substVC s c

  substVC : SubstV g d -> Comp g a -> Comp d a
  substVC s (V v)       = V $ substVV s v
  substVC s (App v w)   = App (substVV s v) (substVV s w)
  substVC s (If0 v c d) = If0 (substVV s v) (substVC s c) (substVC (extsV s) d)
  substVC s (Bnd v c)   = Bnd (substVV s v) (substVC (extsV s) c)

sub1 : Val g a -> SubstV (a::g) g
sub1 v  Here      = v
sub1 v (There el) = Var el

subst1VV : Val g a -> Val (a::g) b -> Val g b
subst1VV v w = substVV (sub1 v) w

subst1VC : Val g a -> Comp (a::g) b -> Comp g b
subst1VC v c = substVC (sub1 v) c

stepV : Comp g a -> Maybe (Comp g a)
stepV (App (Lam c) v)      = Just $ subst1VC v c
stepV (If0  Zero    t f)   = Just t
stepV (If0 (Succ v) t f)   = Just $ subst1VC v f
stepV (Bnd (Fix c) d)      = Just $ Bnd (Wrap $ subst1VC (Fix c) c) d
stepV (Bnd (Wrap (V v)) d) = Just $ subst1VC v d
stepV (Bnd (Wrap c) d)     = [| Bnd (Wrap <$> stepV c) (pure d) |]
stepV  _                   = Nothing

stepIterV : Comp g a -> (Nat, Comp g a)
stepIterV = iterCount stepV
