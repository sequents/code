module Lambda.PCF.V.LamF.Smallstep

import Data.List
import Subset
import Iter
import Lambda.STLC.Ty
import Lambda.PCF.V.LamF.Term

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
  substVV s (LamF c) = LamF $ substVC (extsV $ extsV s) c

  substVC : SubstV g d -> Comp g a -> Comp d a
  substVC s (V v)       = V $ substVV s v
  substVC s (App v w)   = App (substVC s v) (substVC s w)
  substVC s (If0 v c d) = If0 (substVC s v) (substVC s c) (substVC (extsV s) d)

sub1 : Val g a -> SubstV (a::g) g
sub1 v  Here      = v
sub1 v (There el) = Var el

subst1VV : Val g a -> Val (a::g) b -> Val g b
subst1VV v w = substVV (sub1 v) w

subst1VC : Val g a -> Comp (a::g) b -> Comp g b
subst1VC v c = substVC (sub1 v) c

stepV : Comp g a -> Maybe (Comp g a)
stepV (App (V (LamF t)) (V u)) = Just $ subst1VC (LamF t) $
                                        subst1VC (renameV weaken u) t
stepV (App (V t       )    u ) = App (V t) <$> (stepV u)
stepV (App    t            u ) = [| App (stepV t) (pure u) |]
stepV (If0 (V  Zero   ) t f)   = Just t
stepV (If0 (V (Succ v)) t f)   = Just $ subst1VC v f
stepV (If0  v           t f)   = (\q => If0 q t f) <$> stepV v
stepV  _                       = Nothing

stepIterV : Comp g a -> (Nat, Comp g a)
stepIterV = iterCount stepV
