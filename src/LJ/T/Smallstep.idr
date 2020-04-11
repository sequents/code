module LJ.T.Smallstep

import Data.List
import Iter
import Subset

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LJ.T.Term

%default total
%access public export

-- structural rules

mutual
  renameTerm : Subset g d -> TermJ g a -> TermJ d a
  renameTerm sub (Var el k) = Var (sub el) (renameSpine sub k)
  renameTerm sub (Lam t)    = Lam (renameTerm (ext sub) t)
  renameTerm sub (Cut t c)  = Cut (renameTerm sub t) (renameSpine sub c)

  renameSpine : Subset g d -> Spine g a b -> Spine d a b
  renameSpine sub  Nil       = Nil
  renameSpine sub (Cons t c) = Cons (renameTerm sub t) (renameSpine sub c)

shiftTerm : {auto is : IsSubset g d} -> TermJ g a -> TermJ d a
shiftTerm {is} = renameTerm (shift is)

shiftSpine : {auto is : IsSubset g d} -> Spine g a b -> Spine d a b
shiftSpine {is} = renameSpine (shift is)

-- substitution
{-
Subst : List Ty -> List Ty -> Type
Subst g d = {x, a : Ty} -> Elem x g -> Spine d x a -> TermJ d a

ext1 : Subst g d -> Subst g (b::d)
ext1 s el sp = ?wot

exts : Subst g d -> Subst (b::g) (b::d)
exts _  Here      sp = Var Here sp
exts s (There el) sp = (ext1 s) el sp

mutual
  substT : Subst g d -> TermJ g a -> TermJ d a
  substT s (Var el k) = ?wut --s el (substS s k)
  substT s (Lam t)    = Lam $ assert_total $ substT (exts s) t
  substT s (Cut t k)  = Cut (substT s t) (substS s k)

  substS : Subst g d -> Spine g a b -> Spine d a b
  substS s  Nil       = Nil
  substS s (Cons t k) = Cons (substT s t) (substS s k)

Subst1 : TermJ g a -> Subst (a::g) g
Subst1 s  Here      k = Cut s k
Subst1 _ (There el) k = Var el k

subst1TT : TermJ (a::g) b -> TermJ g a -> TermJ g b
subst1TT {a} {g} t s = substT {g=a::g} (Subst1 s) t

subst1SS : Spine (a::g) b c -> TermJ g a -> Spine g b c
subst1SS {a} {g} t s = substS {g=a::g} (Subst1 s) t
-}

mutual
  subst1T : TermJ (a::g) b -> TermJ g a -> TermJ g b
  subst1T (Var  Here      k) u = Cut u (subst1S k u)
  subst1T (Var (There el) k) u = Var el (subst1S k u)
  subst1T (Lam t)            u = Lam $ assert_total $ subst1T (shiftTerm t) (shiftTerm u) -- (renameTerm permute0 t) (renameTerm weaken u)
  subst1T (Cut t k)          u = Cut (subst1T t u) (subst1S k u)

  subst1S : Spine (a::g) b c -> TermJ g a -> Spine g b c
  subst1S  Nil       _ = Nil
  subst1S (Cons t k) u = Cons (subst1T t u) (subst1S k u)

-- small-step interpreter / abstract machine!

stepT : TermJ g a -> Maybe (TermJ g a)
stepT (Cut (Var el k)  m        ) = Just $ Var el (concat k m)
stepT (Cut (Lam t)    (Cons u k)) = Just $ Cut (subst1T t u) k
stepT (Cut (Lam t)     Nil      ) = Just $ Lam t
stepT (Cut (Cut t k)   m        ) = Just $ Cut t (concat k m)
stepT  _                          = Nothing

stepIter : Term [] a -> (Nat, TermJ [] a)
stepIter = iterCount stepT . encode