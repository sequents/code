module LJPCF.T.Smallstep

import Data.List
import Iter
import Subset

import Lambda.STLC.Ty
import LJPCF.T.Term
import PCF.Term

%default total
%access public export

-- structural rules

mutual
  renameT : Subset g d -> TermJ g a -> TermJ d a
  renameT s (Var el k)  = Var (s el) (renameS s k)
  renameT s (Lam t)     = Lam (renameT (ext s) t)
  renameT s (Cut t k)   = Cut (renameT s t) (renameS s k)
  renameT s  Zero       = Zero
  renameT s (Succ t)    = Succ $ renameT s t
  renameT s (Fix f)     = assert_total $
                          Fix $ renameT (ext s) f

  renameS : Subset g d -> Spine g a b -> Spine d a b
  renameS s  Nil        = Nil
  renameS s (Cons t k)  = Cons (renameT s t) (renameS s k)
  renameS s (Tst t f k) = assert_total $
                          Tst (renameT s t) (renameT (ext s) f) (renameS s k)
  renameS s (Inc k)     = assert_total $
                          Inc (renameS s k)

shiftTerm : {auto is : IsSubset g d} -> TermJ g a -> TermJ d a
shiftTerm {is} = renameT (shift is)

shiftSpine : {auto is : IsSubset g d} -> Spine g a b -> Spine d a b
shiftSpine {is} = renameS (shift is)

-- substitution

mutual
  subst1T : TermJ (a::g) b -> TermJ g a -> TermJ g b
  subst1T (Var  Here      k) u = Cut u (subst1S k u)
  subst1T (Var (There el) k) u = Var el (subst1S k u)
  subst1T (Lam t)            u = Lam $ assert_total $ subst1T (shiftTerm t) (shiftTerm u) -- (renameT permute0 t) (renameT weaken u)
  subst1T (Cut t k)          u = Cut (subst1T t u) (subst1S k u)
  subst1T  Zero              u = Zero
  subst1T (Succ t)           u = assert_total $
                                 Succ $ subst1T t u
  subst1T (Fix f)            u = assert_total $
                                 Fix $ assert_total $ subst1T (shiftTerm f) (shiftTerm u)

  subst1S : Spine (a::g) b c -> TermJ g a -> Spine g b c
  subst1S  Nil        _ = Nil
  subst1S (Cons t k)  u = Cons (subst1T t u) (subst1S k u)
  subst1S (Tst t f k) u = Tst (subst1T t u) (assert_total $ subst1T (shiftTerm f) (shiftTerm u)) (subst1S k u)
  subst1S (Inc k)     u = Inc $ subst1S k u

-- small-step interpreter / abstract machine!

stepT : TermJ g a -> Res (TermJ g a)
stepT (Cut (Var el k)   m         ) = Step $ Var el (concat k m)
stepT (Cut (Lam t)     (Cons u  k)) = Step $ Cut (subst1T t u) k
stepT (Cut (Lam t)      Nil       ) = Step $ Lam t
stepT (Cut (Cut t k)    m         ) = Step $ Cut t (concat k m)
stepT (Cut  Zero       (Tst t _ k)) = Step $ Cut t k
stepT (Cut (Succ n)    (Tst _ f k)) = Step $ Cut (subst1T f n) k
stepT (Cut  Zero                k ) = Readback $ Cut Zero k
stepT (Cut (Succ t)             k ) = Step $ Cut t (Inc k)
stepT (Cut (Fix t)              k ) = Step $ Cut (subst1T t (Fix t)) k
stepT  _                            = Stuck

readback : TermJ g a -> Maybe (TermJ g a)
readback (Cut t (Inc s)) = Just $ Cut (Succ t) s
readback (Cut t  Nil   ) = Just t
readback  _              = Nothing

stepIter : Term [] a -> (Nat, TermJ [] a)
stepIter = iterCountR stepT readback . encode
