module LJ.T.ES.Smallstep

import Data.List
import Subset
import Iter

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LJ.T.ES.Term

%default total
%access public export

-- structural rules

-- TODO for some reason totality checking takes a few minutes here without at least 2 asserts
mutual
  renameTerm : Subset g d -> TermJ g a -> TermJ d a
  renameTerm sub (Var el k) = Var (sub el) (renameSpine sub k)
  renameTerm sub (Lam t)    = Lam (renameTerm (ext sub) t)
  renameTerm sub (Cut t c)  = Cut (renameTerm sub t) (renameSpine sub c)
  renameTerm sub (Sub t t2) = assert_total $
                              Sub (renameTerm sub t) (renameTerm (ext sub) t2)

  renameSpine : Subset g d -> Spine g a b -> Spine d a b
  renameSpine sub  Nil       = Nil
  renameSpine sub (Cons t c) = assert_total $
                               Cons (renameTerm sub t) (renameSpine sub c)
  renameSpine sub (Cat c c2) = Cat (renameSpine sub c) (renameSpine sub c2)
  renameSpine sub (SubL t c) = SubL (renameTerm sub t) (renameSpine (ext sub) c)

shiftTerm : {auto is : IsSubset g d} -> TermJ g a -> TermJ d a
shiftTerm {is} = renameTerm (shift is)

shiftSpine : {auto is : IsSubset g d} -> Spine g a b -> Spine d a b
shiftSpine {is} = renameSpine (shift is)

stepT : TermJ g a -> Maybe (TermJ g a)

stepT (Cut (Var el k)                  m                         ) = Just $ Var el (Cat k m)
stepT (Cut (Lam t)                    (Cons u k)                 ) = Just $ Cut (Sub u t) k
stepT (Cut (Lam t)                     Nil                       ) = Just $ Lam t
stepT (Cut (Cut t k)                   m                         ) = Just $ Cut t (Cat k m)

stepT (Cut (Sub u (Var  Here      k))  m                         ) = Just $ Cut u (Cat (SubL u k) m) --(Cut u (SubL u k)) m
stepT (Cut (Sub u (Var (There el) k))  m                         ) = Just $ Var el (Cat (SubL u k) m) --Cut (Var el (SubL u k)) m
stepT (Cut (Sub u (Lam t)           )  m                         ) = Just $ Cut (Lam $ Sub (shiftTerm u) (shiftTerm t)) m
stepT (Cut (Sub u (Cut k l)         )  m                         ) = Just $ Cut (Sub u k) (Cat (SubL u l) m) --(Cut (Sub u k) (SubL u l)) m

stepT (Cut  t                         (Cat  Nil                m)) = Just $ Cut t  m
stepT (Cut  t                         (Cat (Cons u k)          m)) = Just $ Cut t (Cons u (Cat k m))
stepT (Cut  t                         (Cat (Cat k l)           m)) = Just $ Cut t (Cat k (Cat l m))

stepT (Cut  t                         (Cat (SubL _  Nil      ) m)) = Just $ Cut t  m --(Cat Nil m)
stepT (Cut  t                         (Cat (SubL u (Cons s k)) m)) = Just $ Cut t (Cat (Cons (Sub u s) (SubL u k)) m)
stepT (Cut  t                         (Cat (SubL u (Cat k l) ) m)) = Just $ Cut t (Cat (SubL u k) (Cat (SubL u l) m)) --(Cat (Cat (SubL u k) (SubL u l)) m)

stepT  _                                                            = Nothing

stepIter : Term [] a -> (Nat, TermJ [] a)
stepIter = iterCount stepT . encode

-- tests

private
test1 : stepIter TestTm0 = (4, encode ResultTm)
test1 = Refl

private
test2 : stepIter TestTm1 = (10, encode ResultTm)
test2 = Refl

private
test3 : stepIter TestTm2 = (10, encode ResultTm)
test3 = Refl
