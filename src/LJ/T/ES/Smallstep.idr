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

mutual
  stepT : TermJ g a -> Maybe (TermJ g a)

  stepT (Cut (Var el k)  m        ) = Just $ Var el (Cat k m)
  stepT (Cut (Lam t)    (Cons u k)) = Just $ Cut (Sub u t) k
  stepT (Cut (Lam t)     Nil      ) = Just $ Lam t
--stepT (Cut (Cut t k)   m        ) = Just $ Cut t (Cat k m)
  stepT (Cut  k          m        ) = [| Cut (stepT k) (pure m) |] <|> [| Cut (pure k) (stepS m) |]

  stepT (Sub  u (Var  Here      k)) = Just $ Cut u (SubL u k)
  stepT (Sub  u (Var (There el) k)) = Just $ Var el (SubL u k)
  stepT (Sub  u (Lam t)           ) = Just $ Lam $ Sub (shiftTerm u) (shiftTerm t)
--stepT (Sub  u (Cut k l)         ) = Just $ Cut (Sub u k) (SubL u l)
  stepT (Sub  u  k                ) = [| Sub (stepT u) (pure k) |] <|> [| Sub (pure u) (stepT k) |]

  stepT  _                          = Nothing

  stepS : Spine g a b -> Maybe (Spine g a b)

  stepS (Cat  Nil       m) = Just m
  stepS (Cat (Cons u k) m) = Just $ Cons u (Cat k m)
--stepS (Cat (Cat k l)  m) = Just $ Cat k (Cat l m)
  stepS (Cat  k         m) = [| Cat (stepS k) (pure m) |] <|> [| Cat (pure k) (stepS m) |]

  stepS (SubL _  Nil      ) = Just Nil
  stepS (SubL u (Cons t k)) = Just $ Cons (Sub u t) (SubL u k)
--stepS (SubL u (Cat k l) ) = Just $ Cat (SubL u k) (SubL u l)
  stepS (SubL u  k        ) = [| SubL (stepT u) (pure k) |] <|> [| SubL (pure u) (stepS k) |]

  stepS  _                   = Nothing

stepIter : Term [] a -> (Nat, TermJ [] a)
stepIter = iterCount stepT . encode

-- tests

private
test1 : stepIter TestTm0 = (5, encode ResultTm)
test1 = Refl

private
test2 : stepIter TestTm1 = (10, encode ResultTm)
test2 = Refl

private
test3 : stepIter TestTm2 = (10, encode ResultTm)
test3 = Refl
