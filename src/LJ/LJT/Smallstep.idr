module LJ.LJT.Smallstep

import Data.List
import Subset
import Iter

import Lambda.STLC.Ty
import LJ.LJT.Term

import Lambda.STLC.Term

%default total
%access public export

mutual
  stepA : Async g a -> Maybe (Async g a)

  stepA (Beta (Lam t)    (Cons u k)) = Just $ Beta (Sub u t) k
  stepA (Beta (Lam t)     Nil      ) = Just $ Lam t
  stepA (Beta (Var el k)  m        ) = Just $ Var el (Cat k m)
--stepA (Beta (Beta t k)  m        ) = Just $ Beta t (Cat k m)
  stepA (Beta  k          m        ) = [| Beta (stepA k) (pure m) |] <|> [| Beta (pure k) (stepLS m) |]

  stepA (Sub  u (Lam t)           ) = Just $ Lam $ Sub (shiftAsync u) (shiftAsync t)
  stepA (Sub  u (Var  Here      k)) = Just $ Beta u (SubL u k)
  stepA (Sub  u (Var (There el) k)) = Just $ Var el (SubL u k)
--stepA (Sub  u (Beta k l)        ) = Just $ Beta (Sub u k) (SubL u l)
  stepA (Sub  u  k                ) = [| Sub (stepA u) (pure k) |] <|> [| Sub (pure u) (stepA k) |]

  stepA  _                          = Nothing

  stepLS : LSync g a b -> Maybe (LSync g a b)

  stepLS (Cat  Nil       m) = Just m
  stepLS (Cat (Cons u k) m) = Just $ Cons u (Cat k m)
--stepLS (Cat (Cat k l)  m) = Just $ Cat k (Cat l m)
  stepLS (Cat  k         m) = [| Cat (stepLS k) (pure m) |] <|> [| Cat (pure k) (stepLS m) |]

  stepLS (SubL _  Nil      ) = Just Nil
  stepLS (SubL u (Cons t k)) = Just $ Cons (Sub u t) (SubL u k)
--stepLS (SubL u (Cat k l) ) = Just $ Cat (SubL u k) (SubL u l)
  stepLS (SubL u  k        ) = [| SubL (stepA u) (pure k) |] <|> [| SubL (pure u) (stepLS k) |]

  stepLS  _                   = Nothing

stepIter : Term [] a -> (Nat, Async [] a)
stepIter = iterCount stepA . encode

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
