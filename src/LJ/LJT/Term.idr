module LJ.LJT.Term

import Data.List
import Subset

import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

mutual
  -- cut-free (i.e. not Beta/Sub) Asyncs are values
  data Async : List Ty -> Ty -> Type where
    Var  : Elem a g -> LSync g a b -> Async g b      -- contraction / focus
    Lam  : Async (a::g) b -> Async g (a~>b)          -- implication right intro
    Beta : Async g a -> LSync g a b -> Async g b     -- head cut, beta-redex / generalized application
    Sub  : Async g a -> Async (a::g) b -> Async g b  -- mid cut, term explicit substitution

  data LSync : List Ty -> Ty -> Ty -> Type where
    Nil  : LSync g a a                                   -- axiom
    Cons : Async g a -> LSync g b c -> LSync g (a~>b) c  -- implication left intro
    Cat  : LSync g a b -> LSync g b c -> LSync g a c     -- focused head cut, concatenating contexts
    SubL : Async g a -> LSync (a::g) b c -> LSync g b c  -- focused mid cut, list explicit substitution

-- structural rules

-- TODO for some reason totality checking takes a few minutes here without at least 2 asserts
mutual
  renameAsync : Subset g d -> Async g a -> Async d a
  renameAsync sub (Var el k) = Var (sub el) (renameLSync sub k)
  renameAsync sub (Lam t)    = Lam (renameAsync (ext sub) t)
  renameAsync sub (Beta t c) = Beta (renameAsync sub t) (renameLSync sub c)
  renameAsync sub (Sub t t2) = assert_total $ Sub (renameAsync sub t) (renameAsync (ext sub) t2)

  renameLSync : Subset g d -> LSync g a b -> LSync d a b
  renameLSync sub  Nil       = Nil
  renameLSync sub (Cons t c) = assert_total $ Cons (renameAsync sub t) (renameLSync sub c)
  renameLSync sub (Cat c c2) = Cat (renameLSync sub c) (renameLSync sub c2)
  renameLSync sub (SubL t c) = SubL (renameAsync sub t) (renameLSync (ext sub) c)

shiftAsync : {auto is : IsSubset g d} -> Async g a -> Async d a
shiftAsync {is} = renameAsync (shift is)

shiftLSync : {auto is : IsSubset g d} -> LSync g a b -> LSync d a b
shiftLSync {is} = renameLSync (shift is)

-- STLC embedding

encode : Term g a -> Async g a
encode (Var e)   = Var e Nil
encode (Lam t)   = Lam $ encode t
encode (App t u) = Beta (encode t) (Cons (encode u) Nil)
