module LJ.Q.ES.Term

import Data.List
import Subset
import Iter

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LJ.LambdaC.Term
import LJ.LambdaC.Smallstep

%default total
%access public export

mutual
  data Async : List Ty -> Ty -> Type where
    Val  : RSync g a -> Async g a                                     -- focus/dereliction
    GApp : RSync g a -> Async (b::g) c -> Elem (a~>b) g -> Async g c  -- implication left intro
    Let  : RSync g a -> Async (a::g) b -> Async g b                   -- head cut
    Sub  : Async g a -> Async (a::g) b -> Async g b                   -- mid cut, explicit substitution/beta-redex

  -- cut-free (i.e. not SubV) RSyncs are values
  data RSync : List Ty -> Ty -> Type where
    Var  : Elem a g -> RSync g a                     -- axiom
    Lam  : Async (a::g) b -> RSync g (a~>b)          -- implication right intro
    SubV : RSync g a -> RSync (a::g) b -> RSync g b  -- focused head cut, explicit substitution
    -- no focused mid cut

-- structural rules

mutual
  renameAsync : Subset g d -> Async g a -> Async d a
  renameAsync sub (Val r)       = Val $ renameRSync sub r
  renameAsync sub (GApp r a el) = GApp (renameRSync sub r) (renameAsync (ext sub) a) (sub el)
  renameAsync sub (Let r a)     = Let (renameRSync sub r) (renameAsync (ext sub) a)
  renameAsync sub (Sub r l)     = Sub (renameAsync sub r) (renameAsync (ext sub) l)

  renameRSync : Subset g d -> RSync g a -> RSync d a
  renameRSync sub (Var el)   = Var $ sub el
  renameRSync sub (Lam a)    = Lam (renameAsync (ext sub) a)
  renameRSync sub (SubV r l) = SubV (renameRSync sub r) (renameRSync (ext sub) l)

mutual
  renameMAsync : SubsetM g d -> Async g a -> Maybe (Async d a)
  renameMAsync subm (Val r)       = Val <$> renameMRSync subm r
  renameMAsync subm (GApp r a el) = [| GApp (renameMRSync subm r) (renameMAsync (extM subm) a) (subm el) |]
  renameMAsync subm (Let r a)     = [| Let (renameMRSync subm r) (renameMAsync (extM subm) a) |]
  renameMAsync subm (Sub r l)     = [| Sub (renameMAsync subm r) (renameMAsync (extM subm) l) |]

  renameMRSync : SubsetM g d -> RSync g a -> Maybe (RSync d a)
  renameMRSync subm (Var el)   = Var <$> subm el
  renameMRSync subm (Lam a)    = Lam <$> (renameMAsync (extM subm) a)
  renameMRSync subm (SubV r l) = [| SubV (renameMRSync subm r) (renameMRSync (extM subm) l) |]

shiftAsync : {auto is : IsSubset g d} -> Async g a -> Async d a
shiftAsync {is} = renameAsync (shift is)

shiftRSync : {auto is : IsSubset g d} -> RSync g a -> RSync d a
shiftRSync {is} = renameRSync (shift is)

-- terms from paper

lem1 : Async ((a~>b)::a::g) b
lem1 = GApp (Var $ There Here) (Val $ Var Here) Here

cut4 : Async g a -> RSync (a::g) b -> Async g b
cut4 n = Sub n . Val

cut5 : RSync g a -> RSync (a::g) b -> Async g b
cut5 p q = Val $ SubV p q

IRA : Async (a::g) b -> Async g (a~>b)
IRA = Val . Lam

ILA : Async g a -> Async (b::g) c -> Elem (a~>b) g -> Async g c
ILA n m el = Sub n $ Sub (GApp (Var Here) (Val $ Var Here) (There el)) (shiftAsync m)

-- STLC conversion

mutual
  encodeVal : Val g a -> RSync g a
  encodeVal (Var e) = Var e
  encodeVal (Lam t) = Lam $ encodeTm t

  encodeTm : Tm g a -> Async g a
  encodeTm (V    v                        ) = Val $ encodeVal v
  encodeTm (Let (App (V (Var e)) (V v)) p ) = GApp (encodeVal v) (encodeTm p) e
  encodeTm (Let (App (V (Lam m)) (V v)) p ) = Let (Lam $ encodeTm m) (GApp (shiftRSync $ encodeVal v) (shiftAsync $ encodeTm p) Here)
  encodeTm (Let (App (V  v     )  n   ) p ) = assert_total $
                                              encodeTm $ Let n $ Let (App (V $ shiftVal v) (V $ Var Here)) (shiftTm p)
  encodeTm (Let (App  m           n   ) p ) = assert_total $
                                              encodeTm $ Let m $ Let (App (V $ Var Here) (shiftTm n)) (shiftTm p)
  encodeTm (Let (Let  m           n   ) p ) = assert_total $
                                              encodeTm $ Let m $ Let n (shiftTm p)
  encodeTm (Let (V    v               ) p ) = Let (encodeVal v) (encodeTm p)
  encodeTm (App  m                      n ) = assert_total $
                                              encodeTm $ Let (App m n) (V $ Var Here)

encode : Term g a -> Async g a
encode = encodeTm . encodeLC

mutual
  forgetAsyncC : Async g a -> Tm g a
  forgetAsyncC (Val m)       = V $ forgetRSyncC m
  forgetAsyncC (GApp p m el) = Let (App (V $ Var el) (V $ forgetRSyncC p)) (forgetAsyncC m)
  forgetAsyncC (Let p m)     = Let (V $ forgetRSyncC p) (forgetAsyncC m)
  forgetAsyncC (Sub n m)     = subst1 (forgetAsyncC m) (forgetAsyncC n)

  forgetRSyncC : RSync g a -> Val g a
  forgetRSyncC (Var el)   = Var el
  forgetRSyncC (Lam p)    = Lam $ forgetAsyncC p
  forgetRSyncC (SubV p q) = subst1V (forgetRSyncC q) (forgetRSyncC p)

forget : Async g a -> Term g a
forget = forgetTm . forgetAsyncC

--test : RSync [] (A~>A)
--test = SubV {a=A~>A} (Lam (Let {a=A~>A} (Lam (Val (Var Here))) (Val (Var (There Here))))) (SubV {a=A~>A} (Lam (Val (Var Here))) (Var (There Here)))

{-
resultTm : Async [] (A~>A)
resultTm = Val $ Lam $ Val $ Var Here

testTm0 : Async [] (A~>A)
testTm0 = Let (Lam $ Val $ Var Here) (GApp (Lam $ Val $ Var Here) (Val $ Var Here) Here)

testTm3 : Term [] (A~>A)
testTm3 = (App (App (Lam $ Var Here) (Lam $ Var Here)) (App (Lam $ Var Here) (Lam $ Var Here)))


test3 : Term [] (A~>(A~>A))
test3 = App (Lam $ Lam $ Var $ There Here) (Lam $ Var Here)

  -}