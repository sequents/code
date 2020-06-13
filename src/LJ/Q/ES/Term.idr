module LJ.Q.ES.Term

import Data.List
import Subset
import Iter

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LambdaC.Term
import LambdaC.Smallstep

%default total
%access public export

mutual
  -- asynchronous
  data TermQ : List Ty -> Ty -> Type where
    V    : ValQ g a -> TermQ g a                                     -- focus/dereliction
    GApp : ValQ g a -> TermQ (b::g) c -> Elem (a~>b) g -> TermQ g c  -- implication left intro
    Let  : ValQ g a -> TermQ (a::g) b -> TermQ g b                   -- head cut
    Sub  : TermQ g a -> TermQ (a::g) b -> TermQ g b                  -- mid cut, explicit substitution/beta-redex

  -- right-synchronois, cut-free (i.e. not SubV) ValQs are values
  data ValQ : List Ty -> Ty -> Type where
    Var  : Elem a g -> ValQ g a                   -- axiom
    Lam  : TermQ (a::g) b -> ValQ g (a~>b)        -- implication right intro
    SubV : ValQ g a -> ValQ (a::g) b -> ValQ g b  -- focused head cut, explicit substitution
    -- no focused mid cut

-- structural rules

mutual
  renameTerm : Subset g d -> TermQ g a -> TermQ d a
  renameTerm sub (V r)         = V $ renameVal sub r
  renameTerm sub (GApp r a el) = GApp (renameVal sub r) (renameTerm (ext sub) a) (sub el)
  renameTerm sub (Let r a)     = Let (renameVal sub r) (renameTerm (ext sub) a)
  renameTerm sub (Sub r l)     = Sub (renameTerm sub r) (renameTerm (ext sub) l)

  renameVal : Subset g d -> ValQ g a -> ValQ d a
  renameVal sub (Var el)   = Var $ sub el
  renameVal sub (Lam a)    = Lam (renameTerm (ext sub) a)
  renameVal sub (SubV r l) = SubV (renameVal sub r) (renameVal (ext sub) l)

mutual
  renameMTerm : SubsetM g d -> TermQ g a -> Maybe (TermQ d a)
  renameMTerm subm (V r)         = V <$> renameMVal subm r
  renameMTerm subm (GApp r a el) = [| GApp (renameMVal subm r) (renameMTerm (extM subm) a) (subm el) |]
  renameMTerm subm (Let r a)     = [| Let (renameMVal subm r) (renameMTerm (extM subm) a) |]
  renameMTerm subm (Sub r l)     = [| Sub (renameMTerm subm r) (renameMTerm (extM subm) l) |]

  renameMVal : SubsetM g d -> ValQ g a -> Maybe (ValQ d a)
  renameMVal subm (Var el)   = Var <$> subm el
  renameMVal subm (Lam a)    = Lam <$> (renameMTerm (extM subm) a)
  renameMVal subm (SubV r l) = [| SubV (renameMVal subm r) (renameMVal (extM subm) l) |]

shiftTerm : {auto is : IsSubset g d} -> TermQ g a -> TermQ d a
shiftTerm {is} = renameTerm (shift is)

shiftVal : {auto is : IsSubset g d} -> ValQ g a -> ValQ d a
shiftVal {is} = renameVal (shift is)

-- terms from paper

lem1 : TermQ ((a~>b)::a::g) b
lem1 = GApp (Var $ There Here) (V $ Var Here) Here

cut4 : TermQ g a -> ValQ (a::g) b -> TermQ g b
cut4 n = Sub n . V

cut5 : ValQ g a -> ValQ (a::g) b -> TermQ g b
cut5 p q = V $ SubV p q

IRA : TermQ (a::g) b -> TermQ g (a~>b)
IRA = V . Lam

ILA : TermQ g a -> TermQ (b::g) c -> Elem (a~>b) g -> TermQ g c
ILA n m el = Sub n $ Sub (GApp (Var Here) (V $ Var Here) (There el)) (shiftTerm m)

-- STLC conversion

mutual
  encodeVal : Val g a -> ValQ g a
  encodeVal (Var e) = Var e
  encodeVal (Lam t) = Lam $ encodeTm t

  encodeTm : Tm g a -> TermQ g a
  encodeTm (V    v                        ) = V $ encodeVal v
  encodeTm (Let (App (V (Var e)) (V v)) p ) = GApp (encodeVal v) (encodeTm p) e
  encodeTm (Let (App (V (Lam m)) (V v)) p ) = Let (Lam $ encodeTm m) (GApp (shiftVal $ encodeVal v) (shiftTerm $ encodeTm p) Here)
  encodeTm (Let (App (V  v     )  n   ) p ) = assert_total $
                                              encodeTm $ Let n $ Let (App (V $ shiftVal v) (V $ Var Here)) (shiftTm p)
  encodeTm (Let (App  m           n   ) p ) = assert_total $
                                              encodeTm $ Let m $ Let (App (V $ Var Here) (shiftTm n)) (shiftTm p)
  encodeTm (Let (Let  m           n   ) p ) = assert_total $
                                              encodeTm $ Let m $ Let n (shiftTm p)
  encodeTm (Let (V    v               ) p ) = Let (encodeVal v) (encodeTm p)
  encodeTm (App  m                      n ) = assert_total $
                                              encodeTm $ Let (App m n) (V $ Var Here)

encode : Term g a -> TermQ g a
encode = encodeTm . encodeLC

mutual
  forgetTermC : TermQ g a -> Tm g a
  forgetTermC (V m)         = V $ forgetValC m
  forgetTermC (GApp p m el) = Let (App (V $ Var el) (V $ forgetValC p)) (forgetTermC m)
  forgetTermC (Let p m)     = Let (V $ forgetValC p) (forgetTermC m)
  forgetTermC (Sub n m)     = subst1 (forgetTermC m) (forgetTermC n)

  forgetValC : ValQ g a -> Val g a
  forgetValC (Var el)   = Var el
  forgetValC (Lam p)    = Lam $ forgetTermC p
  forgetValC (SubV p q) = subst1V (forgetValC q) (forgetValC p)

forget : TermQ g a -> Term g a
forget = forgetTm . forgetTermC

--test : ValQ [] (A~>A)
--test = SubV {a=A~>A} (Lam (Let {a=A~>A} (Lam (V (Var Here))) (V (Var (There Here))))) (SubV {a=A~>A} (Lam (V (Var Here))) (Var (There Here)))

{-
resultTm : TermQ [] (A~>A)
resultTm = V $ Lam $ V $ Var Here

testTm0 : TermQ [] (A~>A)
testTm0 = Let (Lam $ V $ Var Here) (GApp (Lam $ V $ Var Here) (V $ Var Here) Here)

testTm3 : Term [] (A~>A)
testTm3 = (App (App (Lam $ Var Here) (Lam $ Var Here)) (App (Lam $ Var Here) (Lam $ Var Here)))


test3 : Term [] (A~>(A~>A))
test3 = App (Lam $ Lam $ Var $ There Here) (Lam $ Var Here)

  -}