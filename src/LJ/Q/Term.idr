module LJ.Q.Term

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
    GApp : Elem (a~>b) g -> ValQ g a -> TermQ (b::g) c -> TermQ g c  -- implication left intro, `let x : b = (f : a~>b) (t : a) in u : c`
    Let  : ValQ g a -> TermQ (a::g) b -> TermQ g b                   -- head cut, `let x = t in u`

  -- right-synchronous
  data ValQ : List Ty -> Ty -> Type where
    Var  : Elem a g -> ValQ g a                                      -- axiom
    Lam  : TermQ (a::g) b -> ValQ g (a~>b)                           -- implication right intro

-- structural rules

mutual
  renameTerm : Subset g d -> TermQ g a -> TermQ d a
  renameTerm sub (V r)         = V $ renameVal sub r
  renameTerm sub (GApp el r a) = GApp (sub el) (renameVal sub r) (renameTerm (ext sub) a)
  renameTerm sub (Let r a)     = Let (renameVal sub r) (renameTerm (ext sub) a)

  renameVal : Subset g d -> ValQ g a -> ValQ d a
  renameVal sub (Var el) = Var $ sub el
  renameVal sub (Lam a)  = Lam (renameTerm (ext sub) a)

mutual
  renameMTerm : SubsetM g d -> TermQ g a -> Maybe (TermQ d a)
  renameMTerm subm (V r)         = V <$> renameMVal subm r
  renameMTerm subm (GApp el r a) = [| GApp (subm el) (renameMVal subm r) (renameMTerm (extM subm) a) |]
  renameMTerm subm (Let r a)     = [| Let (renameMVal subm r) (renameMTerm (extM subm) a) |]

  renameMVal : SubsetM g d -> ValQ g a -> Maybe (ValQ d a)
  renameMVal subm (Var el) = Var <$> subm el
  renameMVal subm (Lam a)  = Lam <$> (renameMTerm (extM subm) a)

shiftTerm : {auto is : IsSubset g d} -> TermQ g a -> TermQ d a
shiftTerm {is} = renameTerm (shift is)

shiftVal : {auto is : IsSubset g d} -> ValQ g a -> ValQ d a
shiftVal {is} = renameVal (shift is)

-- STLC conversion

mutual
  encodeVal : Val g a -> ValQ g a
  encodeVal (Var e) = Var e
  encodeVal (Lam t) = Lam $ encodeTm t

  encodeTm : Tm g a -> TermQ g a
  encodeTm (V    v                        ) = V $ encodeVal v
  encodeTm (Let (App (V (Var e)) (V v)) p ) = GApp e (encodeVal v) (encodeTm p)
  encodeTm (Let (App (V (Lam m)) (V v)) p ) = Let (Lam $ encodeTm m) (GApp Here (shiftVal $ encodeVal v) (shiftTerm $ encodeTm p))
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
  forgetTermC (GApp el p m) = Let (App (V $ Var el) (V $ forgetValC p)) (forgetTermC m)
  forgetTermC (Let p m)     = Let (V $ forgetValC p) (forgetTermC m)

  forgetValC : ValQ g a -> Val g a
  forgetValC (Var el)   = Var el
  forgetValC (Lam p)    = Lam $ forgetTermC p

forget : TermQ g a -> Term g a
forget = forgetTm . forgetTermC

-- let f : (*~>*)~>(*~>*) = \x.[x]
--     t : (*~>*) = f (\x.[x])
--  in
-- t
testTm0 : TermQ [] (A~>A)
testTm0 = Let (Lam $ V $ Var Here) $
          GApp Here (Lam $ V $ Var Here) $
          V $ Var Here

-- let f = \x.[x]
--     g = f (\x.[x])
--     t = g (\x.[x])
--  in
-- t
testTm1 : TermQ [] (Imp A A)
testTm1 = Let (Lam $ V $ Var Here) $
          GApp Here (Lam $ V $ Var Here) $
          GApp Here (Lam $ V $ Var Here) $
          V $ Var Here

-- let f = \x.[x]
--     g = f (\x.[x])
--     h = \x.[x]
--     t = h g
--  in
-- t
testTm2 : TermQ [] (Imp A A)
testTm2 = Let (Lam $ V $ Var Here) $
          GApp Here (Lam $ V $ Var Here) $
          Let (Lam $ V $ Var Here) $
          GApp Here (Var $ There Here) $
          V $ Var Here
