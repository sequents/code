module LJ.Q.PCF.Term

import Data.List
import Subset
import Iter

import Lambda.STLC.Ty
import Lambda.PCF.Term
import LambdaC.PCF.Term
--import LambdaC.Smallstep

%default total
%access public export

mutual
  -- asynchronous
  data TermQ : List Ty -> Ty -> Type where
    V    : ValQ g a -> TermQ g a                                     -- focus/dereliction
    GApp : Elem (a~>b) g -> ValQ g a -> TermQ (b::g) c -> TermQ g c  -- implication left intro, `let x : b = (f : a~>b) (t : a) in u : c`
    Let  : ValQ g a -> TermQ (a::g) b -> TermQ g b                   -- head cut, `let x = t in u`
    GIf0 : Elem A g -> TermQ g a -> TermQ (A::g) a -> TermQ (a::g) b -> TermQ g b
    LetF : TermQ (a::g) a -> TermQ (a::g) b -> TermQ g b

  -- right-synchronous
  data ValQ : List Ty -> Ty -> Type where
    Var  : Elem a g -> ValQ g a                                      -- axiom
    Lam  : TermQ (a::g) b -> ValQ g (a~>b)                           -- implication right intro
    Zero : ValQ g A
    Succ : TermQ g A -> ValQ g A

-- structural rules

mutual
  renameTerm : Subset g d -> TermQ g a -> TermQ d a
  renameTerm sub (V v)           = V $ renameVal sub v
  renameTerm sub (GApp el v t)   = GApp (sub el) (renameVal sub v) (renameTerm (ext sub) t)
  renameTerm sub (Let v t)       = Let (renameVal sub v) (renameTerm (ext sub) t)
  renameTerm sub (GIf0 el t f u) = GIf0 (sub el) (renameTerm sub t) (renameTerm (ext sub) f) (renameTerm (ext sub) u)
  renameTerm sub (LetF t u)      = LetF (renameTerm (ext sub) t) (renameTerm (ext sub) u)

  renameVal : Subset g d -> ValQ g a -> ValQ d a
  renameVal sub (Var el)    = Var $ sub el
  renameVal sub (Lam t)     = Lam $ renameTerm (ext sub) t
  renameVal sub  Zero       = Zero
  renameVal sub (Succ t)    = Succ $ renameTerm sub t

--mutual
--  renameMTerm : SubsetM g d -> TermQ g a -> Maybe (TermQ d a)
--  renameMTerm subm (V r)         = V <$> renameMVal subm r
--  renameMTerm subm (GApp el r a) = [| GApp (subm el) (renameMVal subm r) (renameMTerm (extM subm) a) |]
--  renameMTerm subm (Let r a)     = [| Let (renameMVal subm r) (renameMTerm (extM subm) a) |]
--
--  renameMVal : SubsetM g d -> ValQ g a -> Maybe (ValQ d a)
--  renameMVal subm (Var el) = Var <$> subm el
--  renameMVal subm (Lam a)  = Lam <$> (renameMTerm (extM subm) a)

shiftTerm : {auto is : IsSubset g d} -> TermQ g a -> TermQ d a
shiftTerm {is} = renameTerm (shift is)

shiftVal : {auto is : IsSubset g d} -> ValQ g a -> ValQ d a
shiftVal {is} = renameVal (shift is)
{-
-- PCF conversion

mutual
  encodeVal : Val g a -> ValQ g a
  encodeVal (Var e)     = Var e
  encodeVal (Lam t)     = Lam $ encodeTm t
  encodeVal  Zero       = Zero
  encodeVal (Succ n)    = Succ $ encodeTm n

  encodeTm : Tm g a -> TermQ g a
  encodeTm (V    v                       ) = V $ encodeVal v
  encodeTm (Let (App (V (Var e)) (V v)) p) = GApp e (encodeVal v) (encodeTm p)
  encodeTm (Let (App (V (Lam m)) (V v)) p) = Let (Lam $ encodeTm m) (GApp Here (shiftVal $ encodeVal v) (shiftTerm $ encodeTm p))
  encodeTm (Let (App (V  v     )  n   ) p) = assert_total $
                                             encodeTm $ Let n $ Let (App (V $ shiftVal v) (V $ Var Here)) (shiftTm p)
  encodeTm (Let (App  m           n   ) p) = assert_total $
                                             encodeTm $ Let m $ Let (App (V $ Var Here) (shiftTm n)) (shiftTm p)
  encodeTm (Let (Let  m           n   ) p) = assert_total $
                                             encodeTm $ Let m $ Let n (shiftTm p)
  encodeTm (Let (V    v               ) p) = Let (encodeVal v) (encodeTm p)
  encodeTm (Let (If0 p t f)             u) = GIf0 ?wat ?wat1 ?wat2 (encodeTm u)
  encodeTm (Let (Fix t)                 u) = LetF (encodeTm t) (encodeTm u)
  encodeTm (App  m                      n) = assert_total $
                                             encodeTm $ Let (App m n) (V $ Var Here)
  encodeTm (If0  p t f                   ) = assert_total $
                                             encodeTm $ Let (If0 p t f) (V $ Var Here)
  encodeTm (Fix  t                       ) = assert_total $
                                             encodeTm $ Let (Fix t) (V $ Var Here)


encode : Term g a -> TermQ g a
encode = encodeTm . encodePCF

mutual
  forgetTermC : TermQ g a -> Tm g a
  forgetTermC (V m)         = V $ forgetValC m
  forgetTermC (GApp el p m) = Let (App (V $ Var el) (V $ forgetValC p)) (forgetTermC m)
  forgetTermC (Let p m)     = Let (V $ forgetValC p) (forgetTermC m)

  forgetValC : ValQ g a -> Val g a
  forgetValC (Var el)    = Var el
  forgetValC (Lam p)     = Lam $ forgetTermC p
  forgetValC  Zero       = Zero
  forgetValC (Succ n)    = Succ $ forgetTermC n
  forgetValC (If0 p t f) = If0 (forgetTermC p) (forgetTermC t) (forgetTermC f)
  forgetValC (Fix f)     = Fix $ forgetTermC f

forget : TermQ g a -> Term g a
forget = forgetTm . forgetTermC
  -}
-- let f : (*~>*)~>(*~>*) = \x.[x]
--     t : (*~>*) = f (\x.[x])
-- in [t]
testTm0 : TermQ [] (A~>A)
testTm0 = Let (Lam $ V $ Var Here) $
          GApp Here (Lam $ V $ Var Here) $
          V $ Var Here

-- let f = \x.[x]
--     g = f (\x.[x])
--     t = g (\x.[x])
-- in [t]
testTm1 : TermQ [] (Imp A A)
testTm1 = Let (Lam $ V $ Var Here) $
          GApp Here (Lam $ V $ Var Here) $
          GApp Here (Lam $ V $ Var Here) $
          V $ Var Here

-- let f = \x.[x]
--     g = f (\x.[x])
--     h = \x.[x]
--     t = h g
-- in [t]
testTm2 : TermQ [] (Imp A A)
testTm2 = Let (Lam $ V $ Var Here) $
          GApp Here (Lam $ V $ Var Here) $
          Let (Lam $ V $ Var Here) $
          GApp Here (Var $ There Here) $
          V $ Var Here

fromN : Nat -> ValQ g A
fromN  Z    = Zero
fromN (S n) = Succ $ V $ fromN n

-- let f = \x.[Z]
--     fix w = [S [w]]
--     t = f w
-- in [t]
bam : TermQ [] A
bam = Let (Lam $ V Zero) $
      LetF (V $ Succ $ V $ Var Here) $
      GApp (There Here) (Var Here) $
      V $ Var Here

--plusN : TermQ g (A~>A~>A)
--plusN = LetF (V $ Lam $ V $ Lam $ GIf0 (There Here)
--                                       (V $ Var Here)
--                                       (GApp (There $ There $ There Here) (Var Here) $
--                                        GApp Here (Var $ There $ There Here) $
--                                        V $ Succ $ V $ Var Here)
--                                       (V $ Var Here))
--             (V $ Var Here)

-- let fix add = \x.[\y.let if r = x
--                                 then [y]
--                                 else \z.let g = add z
--                                             t = g y
--                                         in [S [t]]
--                      in [r]]
--     g = add 2
--     t = g 2
-- in [t]
twotwoN : TermQ [] A
twotwoN = LetF (V $ Lam $ V $ Lam $ GIf0 (There Here)
                                         (V $ Var Here)
                                         (GApp (There $ There $ There Here) (Var Here) $
                                          GApp Here (Var $ There $ There Here) $
                                          V $ Succ $ V $ Var Here)
                                         (V $ Var Here)) $
          GApp Here (fromN 2) $
          GApp Here (fromN 2) $
          V $ Var Here

--let fix sub = \x.[\y.let if r = y
--                                then [x]
--                                else \z.let if s = x
--                                                   then [Z]
--                                                   else \w.let g = sub w
--                                                               t = g z
--                                                           in [t]
--                                        in [s]
--                     in [r]]
--in [sub]
minusN : TermQ g (A~>A~>A)
minusN = LetF (V $ Lam $ V $ Lam $ GIf0 Here
                                        (V $ Var $ There Here)
                                        (GIf0 (There $ There Here)
                                              (V Zero)
                                              (GApp (There $ There $ There $ There Here) (Var Here) $
                                               GApp Here (Var $ There $ There Here) $
                                               V $ Var Here)
                                              (V $ Var Here))
                                        (V $ Var Here)) $
         V $ Var Here


