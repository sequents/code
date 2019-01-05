module Lambda.CEK

import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

{-
mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : Tm g a -> Env g -> Clos a

data Frame : Ty -> Type where
  Fun : Tm g a -> Env g -> Frame a
  Arg : Clos a -> Frame a
 
data Stack : Ty -> Ty -> Type where
  NS : Stack a a
  CS : Frame a -> Stack b c -> Stack (a~>b) c

--data Stack : Ty -> Ty -> Type where
--  NS : Stack a a
--  FS : Tm g a -> Env g -> Stack b c -> Stack a c
--  AS : Clos a -> Stack b c -> Stack a c

data State : List Ty -> Ty -> Ty -> Type where
  L : Tm g a -> Env g -> Stack a b -> State g a b
  R : Clos a -> Stack a b -> State g a b

step : State g a b -> Maybe (d ** c ** h ** State d c h)
step {g=a::g}             {b} (L (Vr  Here)      (v::_)                 s ) = Just (   g ** a ** b   ** R  v            s)
step {g=_::g} {a}         {b} (L (Vr (There el)) (_::e)                 s ) = Just (   g ** a ** b  ** L (Vr el)    e  s)
step {g}      {a=Imp a x} {b} (L (Lm t)              e                  s ) = Just (   g ** Imp a x ** b ** R (Cl (Lm t) e) s)
step {g}      {a}         (L (Ap {a=x} t u)      e                  s ) = Just (   g ** x  ** b     ** L  u         e  ?wat)
step          {a=Imp a x} (R (Cl       (Lm t)    e) (CS (Fun {g=j} t1 e1) s)) = ?wat4 --Just (   j ** a       ** L t1         e1 ?wat1)
step {g}      {a=Imp a x} (R (Cl {g=j} (Lm t)    e) (CS (Arg v)           s)) = ?wat5 --Just (a::j ** x       ** L t      (v::e) s)
step _ = Nothing
-}
