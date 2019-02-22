module PCF.Bytecode

import Data.List
import Iter
import Path
import Elem
import Lambda.STLC.Ty
import PCF.Term
import Binary

import Data.Vect

%default total
%access public export

-- typed bytecode

mutual
  data I : (List Ty, Ty) -> (List Ty, Ty) -> Type where
    Access : Elem a g -> I (g,a) (g,a)
    Grab   : I (g,a~>b) (a::g,b) 
    Push   : Control g a -> I (g,b) (g,a~>b)
    Nul    : I (g,A) (g,a)
    Inc    : I (g,A) (g,A)
    Case   : Control g a -> Control (A::g) a -> I (g,a) (g,A)
    Loop   : I (g,a) (a::g,a)
  
  record Control (g : List Ty) (a : Ty) where
    constructor MkCtr
    ec   : List Ty
    et   : Ty
    path : Path I (g,a) (ec, et)
  --Control g a = (d**b**Path I (g,a) (d,b))

infixr 5 +:
(+:) : I (g,a) (d,b) -> Control d b -> Control g a
(+:) i (MkCtr s c p) = MkCtr s c (i::p)

-- translate term into bytecode
  
compile : Term g a -> Control g a
compile {g} {a} (Var e)       = MkCtr g a [Access e]
compile         (Lam t)       = Grab +: compile t
compile         (App {b} t u) = Push {b} (compile u) +: compile t
compile {g}      Zero         = MkCtr g A [Nul]
compile         (Succ t)      = Inc +: compile t
compile         (If0 c t f)   = Case (compile t) (compile f) +: compile c
compile         (Fix t)       = Loop +: compile t

Codec (Control g a) where
  toBuf buf (MkCtr d b p) = do b1 <- toBuf buf d
                               b2 <- toBuf b1 b
                               go b2 (g**a**p)
  where 
    go : Binary -> (s ** c ** Path I (s,c) (d,b)) -> IOE Binary
    go bf (d**b**[]) = pure bf
    go bf (s**c**Access e::_) = do b1 <- toBuf bf (the Bits8 10)
                                   toBuf b1 (toIntegerNat $ elem2Nat e)
    go bf (s**e~>f**Grab::q) = assert_total $ 
                               do b1 <- toBuf buf (the Bits8 11) 
                                  go b1 (e::s ** f ** q) 
    go bf (s**c**Push {a=e} u::q) = assert_total $ 
                                    do b1 <- toBuf bf (the Bits8 12) 
--                                       b2 <- toBuf b1 s
--                                       b3 <- toBuf b2 e
                                       b4 <- toBuf b1 u
                                       b5 <- toBuf b4 (the Bits8 13) 
                                       go b5 (s ** e~>c ** q) 
    go bf (s**A**Nul::_) = toBuf bf (the Bits8 14)
    go bf (s**A**Inc::q) = assert_total $ 
                           do b1 <- toBuf bf (the Bits8 15)
                              go b1 (s**A**q)  
    go bf (s**c**Case t f::q) = assert_total $ 
                                do b1 <- toBuf bf (the Bits8 16) 
--                                   b1 <- toBuf buf g
--                                   b2 <- toBuf b1 a
                                   b2 <- toBuf b1 t
                                   b3 <- toBuf b2 (the Bits8 17) 
                                   b4 <- toBuf b3 f
                                   b5 <- toBuf b4 (the Bits8 18) 
                                   go b5 (s ** A ** q) 
    go bf (s**c**Loop::q) = assert_total $ 
                            do b1 <- toBuf bf (the Bits8 19)
                               go b1 (c::s**c**q)  
                              
  fromBuf buf = do (d, b1) <- fromBuf buf {a=List Ty}
                   (b, b2) <- fromBuf b1 {a=Ty}
                   ((s**c**p), b3) <- go {d} {b} b2 
                   case (decEq g s, decEq a c) of 
                     (Yes Refl, Yes Refl) => pure (MkCtr d b p, b3)
                     (_, _) => throw "type mismatch for toplevel path"
  where
    go : Binary -> IOE ((s ** c ** Path I (s,c) (d,b)), Binary)

{-

    fromBuf buf = do (tag, b1) <- fromBuf buf {a=Bits8}
                     case tag of 
                       10 => do (g, b2) <- fromBuf b1 {a=List Ty}
                                (a, b3) <- fromBuf b2 {a=Ty}   
                                (n, b4) <- fromBuf b2 {a=Integer}
                                case nat2Elem {a} {g} (fromIntegerNat n) of 
                                  Just e => pure $ ((g,a) ** (g,a) ** Bytecode.Access e)
                                  Nothing => throw "Corrupt elem index"
                       _ => throw "unknown tag"
  Codec (Control g a) where
    toBuf buf c = ?wot
    fromBuf buf = ?wot2
  -}