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
    Nul    : I (g,A) (g,A)
    Inc    : I (g,A) (g,A)
    Case   : Control g a -> Control (A::g) a -> I (g,a) (g,A)
    Loop   : I (g,a) (a::g,a)
  
  record Control (g : List Ty) (a : Ty) where
    constructor MkCtr
    ec   : List Ty
    et   : Ty
    path : Path I (g,a) (ec, et)

Show (Control g a) where
  show (MkCtr d b p) = "{ " ++ show g ++ " |- " ++ show a ++ " } " 
                       ++ go g a p {w=d} {z=b}
                       ++ "{ " ++ show d ++ " |- " ++ show b ++ " }"
    where
    go : (s : List Ty) -> (c : Ty) -> Path I (s,c) (w,z) -> String
    go w z      []                = ""
    go s c      (Access e::q)     = "ACC" ++ show (elem2Nat e) ++ " " ++ go s c q
    go s (e~>f) (Grab::q)         = "GRB " ++ go (e::s) f q
    go s c      (Push {a=e} u::q) = "PSH <" ++ show u ++ "> " ++ go s (e~>c) q
    go s A      (Nul::q)          = "NUL " ++ go s A q
    go s A      (Inc::q)          = "INC " ++ go s A q
    go s c      (Case t f::q)     = "CAS <" ++ show t ++ "> <" ++ show f ++ "> " ++ go s A q
    go s c      (Loop::q)         = "LOP " ++ go (c::s) c q
    
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
                               go b2 g a p {w=d} {z=b}
    where 
    go : Binary -> (s : List Ty) -> (c : Ty) -> Path I (s,c) (w,z) -> IOE Binary
    go bf w  z     []                = toBuf bf (the Bits8 30)
    go bf s  c     (Access e::q)     = assert_total $ 
                                       do b1 <- toBuf bf (the Bits8 20)
                                          b2 <- toBuf b1 (toIntegerNat $ elem2Nat e)
                                          go b2 s c q
    go bf s (e~>f) (Grab::q)         = assert_total $ 
                                       do b1 <- toBuf bf (the Bits8 21) 
                                          go b1 (e::s) f q
    go bf s  c     (Push {a=e} u::q) = assert_total $ 
                                       do b1 <- toBuf bf (the Bits8 22) 
                                          b2 <- toBuf b1 e
                                          b3 <- toBuf b2 u
                                          go b3 s (e~>c) q
    go bf s  A     (Nul::q)          = assert_total $ 
                                       do b1 <- toBuf bf (the Bits8 23)
                                          go b1 s A q
    go bf s  A     (Inc::q)          = assert_total $ 
                                       do b1 <- toBuf bf (the Bits8 24)
                                          go b1 s A q
    go bf s  c     (Case t f::q)     = assert_total $ 
                                       do b1 <- toBuf bf (the Bits8 25) 
                                          b2 <- toBuf b1 t
                                          b3 <- toBuf b2 f
                                          go b3 s A q
    go bf s  c     (Loop::q)         = assert_total $ 
                                       do b1 <- toBuf bf (the Bits8 26)
                                          go b1 (c::s) c q
                              
  fromBuf buf = do (d, b1) <- fromBuf buf {a=List Ty}
                   (b, b2) <- fromBuf b1 {a=Ty}
                   (tag, b3) <- fromBuf b2 {a=Bits8}
                   ((s**c**p), b4) <- go b3 tag g a
                   case (decEq d s, decEq b c) of 
                     (Yes Refl, Yes Refl) => pure (MkCtr d b p, b4)
                     (_, _) => throw $ "type mismatch at path endpoint: expected " ++ show d ++ "|-" ++ show b 
                                    ++ ", got " ++ show s ++ "|-" ++ show c
    where
    go : Binary -> Bits8 -> (s : List Ty) -> (c : Ty) -> IOE ((d**b**Path I (s,c) (d,b)), Binary)
    go bf 20 s  c        = do (n, b1) <- fromBuf bf {a=Integer}
                              case indexElem (fromIntegerNat n) s of 
                                Just (x ** e) => 
                                   case decEq c x of  
                                    Yes Refl => do (tag, b2) <- fromBuf b1 {a=Bits8}
                                                   ((d**b**p), b3) <- assert_total $ go b2 tag s c
                                                   pure ((d**b**Access e::p), b3)
                                    No _ => throw "type mismatch in path"                          
                                Nothing => throw "elem out of bounds"
    go bf 21 s (Imp c e) = do (tag, b1) <- fromBuf bf {a=Bits8}
                              ((d**b**p), b2) <- go b1 tag (c::s) e
                              pure ((d**b**Grab::p), b2) 
    go bf 22 s  c        = do (e, b1) <- fromBuf bf {a=Ty}
                              (u, b2) <- assert_total $ fromBuf b1 {a=Control s e}
                              (tag, b3) <- fromBuf b2 {a=Bits8}
                              ((d**b**p), b4) <- assert_total $ go b3 tag s (e~>c)
                              pure ((d**b**Push u::p), b4) 
    go bf 23 s  A        = do (tag, b1) <- fromBuf bf {a=Bits8}
                              ((d**b**p), b2) <- assert_total $ go b1 tag s A
                              pure ((d**b**Nul::p), b2)
    go bf 24 s  A        = do (tag, b1) <- fromBuf bf {a=Bits8}
                              ((d**b**p), b2) <- assert_total $ go b1 tag s A
                              pure ((d**b**Inc::p), b2)
    go bf 25 s  c        = do (t, b1) <- assert_total $ fromBuf bf {a=Control s c}
                              (f, b2) <- assert_total $ fromBuf b1 {a=Control (A::s) c}
                              (tag, b3) <- fromBuf b2 {a=Bits8}
                              ((d**b**p), b4) <- assert_total $ go b3 tag s A
                              pure ((d**b**Case t f::p), b4) 
    go bf 26 s  c        = do (tag, b1) <- fromBuf bf {a=Bits8}
                              ((d**b**p), b2) <- assert_total $ go b1 tag (c::s) c
                              pure ((d**b**Loop::p), b2)
    go bf 30 s  c        = pure ((s**c**[]), bf)
    go bf _  _  _        = throw " tag/type mismatch"
