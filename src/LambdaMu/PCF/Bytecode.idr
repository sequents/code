module LambdaMu.PCF.Bytecode

import Data.List
import Iter
import Path
import Elem
import Binary
import LambdaMu.Ty
import LambdaMu.PCF.Term

import Data.Vect

%default total
%access public export

-- typed bytecode

mutual
  data I : (List Ty, Ty, List Ty) -> (List Ty, Ty, List Ty) -> Type where
    Access : Elem a g ->                            I (g,a   ,d) (   g,a   ,   d)
    Grab   :                                        I (g,a~>b,d) (a::g,b   ,   d)
    Push   : Control g a d ->                       I (g,b   ,d) (   g,a~>b,   d)
    Catch  :                                        I (g,a   ,d) (   g,Bot ,a::d)
    Throw  : Elem a d ->                            I (g,Bot ,d) (   g,a   ,   d)
    Nul    :                                        I (g,A   ,d) (   g,A   ,   d)
    Inc    :                                        I (g,A   ,d) (   g,A   ,   d)
    Case   : Control g a d -> Control (A::g) a d -> I (g,a   ,d) (   g,A   ,   d)
    Loop   :                                        I (g,a   ,d) (a::g,a   ,   d)

  record Control (g : List Ty) (a : Ty) (d : List Ty) where
    constructor MkCtr
    ec   : List Ty
    et   : Ty
    ed   : List Ty
    path : Path I (g,a,d) (ec,et,ed)

mutual
  showCtrl : Control g a d -> String
  showCtrl (MkCtr k b z p) = "{ " ++ show g ++ " |- " ++ show a ++ " | " ++ show d ++ " } "
                          ++ showPath g a d p {w=k} {x=b} {j=z}
                          ++ "{ " ++ show k ++ " |- " ++ show b ++ " | " ++ show z ++ " }"

  showPath : (s : List Ty) -> (c : Ty) -> (t : List Ty) -> Path I (s,c,t) (w,x,j) -> String
  showPath w  x     j []                 = ""
  showPath s  c     t (Access e::q)      = "ACC" ++ show (elem2Nat e) ++ " " ++ showPath s c t q
  showPath s (e~>f) t (Grab::q)          = "GRB " ++ showPath (e::s) f t q
  showPath s  c     t (Push {a=e} u::q)  = "PSH <" ++ showCtrl u ++ "> " ++ showPath s (e~>c) t q
  showPath s  c     t (Catch::q)         = "CAT " ++ showPath s Bot (c::t) q
  showPath s  Bot   t (Throw {a=o} e::q) = "THR" ++ show (elem2Nat e) ++ " " ++ showPath s o t q
  showPath s  A     t (Nul::q)           = "NUL " ++ showPath s A t q
  showPath s  A     t (Inc::q)           = "INC " ++ showPath s A t q
  showPath s  c     t (Case tr fa::q)    = "CAS <" ++ showCtrl tr ++ "> <" ++ showCtrl fa ++ "> " ++ showPath s A t q
  showPath s  c     t (Loop::q)          = "LOP " ++ showPath (c::s) c t q

Show (Control g a d) where
  show = showCtrl

infixr 5 +:
(+:) : I (g,a,d) (k,b,z) -> Control k b z -> Control g a d
(+:) i (MkCtr s c t p) = MkCtr s c t (i::p)

-- translate term into bytecode

compile : Term g a d -> Control g a d
compile {g} {a} {d} (Var e)       = MkCtr g a d [Access e]
compile             (Lam t)       = Grab +: compile t
compile             (App {b} t u) = Push {b} (compile u) +: compile t
compile             (Mu t)        = Catch +: compile t
compile             (Named e t)   = Throw e +: compile t
compile {g}     {d}  Zero         = MkCtr g A d [Nul]
compile             (Succ t)      = Inc +: compile t
compile             (If0 c t f)   = Case (compile t) (compile f) +: compile c
compile             (Fix t)       = Loop +: compile t

Codec (Control g a d) where
  toBuf buf (MkCtr k b z p) = do b1 <- toBuf buf k
                                 b2 <- toBuf b1 b
                                 b3 <- toBuf b2 z
                                 go b3 g a d p {w=k} {x=b} {j=z}
    where
    go : Binary -> (s : List Ty) -> (c : Ty) -> (t : List Ty) -> Path I (s,c,t) (w,x,j) -> IOE Binary
    go bf w  x     j []                 = toBuf bf (the Bits8 30)
    go bf s  c     t (Access e::q)      = assert_total $
                                          do b1 <- toBuf bf (the Bits8 20)
                                             b2 <- toBuf b1 (toIntegerNat $ elem2Nat e)
                                             go b2 s c t q
    go bf s (e~>f) t (Grab::q)          = assert_total $
                                          do b1 <- toBuf bf (the Bits8 21)
                                             go b1 (e::s) f t q
    go bf s  c     t (Push {a=e} u::q)  = assert_total $
                                          do b1 <- toBuf bf (the Bits8 22)
                                             b2 <- toBuf b1 e
                                             b3 <- toBuf b2 u
                                             go b3 s (e~>c) t q
    go bf s  c     t (Catch::q)         = assert_total $
                                          do b1 <- toBuf bf (the Bits8 23)
                                             go b1 s Bot (c::t) q
    go bf s  Bot   t (Throw {a=o} e::q) = assert_total $
                                          do b1 <- toBuf bf (the Bits8 24)
                                             b2 <- toBuf b1 o
                                             b3 <- toBuf b2 (toIntegerNat $ elem2Nat e)
                                             go b3 s o t q
    go bf s  A     t (Nul::q)           = assert_total $
                                          do b1 <- toBuf bf (the Bits8 25)
                                             go b1 s A t q
    go bf s  A     t (Inc::q)           = assert_total $
                                          do b1 <- toBuf bf (the Bits8 26)
                                             go b1 s A t q
    go bf s  c     t (Case tr fa::q)    = assert_total $
                                          do b1 <- toBuf bf (the Bits8 27)
                                             b2 <- toBuf b1 tr
                                             b3 <- toBuf b2 fa
                                             go b3 s A t q
    go bf s  c     t (Loop::q)          = assert_total $
                                          do b1 <- toBuf bf (the Bits8 28)
                                             go b1 (c::s) c t q

  fromBuf buf = do (k, b1) <- fromBuf buf {a=List Ty}
                   (b, b2) <- fromBuf b1 {a=Ty}
                   (z, b3) <- fromBuf b2 {a=List Ty}
                   (tag, b4) <- fromBuf b3 {a=Bits8}
                   ((s**c**t**p), b5) <- go b4 tag g a d
                   case (decEq k s, decEq b c, decEq z t) of
                     (Yes Refl, Yes Refl, Yes Refl) => pure (MkCtr k b z p, b5)
                     (_, _, _) => throw $ "type mismatch at path endpoint: expected " ++ show k ++ "|-" ++ show b ++ "|" ++ show z
                                  ++ ", got " ++ show s ++ "|-" ++ show c ++ "|" ++ show t
    where
    go : Binary -> Bits8 -> (s : List Ty) -> (c : Ty) -> (t : List Ty) -> IOE ((k**b**z**Path I (s,c,t) (k,b,z)), Binary)
    go bf 20 s  c        t  = do (n, b1) <- fromBuf bf {a=Integer}
                                 case indexElem (fromIntegerNat n) s of
                                   Just (x ** e) =>
                                      case decEq c x of
                                       Yes Refl => do (tag, b2) <- fromBuf b1 {a=Bits8}
                                                      ((k**b**z**p), b3) <- assert_total $ go b2 tag s c t
                                                      pure ((k**b**z**Access e::p), b3)
                                       No _ => throw $ "type mismatch in path: expected " ++ show c ++ ", got " ++ show x
                                   Nothing => throw $ "elem out of bounds: " ++ show n
    go bf 21 s (Imp c e) t = do (tag, b1) <- fromBuf bf {a=Bits8}
                                ((k**b**z**p), b2) <- go b1 tag (c::s) e t
                                pure ((k**b**z**Grab::p), b2)
    go bf 22 s  c        t = do (e, b1) <- fromBuf bf {a=Ty}
                                (u, b2) <- assert_total $ fromBuf b1 {a=Control s e t}
                                (tag, b3) <- fromBuf b2 {a=Bits8}
                                ((k**b**z**p), b4) <- assert_total $ go b3 tag s (e~>c) t
                                pure ((k**b**z**Push u::p), b4)
    go bf 23 s  c        t = do (tag, b1) <- fromBuf bf {a=Bits8}
                                ((k**b**z**p), b2) <- assert_total $ go b1 tag s Bot (c::t)
                                pure ((k**b**z**Catch::p), b2)
    go bf 24 s  Bot      t = do (c, b1) <- fromBuf bf {a=Ty}
                                (n, b2) <- fromBuf b1 {a=Integer}
                                case indexElem (fromIntegerNat n) t of
                                  Just (x ** e) =>
                                     case decEq c x of
                                      Yes Refl => do (tag, b3) <- fromBuf b2 {a=Bits8}
                                                     ((k**b**z**p), b4) <- assert_total $ go b3 tag s c t
                                                     pure ((k**b**z**Throw e::p), b4)
                                      No _ => throw $ "type mismatch in path: expected " ++ show c ++ ", got " ++ show x
                                  Nothing => throw $ "elem out of bounds: " ++ show n
    go bf 25 s  A        t = do (tag, b1) <- fromBuf bf {a=Bits8}
                                ((k**b**z**p), b2) <- assert_total $ go b1 tag s A t
                                pure ((k**b**z**Nul::p), b2)
    go bf 26 s  A        t = do (tag, b1) <- fromBuf bf {a=Bits8}
                                ((k**b**z**p), b2) <- assert_total $ go b1 tag s A t
                                pure ((k**b**z**Inc::p), b2)
    go bf 27 s  c        t = do (tr, b1) <- assert_total $ fromBuf bf {a=Control s c t}
                                (fa, b2) <- assert_total $ fromBuf b1 {a=Control (A::s) c t}
                                (tag, b3) <- fromBuf b2 {a=Bits8}
                                ((k**b**z**p), b4) <- assert_total $ go b3 tag s A t
                                pure ((k**b**z**Case tr fa::p), b4)
    go bf 28 s  c        t = do (tag, b1) <- fromBuf bf {a=Bits8}
                                ((k**b**z**p), b2) <- assert_total $ go b1 tag (c::s) c t
                                pure ((k**b**z**Loop::p), b2)
    go bf 30 s  c        t = pure ((s**c**t**[]), bf)
    go bf _  _  _        _ = throw " tag/type mismatch"
