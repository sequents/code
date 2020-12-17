module Lambda.PCF.V.LamF.Term

import Data.List
import Elem
import Subset
import Lambda.STLC.Ty

%default total

mutual
  public export
  data Val : List Ty -> Ty -> Type where
    Var  : Elem a g -> Val g a
    Zero : Val g A
    Succ : Val g A -> Val g A
    LamF : Comp (a::(a~>b)::g) b -> Val g (a~>b)

  public export
  data Comp : List Ty -> Ty -> Type where
    V   : Val g a -> Comp g a
    App : Comp g (a~>b) -> Comp g a -> Comp g b
    If0 : Comp g A -> Comp g a -> Comp (A::g) a -> Comp g a

mutual
  export
  Show (Val g a) where
    show (Var n)  = show $ elem2Nat n
    show  Zero    = "Z"
    show (Succ v) = "S" ++ show v
    show (LamF c) = "\\" ++ assert_total (show c)

  export
  Show (Comp g a) where
    show (V v)       = "[" ++ show v ++ "]"
    show (App t u)   = "(" ++ show t ++ ")(" ++ show u ++ ")"
    show (If0 v t f) = "IFZ " ++ show v ++ " THEN " ++ show t ++ " ELSE " ++ show f

mutual
  public export
  renameV : Subset g d -> Val g a -> Val d a
  renameV s (Var el) = Var $ s el
  renameV s  Zero    = Zero
  renameV s (Succ v) = Succ $ renameV s v
  renameV s (LamF c) = LamF $ renameC (ext $ ext s) c

  public export
  renameC : Subset g d -> Comp g a -> Comp d a
  renameC s (V v)       = V $ renameV s v
  renameC s (App v u)   = App (renameC s v) (renameC s u)
  renameC s (If0 v t f) = If0 (renameC s v) (renameC s t) (renameC (ext s) f)

export
lt : Comp g a -> Comp (a::g) b -> Comp g b
lt t u = App (V $ LamF $ renameC (ext weaken) u) t

export
idid : Comp g (A~>A)
idid = App (V $ LamF $ V $ Var Here) (V $ LamF $ V $ Var Here)

export
idid_id : Comp g (A~>A)
idid_id = App (App (V $ LamF $ V $ Var Here) (V $ LamF $ V $ Var Here)) (V $ LamF $ V $ Var Here)

export
id_idid : Comp g (A~>A)
id_idid = App (V $ LamF $ V $ Var Here) (App (V $ LamF $ V $ Var Here) (V $ LamF $ V $ Var Here))

export
bam0 : Comp g A
bam0 = App (V $ LamF $ App (V $ Var $ There Here) (V $ Succ $ Var Here)) (V Zero)

export
bam : Comp g A
bam = App (V $ LamF $ V Zero) bam0

export
fromN : Nat -> Val g A
fromN  Z    = Zero
fromN (S n) = Succ $ fromN n

export
plusN : Val g (A~>A~>A)
plusN = LamF $ V $ LamF $ If0 (V $ Var $ There $ There Here)
                              (V $ Var Here)
                              (lt (App (App (V $ Var $ There $ There $ There $ There Here)
                                            (V $ Var Here))
                                       (V $ Var $ There Here)) $
                               V $ Succ $ Var Here)

export
plus32 : Comp g A
plus32 = App (App (V plusN) (V $ fromN 3)) (V $ fromN 2)
