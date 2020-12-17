module Lambda.PCF.V.Mod.Term

import Data.List
import Elem
import Subset
import Lambda.PCF.V.Mod.Ty

%default total

mutual
  public export
  data Val : List Ty -> Ty -> Type where
    Var  : Elem a g -> Val g a
    Zero : Val g A
    Succ : Val g A -> Val g A
    Lam  : Comp (a::g) b -> Val g (a~>b)
    Fix  : Comp (C a::g) a -> Val g (C a)
    Wrap : Comp g a -> Val g (C a)

  public export
  data Comp : List Ty -> Ty -> Type where
    V   : Val g a -> Comp g a
    App : Val g (a~>b) -> Val g a -> Comp g b
    If0 : Val g A -> Comp g a -> Comp (A::g) a -> Comp g a
    Bnd : Val g (C a) -> Comp (a::g) b -> Comp g b

mutual
  export
  Show (Val g a) where
    show (Var n)  = show $ elem2Nat n
    show  Zero    = "Z"
    show (Succ v) = "S" ++ show v
    show (Lam c)  = "\\" ++ assert_total (show c)
    show (Fix c)  = "FIX " ++ assert_total (show c)
    show (Wrap c) = "{" ++ assert_total (show c) ++ "}"

  export
  Show (Comp g a) where
    show (V v)       = "[" ++ show v ++ "]"
    show (App t u)   = "(" ++ show t ++ ")(" ++ show u ++ ")"
    show (If0 v t f) = "IFZ " ++ show v ++ " THEN " ++ show t ++ " ELSE " ++ show f
    show (Bnd v c)   = "BIND " ++ show v ++ " IN " ++ show c

mutual
  export
  renameV : Subset g d -> Val g a -> Val d a
  renameV s (Var el) = Var $ s el
  renameV s  Zero    = Zero
  renameV s (Succ v) = Succ $ renameV s v
  renameV s (Lam c)  = Lam $ renameC (ext s) c
  renameV s (Fix c)  = Fix $ renameC (ext s) c
  renameV s (Wrap c) = Wrap $ renameC s c

  export
  renameC : Subset g d -> Comp g a -> Comp d a
  renameC s (V v)       = V $ renameV s v
  renameC s (App v u)   = App (renameV s v) (renameV s u)
  renameC s (If0 v t f) = If0 (renameV s v) (renameC s t) (renameC (ext s) f)
  renameC s (Bnd v c)   = Bnd (renameV s v) (renameC (ext s) c)

lt : Comp g a -> Comp (a::g) b -> Comp g b
lt t u = Bnd (Wrap t) u

export
ap : Comp g (a~>b) -> Comp g a -> Comp g b
ap t u = lt t $ lt (renameC There u) $ App (Var $ There Here) (Var Here)

export
idid : Comp g (A~>A)
idid = App (Lam $ V $ Var Here) (Lam $ V $ Var Here)

export
idid_id : Comp g (A~>A)
idid_id = ap (App (Lam $ V $ Var Here) (Lam $ V $ Var Here)) (V $ Lam $ V $ Var Here)

export
id_idid : Comp g (A~>A)
id_idid = ap (V $ Lam $ V $ Var Here) (App (Lam $ V $ Var Here) (Lam $ V $ Var Here))

export
bam0 : Val g (C A)
bam0 = Fix $ Bnd (Var Here) (V $ Succ $ Var Here)

export
bam : Comp g A
bam = Bnd bam0 $ App (Lam $ V Zero) (Var Here)

export
fromN : Nat -> Val g A
fromN  Z    = Zero
fromN (S n) = Succ $ fromN n

export
plusN : Val g (C (A~>A~>A))
plusN = Fix $ V $ Lam $ V $ Lam $ If0 (Var $ There Here)
                                      (V $ Var Here)
                                      (Bnd (Var $ There $ There $ There Here) $
                                       lt (App (Var Here) (Var $ There Here)) $
                                       lt (App (Var Here) (Var $ There $ There $ There Here)) $
                                       (V $ Succ $ Var Here))

export
plus32 : Comp g A
plus32 = ap (Bnd plusN $ App (Var Here) (fromN 3)) (V $ fromN 2)
