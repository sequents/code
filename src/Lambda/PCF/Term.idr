module Lambda.PCF.Term

import Lambda.STLC.Ty
import Data.List
import Elem

%access public export
%default total

-- type A will stand for a natural number

data Term : List Ty -> Ty -> Type where
  Var  : Elem a g -> Term g a
  Lam  : Term (a::g) b -> Term g (a~>b)
  App  : Term g (a~>b) -> Term g a -> Term g b
  Zero : Term g A
  Succ : Term g A -> Term g A
  If0  : Term g A -> Term g a -> Term (A::g) a -> Term g a
  Fix  : Term (a::g) a -> Term g a

-- print

Show (Term g a) where
  show (Var n)     = show $ elem2Nat n
  show (Lam t)     = "\\" ++ show t
  show (App t u)   = "(" ++ show t ++ ")(" ++ show u ++ ")"
  show  Zero       = "Z"
  show (Succ t)    = "S" ++ show t
  show (If0 c t f) = "IFZ " ++ show c ++ " THEN " ++ show t ++ " ELSE " ++ show f
  show (Fix t)     = "FIX " ++ show t

-- numbers

fromN : Nat -> Term g A
fromN  Z    = Zero
fromN (S n) = Succ $ fromN n

toN : Term g A -> Maybe Nat
toN  Zero    = Just Z
toN (Succ t) = S <$> toN t
toN  _       = Nothing

sucN : Term g (A~>A)
sucN = Lam $ Succ $ Var Here

-- identity tests

idid : Term [] (A~>A)
idid = App (Lam $ Var Here) (Lam $ Var Here)

idid_id : Term [] (A~>A)
idid_id = App (App (Lam $ Var Here) (Lam $ Var Here)) (Lam $ Var Here)

id_idid : Term [] (A~>A)
id_idid = App (Lam $ Var Here) (App (Lam $ Var Here) (Lam $ Var Here))

-- non-termination

bam : Term [] A
bam = App (Lam Zero) (Fix $ Succ $ Var Here)

-- Church arithmetic

Ch : Ty -> Ty
Ch a = (a~>a)~>(a~>a)

twoC : Term g (Ch a)
twoC = Lam $ Lam $ App (Var $ There Here) (App (Var $ There Here) (Var Here))

plusC : Term g (Ch a ~> Ch a ~> Ch a)
plusC = Lam $ Lam $ Lam $ Lam $ App (App (Var $ There $ There $ There Here)
                                         (Var $ There Here))
                                    (App (App (Var $ There $ There Here)
                                              (Var $ There Here))
                                         (Var Here))

twotwoC : Term [] A
twotwoC = App (App (App (App plusC twoC) twoC) sucN) Zero

mkTwo : Term [] A
mkTwo = App (App twoC sucN) Zero

-- Nat arithmetic

plusN : Term g (A~>A~>A)
plusN = Fix $ Lam $ Lam $ If0 (Var $ There Here)
                              (Var Here)
                              (Succ $ App (App (Var $ There $ There $ There Here)
                                               (Var Here))
                                          (Var $ There Here))

twotwoN : Term [] A
twotwoN = App (App plusN (fromN 2)) (fromN 2)

minusN : Term g (A~>A~>A)
minusN = Fix $ Lam $ Lam $ If0 (Var Here)
                               (Var $ There Here)
                               (If0 (Var $ There $ There Here)
                                     Zero
                                    (App (App (Var $ There $ There $ There $ There Here)
                                              (Var Here))
                                         (Var $ There Here)))

threeMinusTwoN : Term [] A
threeMinusTwoN = App (App minusN (fromN 3)) (fromN 2)

-- sharing

plusplus : Term [] A
plusplus = App (Lam $ App (App plusN (Var Here)) (Var Here)) $
           App (App plusN (fromN 9)) (fromN 1)
