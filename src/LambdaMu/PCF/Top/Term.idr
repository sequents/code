module LambdaMu.PCF.Top.Term

import Data.List
import LambdaMu.Ty

%access public export
%default total

mutual
  data Term : List Ty -> Ty -> List Ty -> Type where
    Var   : Elem a g -> Term g a d
    Lam   : Term (a::g) b d -> Term g (a~>b) d
    App   : Term g (a~>b) d -> Term g a d -> Term g b d
    Mu    : Cmd g (a::d) -> Term g a d
    Zero  : Term g A d
    Succ  : Term g A d -> Term g A d
    If0   : Term g A d -> Term g a d -> Term (A::g) a d -> Term g a d
    Fix   : Term (a::g) a d -> Term g a d

  data Cmd : List Ty -> List Ty -> Type where
    Named : Elem a d -> Term g a d -> Cmd g d
    Top   : Term g Bot d -> Cmd g d

fromN : Nat -> Term g A d
fromN  Z    = Zero
fromN (S n) = Succ $ fromN n

sucN : Term g (A~>A) d
sucN = Lam $ Succ $ Var Here

lift : Elem a d -> Term g (NOT a) d
lift el = Lam $ Mu $ Named (There el) (Var Here)

pair : Term g (a ~> b ~> AND a b) d
pair = Lam $ Lam $ Lam $ App (App (Var Here)
                                  (Var $ There $ There Here))
                             (Var $ There Here)

andFst : Term g (AND a b ~> a) d
andFst = Lam $ Mu $ Top $ App (Var Here)
                              (Lam $ Lam $ Mu $ Named (There Here) (Var $ There Here))

andSnd : Term g (AND a b ~> b) d
andSnd = Lam $ Mu $ Top $ App (Var Here)
                              (Lam $ lift Here)

raise : Term g a (b::a::d) -> Term g b (a::d)
raise = Mu . Named (There Here)

handle : Term g (a~>b) (b::d) -> Term g b (a::b::d) -> Term g b d
handle m n = Mu $ Named Here $ App m (Mu $ Named (There Here) n)

-- test

foo : Term [] A []
foo = handle sucN (raise $ Succ $ Succ Zero)

bar : Term [] A []
bar = handle sucN (Succ $ Succ Zero)

baz : Term [] A []
baz = App andSnd (App (App pair (fromN 5)) (fromN 3))

bam : Term [] A []
bam = App (Lam Zero) (Fix $ Succ $ Var Here)

Ch : Ty -> Ty
Ch a = (a~>a)~>(a~>a)

twoC : Term g (Ch a) d
twoC = Lam $ Lam $ App (Var $ There Here) (App (Var $ There Here) (Var Here))

plusC : Term g (Ch a ~> Ch a ~> Ch a) d
plusC = Lam $ Lam $ Lam $ Lam $ App (App (Var $ There $ There $ There Here)
                                         (Var $ There Here))
                                    (App (App (Var $ There $ There Here)
                                              (Var $ There Here))
                                         (Var Here))

plus : Term g (A~>A~>A) d
plus = Fix $ Lam $ Lam $ If0 (Var $ There Here)
                               (Var Here)
                               (Succ $ App (App (Var $ There $ There $ There Here)
                                                (Var Here))
                                           (Var $ There Here))

minus : Term g (A~>A~>A) [A,A]
minus = Fix (Lam (Lam (If0 (Var Here)
                        (Var (There Here))
                        (If0 (Var (There (There Here)))
                               (raise $ Var $ There Here)
                               (App (App (Var (There (There (There (There Here)))))
                                         (Var Here))
                                         (Var (There Here)))))))

minus' : Term g (A~>A~>A) []
minus' = Lam $ Lam $ handle (Lam $ Var Here) (App (App minus (Var Here)) (Var $ There Here))

twotwoN : Term [] A []
twotwoN = App (App plus (fromN 2)) (fromN 2)

twotwoC : Term [] A []
twotwoC = App (App (App (App plusC twoC) twoC) sucN) Zero

threeMinusTwoN : Term [] A []
threeMinusTwoN = App (App minus' (fromN 3)) (fromN 2)

twoMinusThreeN : Term [] A []
twoMinusThreeN = App (App minus' (fromN 2)) (fromN 3)

plusplus : Term [] A []
plusplus = App (Lam $ App (App Term.plus (Var Here)) (Var Here))
               (App (App Term.plus (fromN 9)) (fromN 1))
