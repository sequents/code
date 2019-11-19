module MuPCF.Top.Term

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
foo = handle (Lam $ Succ $ Var Here) (raise $ Succ $ Succ Zero)

bar : Term [] A []
bar = handle (Lam $ Succ $ Var Here) (Succ $ Succ Zero)

baz : Term [] A []
baz = App andSnd (App (App pair (fromN 2)) (fromN 3))

plus : Term [] (A~>A~>A) []
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

minus' : Term [] (A~>A~>A) []
minus' = Lam $ Lam $ handle (Lam $ Var Here) (App (App minus (Var Here)) (Var $ There Here))