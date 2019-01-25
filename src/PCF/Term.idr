module PCF.Term

import Data.List

%access public export
%default total

data Ty = N | Imp Ty Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

data Term : List Ty -> Ty -> Type where
  Var  : Elem a g -> Term g a 
  Lam  : Term (a::g) b -> Term g (a~>b)
  App  : Term g (a~>b) -> Term g a -> Term g b
  Zero : Term g N
  Succ : Term g N -> Term g N
  If0  : Term g N -> Term g a -> Term (N::g) a -> Term g a
  Fix :  Term (a::g) a -> Term g a

idid : Term [] (N~>N)
idid = App (Lam $ Var Here) (Lam $ Var Here)  

bam : Term [] N
bam = App (Lam Zero) (Fix $ Succ $ Var Here)

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

twoN : Term g N
twoN = Succ $ Succ Zero

plusN : Term g (N~>N~>N)
plusN = Fix $ Lam $ Lam $ If0 (Var $ There Here) 
                              (Var Here) 
                              (Succ $ App (App (Var $ There $ There $ There Here) 
                                               (Var Here)) 
                                          (Var $ There Here))

twotwoN : Term [] N
twotwoN = App (App plusN twoN) twoN

sucN : Term g (N~>N)
sucN = Lam $ Succ $ Var Here

twotwoC : Term [] N
twotwoC = App (App (App (App plusC twoC) twoC) sucN) Zero

mkTwo : Term [] N
mkTwo = App (App twoC sucN) Zero