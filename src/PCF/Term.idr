module PCF.Term

import Lambda.STLC.Ty
import Data.List

%access public export
%default total

-- type A will stand for a natural nubmer

data Term : List Ty -> Ty -> Type where
  Var  : Elem a g -> Term g a 
  Lam  : Term (a::g) b -> Term g (a~>b)
  App  : Term g (a~>b) -> Term g a -> Term g b
  Zero : Term g A
  Succ : Term g A -> Term g A
  If0  : Term g A -> Term g a -> Term (A::g) a -> Term g a
  Fix  : Term (a::g) a -> Term g a

idid : Term [] (A~>A)
idid = App (Lam $ Var Here) (Lam $ Var Here)  

bam : Term [] A
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

twoN : Term g A
twoN = Succ $ Succ Zero

plusN : Term g (A~>A~>A)
plusN = Fix $ Lam $ Lam $ If0 (Var $ There Here) 
                              (Var Here) 
                              (Succ $ App (App (Var $ There $ There $ There Here) 
                                               (Var Here)) 
                                          (Var $ There Here))

twotwoN : Term [] A
twotwoN = App (App plusN twoN) twoN

sucN : Term g (A~>A)
sucN = Lam $ Succ $ Var Here

twotwoC : Term [] A
twotwoC = App (App (App (App plusC twoC) twoC) sucN) Zero

mkTwo : Term [] A
mkTwo = App (App twoC sucN) Zero