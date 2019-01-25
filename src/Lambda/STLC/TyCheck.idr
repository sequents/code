module Lambda.STLC.TyCheck

import Data.List
import TParsec
import Parse
import Lambda.STLC.Ty
import Lambda.STLC.Term
import Lambda.STLC.Parser

%access public export
%default total

-- bidirectional typechecker

Ctx : Type
Ctx = List (String, Ty)

eraseCtx : Ctx -> List Ty     
eraseCtx = map snd

data InCtx : Ctx -> String -> Ty -> Type where  
  Here : InCtx ((x,a)::g) x a   
  There : Not (x=y) -> InCtx g x a -> InCtx ((y,b)::g) x a

eraseInCtx : InCtx c s a -> Elem a (eraseCtx c)  
eraseInCtx  Here       = Here
eraseInCtx (There _ i) = There $ eraseInCtx i

Uninhabited (InCtx [] x a) where
  uninhabited Here impossible  
  uninhabited (There _ _) impossible  

nowhere : Not (x=y) -> Not (a ** InCtx g x a) -> Not (a ** InCtx ((y,b)::g) x a)
nowhere neq ctra (b**Here)      = neq Refl
nowhere neq ctra (a**There n i) = ctra (a**i)

mutual
  data Val : Ctx -> Val -> Ty -> Type where
    Lam : Val ((s,a)::g) v b -> Val g (Lam s v) (a~>b)
    Emb : Neu g m a -> a = b -> Val g (Emb m) b

  data Neu : Ctx -> Neu -> Ty -> Type where
    Var : InCtx g s a -> Neu g (Var s) a
    Cut : Val g m a -> Neu g (Cut m a) a
    App : Neu g l (a~>b) -> Val g m a -> Neu g (App l m) b

Uninhabited (Val _ (Lam _ _) A) where
  uninhabited (Lam _) impossible
  uninhabited (Emb _ _) impossible

inCtxUniq : InCtx g s a -> InCtx g s b -> a = b  
inCtxUniq  Here           Here          = Refl
inCtxUniq  Here          (There neq2 _) = absurd $ neq2 Refl
inCtxUniq (There neq1 _)  Here          = absurd $ neq1 Refl
inCtxUniq (There _ i1)   (There _ i2)   = inCtxUniq i1 i2

neuUniq : Neu g m a -> Neu g m b -> a = b
neuUniq (Var i1)   (Var i2)   = inCtxUniq i1 i2
neuUniq (Cut v1)   (Cut v2)   = Refl
neuUniq (App t1 _) (App t2 _) = snd $ impInj $ neuUniq t1 t2 

lookup : (g : Ctx) -> (x : String) -> Dec (a ** InCtx g x a)
lookup []           x = No (\(_**e) => uninhabited e)
lookup ((y,b)::g) x with (decEq x y)
  lookup ((y,b)::g) y | Yes Refl = Yes (b**Here)
  lookup ((y,b)::g) x | No ctra with (lookup g x)
    lookup ((y,b)::g) x | No ctra | Yes (a**el) = Yes (a**There ctra el)
    lookup ((y,b)::g) x | No ctra | No ctra2 = No $ nowhere ctra ctra2

notArg : Neu g l (a~>b) -> Not (Val g m a) -> Not (c ** Neu g (App l m) c)
notArg n nv (c**App t u) = let Refl = fst $ impInj $ neuUniq n t in nv u

notSwitch : Neu g m a -> Not (a = b) -> Not (Val g (Emb m) b)
notSwitch n neq (Emb v eq) = let Refl = neuUniq n v in neq eq

mutual    
  synth : (g : Ctx) -> (m : Neu) -> Dec (a ** Neu g m a)
  synth g (Var s) with (lookup g s)
    synth g (Var s) | Yes (a**el) = Yes (a ** Var el)
    synth g (Var s) | No ctra = No $ \(a**Var el) => ctra (a ** el)
  synth g (Cut v t) with (inherit g v t) 
    synth g (Cut v t) | Yes val = Yes (t ** Cut val)
    synth g (Cut v t) | No ctra = No $ \(_**Cut v) => ctra v
  synth g (App t u) with (synth g t)
    synth g (App t u) | Yes (A**n) = No $ \(_**App v _) => uninhabited $ neuUniq v n 
    synth g (App t u) | Yes ((Imp a b)**n) with (inherit g u a)
      synth g (App t u) | Yes ((Imp a b)**n) | Yes m = Yes (b ** App n m)
      synth g (App t u) | Yes ((Imp a b)**n) | No ctra = No $ notArg n ctra
    synth g (App t u) | No ctra = No $ \(b**App {a} v _) => ctra ((a~>b) ** v)

  inherit : (g : Ctx) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inherit g (Lam s v)  A        = No uninhabited
  inherit g (Lam s v) (Imp a b) with (inherit ((s,a)::g) v b)
    inherit g (Lam s v) (Imp a b) | Yes w = Yes $ Lam w
    inherit g (Lam s v) (Imp a b) | No ctra = No $ \(Lam w) => ctra w
  inherit g (Emb n)    a with (synth g n)
    inherit g (Emb n) a | Yes (b ** m) with (decEq a b)
      inherit g (Emb n) a | Yes (b ** m) | Yes prf = Yes $ Emb m (sym prf)
      inherit g (Emb n) a | Yes (b ** m) | No ctra = No $ notSwitch m (ctra . sym)
    inherit g (Emb n) a | No ctra = No $ \(Emb m Refl) => ctra (a ** m)

mutual     
  val2Term : Val g m a -> Term (eraseCtx g) a
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term (Emb v Refl) = neu2Term v

  neu2Term : Neu g m a -> Term (eraseCtx g) a
  neu2Term (Var i)   = Var $ eraseInCtx i
  neu2Term (Cut v)   = val2Term v 
  neu2Term (App t u) = App (neu2Term t) (val2Term u)

parseCheckTerm : String -> Either Error (a ** Term [] a)  
parseCheckTerm s = do b <- parseNeu s
                      case synth [] b of 
                        Yes (a ** n) => Right (a ** neu2Term n)
                        No _ => Left TypeError

private    
test0 : parseCheckTerm "(^x.x : *->*)" = Right (TestTy ** ResultTm)
test0 = Refl

--private    
--test1 : parseCheckTerm "((^x.x : ((*->*)->(*->*))->((*->*)->(*->*))) ^x.x : (*->*)->(*->*)) ^x.x" = Right (TestTy ** TestTm1)
--test1 = Refl

--private
--test2 : parseCheckTerm "(^x.x : ((*->*)->(*->*))) (^x.x : (*->*)->(*->*)) ^x.x" = Right (TestTy ** TestTm2)
--test2 = Refl
