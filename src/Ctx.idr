module Ctx

import Data.List

%default total
%access public export

-- contexts with names

Ctx : Type -> Type
Ctx t = List (String, t)

eraseCtx : Ctx t -> List t
eraseCtx = map snd

data InCtx : Ctx t -> String -> t -> Type where
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

inCtxUniq : InCtx g s a -> InCtx g s b -> a = b
inCtxUniq  Here           Here          = Refl
inCtxUniq  Here          (There neq2 _) = absurd $ neq2 Refl
inCtxUniq (There neq1 _)  Here          = absurd $ neq1 Refl
inCtxUniq (There _ i1)   (There _ i2)   = inCtxUniq i1 i2

lookup : (g : Ctx t) -> (x : String) -> Dec (a ** InCtx g x a)
lookup []           x = No (\(_**e) => uninhabited e)
lookup ((y,b)::g) x with (decEq x y)
  lookup ((y,b)::g) y | Yes Refl = Yes (b**Here)
  lookup ((y,b)::g) x | No ctra with (lookup g x)
    lookup ((y,b)::g) x | No ctra | Yes (a**el) = Yes (a**There ctra el)
    lookup ((y,b)::g) x | No ctra | No ctra2 = No $ nowhere ctra ctra2