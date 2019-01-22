module Lambda.STLC.Ty

%access public export
%default total

data Ty = A | Imp Ty Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

Uninhabited (A = Imp _ _) where
    uninhabited Refl impossible
  
Uninhabited (Imp _ _ = A) where
  uninhabited Refl impossible

impInj : Imp a b = Imp c d -> (a=c, b=d) 
impInj Refl = (Refl, Refl)

DecEq Ty where
  decEq  A         A        = Yes Refl
  decEq  A        (Imp _ _) = No uninhabited
  decEq (Imp _ _)  A        = No uninhabited
  decEq (Imp a b) (Imp c d) with (decEq a c, decEq b d)
    decEq (Imp a b) (Imp c d) | (No ctra, _)         = No $ ctra . fst . impInj
    decEq (Imp a b) (Imp c d) | (_, No ctra2)        = No $ ctra2 . snd . impInj
    decEq (Imp a b) (Imp a b) | (Yes Refl, Yes Refl) = Yes Refl
