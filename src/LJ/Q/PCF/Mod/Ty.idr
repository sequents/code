module LJ.Q.PCF.Mod.Ty

%default total

public export
data Ty = A | Imp Ty Ty | C Ty

infixr 5 ~>
public export
(~>) : Ty -> Ty -> Ty
(~>) = Imp

public export
Show Ty where
  show  A        = "*"
  show (Imp a b) = "(" ++ show a ++ "->" ++ show b ++ ")"
  show (C a)     = "<" ++ show a ++ ">"

public export
Uninhabited (A = Imp _ _) where
  uninhabited Refl impossible

public export
Uninhabited (A = C _) where
  uninhabited Refl impossible

public export
Uninhabited (Imp _ _ = C _) where
  uninhabited Refl impossible

export
impInj : Imp a b = Imp c d -> (a=c, b=d)
impInj Refl = (Refl, Refl)

export
cInj : C a = C b -> a = b
cInj Refl = Refl

public export
DecEq Ty where
  decEq  A         A        = Yes Refl
  decEq  A        (Imp _ _) = No uninhabited
  decEq  A        (C _)     = No uninhabited
  decEq (Imp _ _)  A        = No $ uninhabited . sym
  decEq (Imp a b) (Imp c d) with (decEq a c, decEq b d)
    decEq (Imp a b) (Imp c d) | (No ctra, _)         = No $ ctra . fst . impInj
    decEq (Imp a b) (Imp c d) | (_, No ctra2)        = No $ ctra2 . snd . impInj
    decEq (Imp a b) (Imp a b) | (Yes Refl, Yes Refl) = Yes Refl
  decEq (Imp _ _) (C _)     = No uninhabited
  decEq (C _)      A        = No $ uninhabited . sym
  decEq (C _)     (Imp _ _) = No $ uninhabited . sym
  decEq (C a)     (C b)     with (decEq a b)
    decEq (C a)     (C b) | No ctra = No $ ctra . cInj
    decEq (C a)     (C a) | Yes Refl = Yes Refl