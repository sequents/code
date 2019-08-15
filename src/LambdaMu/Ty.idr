module LambdaMu.Ty

%access public export
%default total

data Ty = A | Bot | Imp Ty Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

Show Ty where
  show  A        = "*"
  show  Bot      = "_|_"
  show (Imp a b) = "(" ++ show a ++ "->" ++ show b ++ ")" 
  
Uninhabited (A = Imp _ _) where
  uninhabited Refl impossible
  
Uninhabited (Imp _ _ = A) where
  uninhabited Refl impossible

Uninhabited (Bot = Imp _ _) where
  uninhabited Refl impossible
  
Uninhabited (Imp _ _ = Bot) where
  uninhabited Refl impossible

Uninhabited (A = Bot) where
  uninhabited Refl impossible
  
Uninhabited (Bot = A) where
  uninhabited Refl impossible

impInj : a~>b = c~>d -> (a=c, b=d) 
impInj Refl = (Refl, Refl)

DecEq Ty where
  decEq  A         A        = Yes Refl
  decEq  A         Bot      = No uninhabited
  decEq  A        (Imp _ _) = No uninhabited
  decEq  Bot       A        = No uninhabited
  decEq  Bot       Bot      = Yes Refl
  decEq  Bot      (Imp _ _) = No uninhabited
  decEq (Imp _ _)  A        = No uninhabited
  decEq (Imp _ _)  Bot      = No uninhabited
  decEq (Imp a b) (Imp c d) with (decEq a c, decEq b d)
    decEq (Imp a b) (Imp c d) | (No ctra, _)         = No $ ctra . fst . impInj
    decEq (Imp a b) (Imp c d) | (_, No ctra2)        = No $ ctra2 . snd . impInj
    decEq (Imp a b) (Imp a b) | (Yes Refl, Yes Refl) = Yes Refl

NOT : Ty -> Ty
NOT t = t ~> Bot

OR : Ty -> Ty -> Ty
OR a b = (NOT a) ~> b

AND : Ty -> Ty -> Ty
AND a b = NOT (a ~> (NOT b))