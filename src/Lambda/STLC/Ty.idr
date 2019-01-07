module Lambda.STLC.Ty

%access public export
%default total

data Ty = A | Imp Ty Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp
