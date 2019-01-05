module Lambda.STLC.Ty

%access public export
%default total

data Ty = A | Imp Ty Ty

infix 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp
