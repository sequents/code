module Lambda.STLC.Ty

import Str
import Binary

%access public export
%default total

data Ty = A | Imp Ty Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

Show Ty where
  show  A        = "*"
  show (Imp a b) = "(" ++ show a ++ "->" ++ show b ++ ")" 

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

Codec Ty where
  toBuf buf t = toBuf buf (fromMaybe 0 $ parseBinStr $ go t)
  where
    go : Ty -> String
    go A = "0"
    go (Imp a b) = "1" ++ go a ++ go b
  fromBuf buf = do (i,r) <- fromBuf {a=Integer} buf
                   case fst <$> (go $ unpack $ toBinStr i) of 
                     Just t => pure (t,r)
                     Nothing => throw "Corrupt Ty"
  where
    go : List Char -> Maybe (Ty, List Char)
    go [] = Nothing
    go ('0'::xs) = Just (A, xs)
    go ('1'::xs) = do (a, xs0) <- go xs
                      (b, xs1) <- assert_total $ go xs0
                      pure $ (Imp a b, xs1)
    go (_::_) = Nothing
