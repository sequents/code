module Elem

import Data.Fin
import Data.List
import Data.List.Quantifiers

%default total
%access public export

elem2Nat : Elem a g -> Nat
elem2Nat  Here      = Z
elem2Nat (There el) = S (elem2Nat el)

indexElem : Nat -> (xs : List a) -> Maybe (x ** Elem x xs)
indexElem  _    []        = Nothing
indexElem  Z    (y :: ys) = Just (y ** Here)
indexElem (S n) (y :: ys) = map (\(x ** p) => (x ** There p)) (indexElem n ys)

elem2Fin : Elem a g -> Fin (length g)
elem2Fin  Here      = FZ
elem2Fin (There el) = FS (elem2Fin el)

fin2Elem : (xs : List a) -> Fin (length xs) -> (x ** Elem x xs)
fin2Elem (x::xs)  FZ    = (x ** Here)
fin2Elem (x::xs) (FS f) = let (x ** p) = fin2Elem xs f in
                          (x ** There p)

-- TODO add to Data.List.Quantifiers
indexAll : Elem x xs -> All p xs -> p x
indexAll  Here     (p::_  ) = p
indexAll (There e) ( _::ps) = indexAll e ps
