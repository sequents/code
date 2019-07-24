module Elem

import Data.Fin
import Data.List

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
