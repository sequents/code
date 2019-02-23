module Elem

import Data.Fin
import Data.List

%default total
%access public export

elem2Nat : Elem a g -> Nat
elem2Nat  Here      = Z
elem2Nat (There el) = S (elem2Nat el)

nat2Elem : DecEq t => (a : t) -> (g : List t) -> Nat -> Maybe (Elem a g)
nat2Elem _ []      _    = Nothing
nat2Elem a (b::g)  Z    with (decEq a b)
  nat2Elem a (a::g) Z | Yes Refl = Just Here
  nat2Elem a (b::g) Z | No ctra = Nothing
nat2Elem a (b::g) (S n) = There <$> nat2Elem a g n

elem2Fin : Elem a g -> Fin (length g)
elem2Fin  Here      = FZ
elem2Fin (There el) = FS (elem2Fin el)
