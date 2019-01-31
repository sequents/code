module Elem

import Data.Fin
import Data.List

%default total
%access public export

elem2Nat : Elem a g -> Nat
elem2Nat  Here      = Z
elem2Nat (There el) = S (elem2Nat el)

elem2Fin : Elem a g -> Fin (length g)
elem2Fin  Here      = FZ
elem2Fin (There el) = FS (elem2Fin el)