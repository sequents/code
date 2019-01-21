module Subset

import Data.List

%access public export
%default total

Subset : (g : List a) -> (d : List a) -> Type
Subset {a} g d = {x : a} -> Elem x g -> Elem x d

nulSubs : Subset [] xs 
nulSubs = absurd

oneSubs : Subset [1,2] [3,2,1]
oneSubs Here = There $ There Here
oneSubs (There Here) = There Here

ext : Subset g d -> Subset (b::g) (b::d)
ext _  Here      = Here
ext r (There el) = There (r el)

contract : Elem x d -> Subset (x::d) d
contract el  Here     = el
contract _  (There s) = s

permute : Subset (a::b::g) (b::a::g)
permute  Here              = There Here
permute (There  Here     ) = Here
permute (There (There el)) = There (There el)
