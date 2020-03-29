module Subset

import Data.List
%hide Prelude.Pairs.Subset

%access public export
%default total

Subset : (g : List a) -> (d : List a) -> Type
Subset {a} g d = {x : a} -> Elem x g -> Elem x d

subsetId : Subset g g
subsetId = id

subsetTrans : Subset g d -> Subset d t -> Subset g t
subsetTrans gd dt = dt . gd

nilSubset : Subset [] xs
nilSubset = absurd

-- oneSubs : Subset [1,2] [3,2,1]
-- oneSubs Here = There $ There Here
-- oneSubs (There Here) = There Here

ext : Subset g d -> Subset (b::g) (b::d)
ext _  Here      = Here
ext r (There el) = There (r el)

weaken : Subset g (x::g)
weaken = There

contract : Elem x g -> Subset (x::g) g
contract el  Here     = el
contract _  (There s) = s

permute : (g : List t) -> Subset (g ++ a::b::d) (g ++ b::a::d)
permute  []      Here              = There Here
permute  []     (There Here)       = Here
permute  []     (There (There el)) = There $ There el
permute (g::gs)  Here              = Here
permute (g::gs) (There el)         = There $ permute gs el

permute0 : Subset (a::b::g) (b::a::g)
permute0 = permute []

-- 3 structural rules are enough

data Struct : List a -> List a -> Type where
  Id       : Struct g g
  Weak     : Struct g d -> Struct g (x::d)
  Contract : Struct g d -> Struct (x::x::g) (x::d)
  Permute  : (s : List a) -> Struct g d -> Struct (s ++ x::y::g) (s ++ y::x::d)

struct : Struct g d -> Subset g d
struct  Id                  el                = el
struct (Weak t)             el                = There $ struct t el
struct (Contract _)         Here              = Here
struct (Contract _)        (There  Here)      = Here
struct (Contract t)        (There (There el)) = There $ struct t el
struct (Permute []      _)  Here              = There Here
struct (Permute []      _) (There  Here)      = Here
struct (Permute []      t) (There (There el)) = There $ There $ struct t el
struct (Permute (s::_)  _)  Here              = Here
struct (Permute (s::ss) t) (There el)         = There $ struct (Permute ss t) el

-- inductive subset relation (useful for auto search)

data IsSubset : List a -> List a -> Type where
  Id    :                      IsSubset           l            l
  ConsR : IsSubset     l  m -> IsSubset           l  (      a::m)
  Cons2 : IsSubset     l  m -> IsSubset (      a::l) (      a::m)
  Swap  : IsSubset     l  m -> IsSubset (   a::b::l) (   b::a::m)
  Rot   : IsSubset     l  m -> IsSubset (a::b::c::l) (c::a::b::m)
  CtrH  :                      IsSubset (   a::a::l) (      a::l)
  CtrT  : IsSubset (a::l) m -> IsSubset (   a::b::l) (      b::m)

ctr : Elem a l -> IsSubset (a :: l) l
ctr  Here      = CtrH
ctr (There el) = CtrT $ ctr el

shift : IsSubset l m -> Subset l m
shift  Id        el                        = el
shift (ConsR s)  el                        = There $ shift s el
shift (Cons2 s)  Here                      = Here
shift (Cons2 s) (There  el)                = There $ shift s el
shift (Swap s)   Here                      = There Here
shift (Swap s)  (There  Here)              = Here
shift (Swap s)  (There (There el))         = There $ There $ shift s el
shift (Rot s)    Here                      = There Here
shift (Rot s)   (There  Here)              = There $ There Here
shift (Rot s)   (There (There  Here))      = Here
shift (Rot s)   (There (There (There el))) = There $ There $ There $ shift s el
shift  CtrH      Here                      = Here
shift  CtrH     (There el)                 = el
shift (CtrT s)   Here                      = There $ shift s Here
shift (CtrT s)  (There Here)               = Here
shift (CtrT s)  (There (There el))         = There $ shift s (There el)

-- partial subsets

SubsetM : (g : List a) -> (d : List a) -> Type
SubsetM {a} g d = {x : a} -> Elem x g -> Maybe (Elem x d)

extM : SubsetM g d -> SubsetM (b::g) (b::d)
extM _  Here      = Just Here
extM r (There el) = There <$> r el

contractM : SubsetM (x::d) d
contractM  Here     = Nothing
contractM (There s) = Just s
