module LJ.F.Term

import Data.List
import Subset

%default total
%access public export

mutual
  data PTy = AP | D NTy

  data NTy = AM | U PTy | Imp PTy NTy

infix 5 ~>
(~>) : PTy -> NTy -> NTy
(~>) = Imp

-- unary negative formula
data UN : NTy -> Type where
  UA : UN  AM
  UU : UN (U p)

mutual
  -- asynchronous
  data Async : List PTy -> NTy -> Type where
    FL  : Elem (D n) g -> LSync g n m -> Async g m  -- left focus, continuation
    FR  : RSync g p -> Async g (U p)                -- right focus, value
    IR  : Async (p::g) n -> Async g (p~>n)          -- lambda
    HCL : Async g n -> LSync g n m -> Async g m     -- left head cut, stack
    HCR : RSync g p -> Async (p::g) n -> Async g n  -- right head cut, let

  -- left synchronous, context + stoup
  data LSync : List PTy -> NTy -> NTy -> Type where
    AxL  : UN n -> LSync g n n                           -- nil
    BL   : Async (p::g) m -> LSync g (U p) m             -- left blur
    IL   : RSync g p -> LSync g n m -> LSync g (p~>n) m  -- cons

  -- right-synchronous
  data RSync : List PTy -> PTy -> Type where
    AxR  : Elem p g -> RSync g p                     -- variable
    BR   : Async g n -> RSync g (D n)                -- right blur

mutual
  renameAsync : Subset g d -> Async g a -> Async d a
  renameAsync s (FL el k) = FL (s el) (renameLSync s k)
  renameAsync s (FR r)    = FR $ renameRSync s r
  renameAsync s (IR t)    = IR $ renameAsync (ext s) t
  renameAsync s (HCL t c) = HCL (renameAsync s t) (renameLSync s c)
  renameAsync s (HCR r a)  = HCR (renameRSync s r) (renameAsync (ext s) a)

  renameLSync : Subset g d -> LSync g a b -> LSync d a b
  renameLSync s (AxL prf)  = AxL prf
  renameLSync s (BL a)     = BL (renameAsync (ext s) a)
  renameLSync s (IL t c)   = IL (renameRSync s t) (renameLSync s c)

  renameRSync : Subset g d -> RSync g a -> RSync d a
  renameRSync s (AxR el)   = AxR $ s el
  renameRSync s (BR a)     = BR $ renameAsync s a
