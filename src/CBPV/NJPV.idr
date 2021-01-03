module CBPV.NJPV

import Data.List
import Subset

import LJ.F.Ty

%default total
%access public export

mutual
  data TermS : List PTy -> NTy -> Type where
    Ie : TermS g (p~>n) -> ValC g p -> TermS g n       -- app
    Pe : ValS g (D n) -> TermS g n                     -- force
    Ct : TermC g n -> TermS g n                        -- coerceT

  data ValS : List PTy -> PTy -> Type where
    Ax : Elem p g -> ValS g p                          -- var
    Cp : ValC g p -> ValS g p                          -- coerceV

  data TermC : List PTy -> NTy -> Type where
    Ni : ValC g p -> TermC g (U p)                     -- pure
    Ii : TermC (p::g) n -> TermC g (p~>n)              -- lam
    Ne : TermS g (U p) -> TermC (p::g) m -> TermC g m  -- bind
    Mt : TermS g n -> UN n -> TermC g n

  data ValC : List PTy -> PTy -> Type where
    Pi : TermC g n -> ValC g (D n)                     -- thunk
    Mp : ValS g p -> ValC g p

lt : ValC g p -> TermC (p::g) n -> TermC g n
lt v t = Ne (Ct $ Ni v) t
