module CBPV.NJPV

import Data.List
import Subset

import LJ.F.Ty

%default total
%access public export

mutual
  data TermS : List PTy -> NTy -> Type where
    Ie : TermS g (p~>n) -> ValI g p -> TermS g n
    Pe : ValS g (D n) -> TermS g n
    Ct : TermI g n -> TermS g n

  data ValS : List PTy -> PTy -> Type where
    Ax : Elem p g -> ValS g p
    Cp : ValI g p -> ValS g p

  data TermI : List PTy -> NTy -> Type where
    Ni : ValI g p -> TermI g (U p)
    Ii : TermI (p::g) n -> TermI g (p~>n)
    Ne : TermS g (U p) -> TermI (p::g) m -> TermI g m
    Mt : TermS g n -> UN n -> TermI g n

  data ValI : List PTy -> PTy -> Type where
    Pi : TermI g n -> ValI g (D n)
    Mp : ValS g p -> ValI g p

lt : ValI g p -> TermI (p::g) n -> TermI g n
lt v t = Ne (Ct $ Ni v) t
