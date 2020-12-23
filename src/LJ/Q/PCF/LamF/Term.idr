module LJ.Q.PCF.LamF.Term

import Data.List
import Subset
import Iter
import Lambda.STLC.Ty
--import Lambda.PCF.Term
--import LambdaC.PCF.Term
--import LambdaC.Smallstep

%default total
%access public export

mutual
  -- asynchronous
  data TermQ : List Ty -> Ty -> Type where
    V    : ValQ g a -> TermQ g a                                                  -- focus/dereliction
    GApp : Elem (a~>b) g -> ValQ g a -> TermQ (b::g) c -> TermQ g c               -- implication left intro, `let x : b = (f : a~>b) (t : a) in u : c`
    GIf0 : Elem A g -> TermQ g a -> TermQ (A::g) a -> TermQ (a::g) b -> TermQ g b -- N left intro
    Let  : ValQ g a -> TermQ (a::g) b -> TermQ g b                                -- head cut, `let x = t in u`

  -- right-synchronous
  data ValQ : List Ty -> Ty -> Type where
    Var  : Elem a g -> ValQ g a                    -- axiom
    LamF : TermQ (a::(a~>b)::g) b -> ValQ g (a~>b) -- implication intro (mixed)
    Zero : ValQ g A                                -- N right intro Z
    Succ : ValQ g A -> ValQ g A                    -- N right intro S

-- structural rules

mutual
  renameTerm : Subset g d -> TermQ g a -> TermQ d a
  renameTerm sub (V v)           = V $ renameVal sub v
  renameTerm sub (GApp el v t)   = GApp (sub el) (renameVal sub v) (renameTerm (ext sub) t)
  renameTerm sub (GIf0 el t f u) = GIf0 (sub el) (renameTerm sub t) (renameTerm (ext sub) f) (renameTerm (ext sub) u)
  renameTerm sub (Let v t)       = Let (renameVal sub v) (renameTerm (ext sub) t)

  renameVal : Subset g d -> ValQ g a -> ValQ d a
  renameVal sub (Var el) = Var $ sub el
  renameVal sub (LamF t) = LamF $ renameTerm (ext $ ext sub) t
  renameVal sub  Zero    = Zero
  renameVal sub (Succ t) = Succ $ renameVal sub t

shiftTerm : {auto is : IsSubset g d} -> TermQ g a -> TermQ d a
shiftTerm {is} = renameTerm (shift is)

shiftVal : {auto is : IsSubset g d} -> ValQ g a -> ValQ d a
shiftVal {is} = renameVal (shift is)

-- let f : (*~>*)~>(*~>*) = \x.[x]
--     t : (*~>*) = f (\x.[x])
-- in [t]
testTm0 : TermQ [] (A~>A)
testTm0 = Let (LamF $ V $ Var Here) $
          GApp Here (LamF $ V $ Var Here) $
          V $ Var Here

-- let f = \x.[x]
--     g = f (\x.[x])
--     t = g (\x.[x])
-- in [t]
testTm1 : TermQ [] (Imp A A)
testTm1 = Let (LamF $ V $ Var Here) $
          GApp Here (LamF $ V $ Var Here) $
          GApp Here (LamF $ V $ Var Here) $
          V $ Var Here

-- let f = \x.[x]
--     g = f (\x.[x])
--     h = \x.[x]
--     t = h g
-- in [t]
testTm2 : TermQ [] (Imp A A)
testTm2 = Let (LamF $ V $ Var Here) $
          GApp Here (LamF $ V $ Var Here) $
          Let (LamF $ V $ Var Here) $
          GApp Here (Var $ There Here) $
          V $ Var Here

fromN : Nat -> ValQ g A
fromN  Z    = Zero
fromN (S n) = Succ $ fromN n

-- let f = \x.[Z]
--     w = \f/x. let x = f (S x)
--               in [x]
--     x = w Z
--     t = f x
-- in [t]
bam : TermQ [] A
bam = Let (LamF {a=A} $ V Zero) $
      Let (LamF $ GApp (There Here) (Succ $ Var Here) $
                  V $ Var Here) $
      GApp Here Zero $
      GApp (There Here) (Var Here) $
      V $ Var Here

-- \f/x.[\y.let r = if x
--                    then [y]
--                    else \z.let g = f z
--                                t = g y
--                            in [S t]
--          in [r]]
add : ValQ [] (A~>A~>A)
add = LamF $ V $
      LamF $
      GIf0 (There $ There Here)
           (V $ Var Here)
           (GApp (There $ There $ There $ There Here) (Var Here) $
            GApp Here (Var $ There $ There Here) $
            V $ Succ $ Var Here) $
      V $ Var Here

-- let add = ..add..
--     g = add 2
--     t = g 2
-- in [t]
twotwo : TermQ [] A
twotwo = Let add $
         GApp Here (fromN 2) $
         GApp Here (fromN 2) $
         V $ Var Here

--\f/x.[\y.let r = if y
--                   then [x]
--                   else \z.let s = if x
--                                     then [Z]
--                                     else \w.let g = f w
--                                                 t = g z
--                                             in [t]
--                           in [s]
--         in [r]]
minusN : ValQ g (A~>A~>A)
minusN = LamF $ V $
         LamF $
         GIf0 Here
              (V $ Var $ There $ There Here)
              (GIf0 (There $ There $ There Here)
                    (V Zero)
                    (GApp (There $ There $ There $ There $ There Here) (Var Here) $
                     GApp Here (Var $ There $ There Here) $
                     V $ Var Here) $
               V $ Var Here) $
         V $ Var Here

-- let minus = ..minusN..
--     g = minus 3
--     t = g 2
-- in [t]
threetwo : TermQ g A
threetwo = Let minusN $
           GApp Here (fromN 3) $
           GApp Here (fromN 2) $
           V $ Var Here