module Iter

%default total
%access public export

iter : (a -> Maybe a) -> a -> Maybe a
iter step = loop 
  where 
  loop : a -> Maybe a
  loop t = case step t of
    Nothing => Just t
    Just t2 => assert_total $ loop t2

iterCount : (a -> Maybe a) -> a -> (Nat, Maybe a)
iterCount step s = loop Z s
  where
  loop : Nat -> a -> (Nat, Maybe a)
  loop n s1 = case step s1 of
    Nothing => (n, Just s1)
    Just s2 => assert_total $ loop (S n) s2