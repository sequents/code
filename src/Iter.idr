module Iter

import public Data.Fuel 

%default total
%access public export

iter : (a -> Maybe a) -> a -> a
iter step = loop 
  where 
  loop : a -> a
  loop t = case step t of
    Nothing => t
    Just t2 => assert_total $ loop t2

iterCount : (a -> Maybe a) -> a -> (Nat, a)
iterCount step s = loop Z s
  where
  loop : Nat -> a -> (Nat, a)
  loop n s1 = case step s1 of
    Nothing => (n, s1)
    Just s2 => assert_total $ loop (S n) s2

iterFuel : Fuel -> (a -> Maybe a) -> a -> (Maybe Nat, a)
iterFuel fu step s = loop fu Z s
  where
  loop : Fuel -> Nat -> a -> (Maybe Nat, a)
  loop Dry      _ s1 = (Nothing, s1)
  loop (More f) n s1 = case step s1 of 
    Nothing => (Just n, s1)
    Just s2 => loop f (S n) s2