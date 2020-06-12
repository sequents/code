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

-- processes with Switch

data Res t = Stuck | Step t | Switch t

Functor Res where
  map f  Stuck       = Stuck
  map f (Step t)     = Step (f t)
  map f (Switch t) = Switch (f t)

Applicative Res where
  pure a = Step a
  Stuck      <*>  Stuck       = Stuck
  Stuck      <*> (Step t)     = Stuck
  Stuck      <*> (Switch t) = Stuck
  (Step f)   <*>  Stuck       = Stuck
  (Step f)   <*> (Step t)     = Step (f t)
  (Step f)   <*> (Switch t) = Switch (f t)
  (Switch f) <*>  Stuck       = Stuck
  (Switch f) <*> (Step t)     = Switch (f t)
  (Switch f) <*> (Switch t) = Switch (f t)

Alternative Res where
  empty = Stuck
  Stuck      <|>  Stuck       = Stuck
  Stuck      <|> (Step t)     = Step t
  Stuck      <|> (Switch t) = Switch t
  (Step s)   <|>  Stuck       = Step s
  (Step s)   <|> (Step t)     = Step s
  (Step s)   <|> (Switch t) = Step s
  (Switch s) <|>  Stuck       = Switch s
  (Switch s) <|> (Step t)     = Switch s
  (Switch s) <|> (Switch t) = Switch s

Monad Res where
  Stuck      >>= f = Stuck
  (Step t)   >>= f = f t
  (Switch t) >>= f = f t

iterCountR : (a -> Res a) -> (a -> Res a) -> a -> (Nat, a)
iterCountR step rb s = loop True Z s
  where
  loop : Bool -> Nat -> a -> (Nat, a)
  loop b n s1 = case (if b then step else rb) s1 of
    Stuck => (n, s1)
    Step s2 => assert_total $ loop b (S n) s2
    Switch s2 => assert_total $ loop (not b) n s2

iterFuelR : Fuel -> (a -> Res a) -> (a -> Res a) -> a -> (Maybe Nat, a)
iterFuelR fu step rb s = loop fu True Z s
  where
  loop : Fuel -> Bool -> Nat -> a -> (Maybe Nat, a)
  loop  Dry     _ _ s1 = (Nothing, s1)
  loop (More f) b n s1 = case (if b then step else rb) s1 of
    Stuck => (Just n, s1)
    Step s2 => assert_total $ loop f b (S n) s2
    Switch s2 => assert_total $ loop f (not b) n s2
