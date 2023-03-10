-- This module defines a minimalistic Finite typeclass for the purpose of
-- playing with DFAs without having to put the state spaces everywhere in
-- types to preserve finiteness. Not sure if this is particularly wise.
--
-- Later on I should put some more magic so that stuff like "Five" is useless
-- and to be able to seamlessly take lists of finite types to their sums.

module Finite where

import MyPrelude
import Data.List
import Data.Maybe


class Ord a => Finite a where
  allValues :: [a]

instance Finite () where 
  allValues = [()]

instance Finite Bool where
  allValues = [False, True]

instance (Finite a, Eq b) => Eq (a -> b) where
  f == g = all (\x -> f x == g x) allValues

-- this is stupidly inefficient
instance (Finite a, Ord a, Ord b) => Ord (a -> b) where
  f <= g = f == g || any (\x -> f x < g x &&
                               all (\y -> y >= x || f y == g y) allValues)
                     allValues

instance (Finite a, Finite b) => Finite (a -> b) where
  allValues = allFunsOver allValues
    where allFunsOver [] = [\_ -> error "empty domain"]
          allFunsOver (a : as) =
            concatMap (\f -> map (addBinding f a) allValues) (allFunsOver as)
          addBinding f a b a' | a == a'   = b
                              | otherwise = f a'

instance (Finite a, Finite b) => Finite (a, b) where
  allValues = [(x,y) | x <- allValues, y <- allValues]

instance (Finite a, Finite b) => Finite (Either a b) where
  allValues = map Left allValues ++ map Right allValues

instance Finite a => Finite (Maybe a) where
  allValues = Nothing : map Just allValues

type Five = Either (Maybe Bool) Bool


