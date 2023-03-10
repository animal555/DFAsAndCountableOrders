{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

-- Not much there, just the official definition of a DFA that we use and a
-- couple of helper functions for examples.
-- We quantify existentially on the state space

module DFA where

import Data.List
import Finite


data DFA a = forall q. Finite q => Aut !q !(a -> q -> q) !(q -> Bool)

dFA2Lang :: DFA a -> [a] -> Bool
dFA2Lang (Aut q0 d f) = f . foldl' (flip d) q0

countStates :: DFA a -> Int
countStates (Aut q0 _ _) = length (q0 : allValues) - 1
