{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}


-- This is the module that translates an automaton recognizing L to the order
-- type that corresponds to (L, ≤lex)
--
-- This is short and bureaucratic; the actual work is done in RCOEqns.
-- Here it's just about setting up the system of equations, taking the states
-- of the automaton to be variables.

module DFA2RCO where

import MyPrelude
import Finite
import RCO
import RCOEqns
import DFA
import Data.List
import Data.Maybe

-- [a] : alphabet
-- (a -> q -> q) : transition function
-- (q -> Bool) : is the state final?
-- (q -> OrdTy q) : system of equations over the set of variables q
state2Eqn :: [a] -> (a -> q -> q) -> (q -> Bool) -> q -> OrdTy q
state2Eqn chars delta final q
  | final q =  osum (OOne : map (OVar . (`delta` q)) chars)
  | otherwise = osum (map (OVar . (`delta` q)) chars)

-- Produce the system of equation, solve it, and lookup the value of the
-- initial state in the solution vector
automata2OrderTyp :: Finite a => DFA a -> OrdTy Void
automata2OrderTyp (Aut q0 delta final) =
  snd . fromJust $ find (\(v,_) -> v == q0) solved
  where
    eqns = map (\q -> (q, state2Eqn allValues delta final q)) allValues
    solved = solveEqnSys eqns

