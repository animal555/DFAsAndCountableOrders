{-# LANGUAGE GADTs #-}

-- Look at the other files for some documentation :)
-- 

module Main where

import Finite
import RCO
import DFA
import DFA2RCO
import Examples

data TestInstance =
  forall a. Finite a => I (DFA a) |
  forall a. Finite a => DI (DFA a) String
-- Datatype of test automata for the algorithm that computes the underlying
-- order type.
--
-- There is an existential quantification over the type a of alphabet of the
-- automaton, which is given in the first component of each constructor.
-- The second constructor allows to give a high-level description of the
-- language recognized by the automaton on top of the code - for the first
-- constructor, some boilerplate message will be displayed instead


-- List of examples to be processed by main; add your own!
testInstances :: [TestInstance]
testInstances =
  [
    DI exDFA1 "(00 + 01 +10)*11",
    DI exDFA2 "(0 + 1)*1",
    DI exDFA3 "(0 + 1)*",
    I exDFA4,
    I exDFA5,
    I exDFASD1,
    I exDFASD2,
    I exDFASD3,
    I exDFASD5
  ]

runInstance :: TestInstance -> String
runInstance i = "The order type of the lexicographic order over " ++
                description ++ " is:\n" ++ "   " ++ showOrdTy o ++ "\n"
      where description = case i of
                           DI _ str -> str
                           I a -> "some language recognized by a " ++
                                  show (countStates a) ++
                                  "-state(s) DFA that I build somehow"
            o = case i of 
                 DI a _ -> automata2OrderTyp a
                 I a    -> automata2OrderTyp a

main :: IO ()
main = do
  putStrLn (unlines (map runInstance testInstances))
