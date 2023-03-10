{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

-- This is the module where there are examples of the algorithm running; this
-- is not very readable because I have not found a good way to output the UTF8
-- characters properly via neovim + HLS

module Examples where

import MyPrelude
import Finite
import DFA
import RCO
import DFA2RCO

-- Some examples:
--
-- 1] a DFA recognizing (00 + 01 + 10)*11
-- The alphabet is Bool, the state space Either (Maybe Bool) Bool
exDFA1 :: DFA Bool
exDFA1 = Aut (Left Nothing) delta f
  where f (Right x) = x
        f _         = False
        delta x (Left Nothing) = Left (Just x)
        delta True (Left (Just True)) = Right True
        delta _ (Left (Just _)) = Left Nothing
        delta _ (Right _) = Right False

-- >>>  automata2OrderTyp exDFA1
-- LSum (Shuffle [LProdOmOp (LSum (Shuffle [LProdOmOp OOne]) (LProdOmOp OOne))]) (LProdOmOp (LSum (Shuffle [LProdOmOp OOne]) (LProdOmOp OOne)))

-- 2] a DFA recognizing (0 + 1)*1
-- The alphabet is Bool and state space are both Bool

exDFA2 :: DFA Bool
exDFA2 = Aut False const id

-- >>> automata2OrderTyp exDFA2
-- Shuffle [OOne]

-- 3] (0 + 1)*

exDFA3 :: DFA Bool
exDFA3 = Aut () (\ _ _ -> ()) (const True)

-- >>> automata2OrderTyp exDFA3
-- LSum (LProdOm OOne) (Shuffle [LProdOm OOne])

-- >>> simplify . initialSol $ osum [OOne, OVar Nothing, OVar Nothing]


-- 4] I forget why I put this thing (maybe debugging?)
exDFA4 :: DFA (Bool, Bool)
exDFA4 = Aut (Just . Left $ (False, a)) delta finals
  where finals = (`elem` [Just . Right $ Nothing, Just . Right . Just $ True])
        delta  = tFunOfList transs
        transs = [(i,Left (parity, j), Left (not parity, i)) |
                      i <- [a,d], j <- [a,d], parity <- allValues]
                 ++
                 [(b, Left (True, d), Right Nothing),
                  (b, Right Nothing,  Right Nothing)]
                 ++
                 [(b, Left (False, d), Right $ Just False),
                  (b, Right $ Just False, Right $ Just False),
                  (c, Right $ Just False, Right $ Just True)]
        [a,b,c,d] = reverse allValues :: [(Bool, Bool)]

-- 5] I forget why I put this thing
exDFA5 :: DFA (Either (Maybe Bool) Bool)
exDFA5 = Aut (Just qMain) delta (\z -> z `elem` map Just [qOm, qOmOpF])
  where [qMain, qOm, qOmOp, qOmOpF] = allValues :: [(Bool, Bool)]
        delta = tFunOfList transs
        [a,b,c,d,e] = allValues :: [Five]
        transs = [(a, qMain, qMain),
                  (b, qMain, qOm)  ,
                  (c, qMain, qMain),
                  (d, qMain, qOmOp),
                  (e, qMain, qMain),
                  (e, qOm, qOm),
                  (a, qOmOp, qOmOp),
                  (b, qOmOp, qOmOpF)]

-- OK, to produce more interesting example, I have a few functions over
-- automata. They will be functional in the underlying order-types, and
-- allow us to do realize more complicated examples easily 

-- This takes two automata realizing order types τ and σ and produce an
-- automaton realizing {τ, σ}η
exDFAShuffle2 :: (Finite a1, Finite a2) => DFA a1 -> DFA a2 -> DFA (Either Five (Either a1 a2))
exDFAShuffle2 (Aut q0 deltal fq) (Aut r0 deltar fr) =
       Aut (Just Nothing) delta final
    where final (Just (Just (Left q))) = fq q
          final (Just (Just (Right r))) = fr r
          final _ = False
          [a,b,c,d,e] = allValues :: [Five]
          delta = tFunOfList transList
          transList =
            [(Left b, Nothing, Just (Left q0)),
             (Left d, Nothing, Just (Right r0))] ++
            [(Left l, Nothing, Nothing) | l <- [a,c,e]] ++
            [(Right . Left $ l, lSt q, lSt $ deltal l q) | (l,q) <- allValues] ++
            [(Right . Right $ l, rSt q, rSt $ deltar l q) | (l,q) <- allValues]
          lSt = Just . Left
          rSt = Just . Right
-- TODO: the list version [τ₁, ..., τ_k] ↦ {τ₁, ..., τ_k}η
--       this would require GADT magic


-- This takes two automata realizing order types τ and σ and produce an
-- automaton realizing τ + σ
exDFALSum :: (Finite a1, Finite a2) => DFA a1 -> DFA a2 -> DFA (Either Bool (Either a1 a2))
exDFALSum (Aut q0 deltal fq) (Aut r0 deltar fr) =
    Aut (Just Nothing) delta final
    where final (Just (Just (Left q))) = fq q
          final (Just (Just (Right r))) = fr r
          final _ = False
          [a,b] = allValues :: [Bool]
          delta = tFunOfList transList
          transList =
            [(Left a, Nothing, Just (Left q0)),
             (Left b, Nothing, Just (Right r0))] ++
            [(Right . Left $ l, lSt q, lSt $ deltal l q) | (l,q) <- allValues] ++
            [(Right . Right $ l, rSt q, rSt $ deltar l q) | (l,q) <- allValues]
          lSt = Just . Left
          rSt = Just . Right

-- Automaton realizing ω
exDFAOm :: DFA Bool
exDFAOm = Aut True (&&) id

-- >>> simplify . automata2OrderTyp $ exDFAOm
-- LProdOm OOne

-- Automaton realizing -ω
exDFAOmOp :: DFA Bool
exDFAOmOp = Aut (Just init) delta (== Just final)
  where [init, final] = allValues :: [Bool]
        delta = tFunOfList transList
        [a, b] = allValues :: [Bool]
        transList = [(a,init,init),(b,init,final)]

-- Automaton realizing 1
exDFAOne :: DFA ()
exDFAOne = Aut True (\_ _ -> False) id

-- >>> simplify . automata2OrderTyp $ exDFAOmOp
-- LProdOmOp OOne

-- >>> simplify . automata2OrderTyp $ exDFAShuffle2 exDFAOm exDFAOmOp
-- Shuffle [LProdOm OOne,LProdOmOp OOne]

-- OK below are a series of examples that show off how the shuffle operator
-- may need to be nested an arbitrary number of time in those shuffles
-- expressions.
--
-- I omit the type annotations because the alphabets become large very quickly
-- as I use this handy exDFAShuffle2 combinators
exDFASD1 = exDFAShuffle2 exDFAOm exDFAOmOp

-- >>> countStates exDFASD1
-- 7

-- >>> automata2OrderTyp $ exDFASD1
-- Shuffle [LProdOm OOne,LProdOmOp OOne]

exDFASD2 = exDFAShuffle2 (exDFALSum exDFAOm exDFAOmOp) exDFASD1

-- >>> countStates exDFASD2
-- 16

-- >>> automata2OrderTyp $ exDFASD2
-- Shuffle [LSum (LProdOm OOne) (LProdOmOp OOne),Shuffle [LProdOm OOne,LProdOmOp OOne]]

exDFASD3 = exDFALSum x x
 where x = exDFAShuffle2 exDFAOne exDFASD2


-- >>> countStates exDFASD3
-- 42

-- >>> automata2OrderTyp $ exDFASD3
-- LSum (Shuffle [OOne,Shuffle [LSum (LProdOm OOne) (LProdOmOp OOne),Shuffle [LProdOm OOne,LProdOmOp OOne]]]) (Shuffle [OOne,Shuffle [LSum (LProdOm OOne) (LProdOmOp OOne),Shuffle [LProdOm OOne,LProdOmOp OOne]]])

-- Better not write the type of the alphabet for this one :)
exDFASD5 = exDFAShuffle2 (exDFAShuffle2 exDFASD1 exDFASD3) (exDFAShuffle2 exDFASD2 exDFA3)

-- >>> countStates exDFASD5
-- 72

