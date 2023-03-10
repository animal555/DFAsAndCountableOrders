{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

-- The first non-trivial file; defines the syntax for regular countable
-- (linear) orders with parameters, basic operations, pretty-printing and,
-- most importantly, a normalization algorithm.
--
-- It should be stressed that I did not formally prove that the normalization
-- algorithm works (i.e., it does rewriting that is terminating and confluent),
-- but that sounds plausible at this stage. Although I am afraid I mostly
-- relied on old memory on the equations of algebras for countable word rather
-- than trying to write things down somewhat properly.
--
-- Seems to work like a charm on examples so far though!
-- But I will be wishy-washy if I talk about normal forms and "simpler" terms,
-- although I do have a strong opinion of what they are.

module RCO where

import Data.List
import MyPrelude

-- The important datatype for parameterized regular countable order types.
-- 
-- These can also be regarded as countable words with letters in Maybe a (OOne
-- would correspond to its own letter) or particularly nice functors over
-- countable linear orders (a would denote the set of variables).
-- Taking a = Void yields closed term for regular countable order types.
--
-- While the meaning of "solving an equation" we will be interested in requires
-- to talk about the category of functors over total orders, we can work at the
-- level of order types since they determine whatever those functors do anyway;
-- it is just that morphisms of order type is not a well-behaved notion I think
-- for talking about computing initial algebras.
--
-- So apologies if I blur the order/order types in explanations below
data OrdTy a =
     OVar a                   -- A variable
   | OOne                     -- The singleton order
   | OZero                    -- The empty order
   | LSum (OrdTy a) (OrdTy a) -- The lexicographic sum (F, G) ↦ F + G
   | LProdOm (OrdTy a)        -- the map F ↦ ω · F (iterate F + ... + F + ...)
   | LProdOmOp (OrdTy a)      -- the map F ↦ ω^op · F (ω^op is just ω reversed)
   | Shuffle [OrdTy a]        -- the most mysterious operator
 deriving (Eq, Show, Ord)     --    {F₁, ..., F_n} ↦ {F₁, ..., F_n}^η

-- # Additional explanations
-- 
-- ## The lexicographic sum
--   The carrier of A + B is the disjoint union,
--   we have inl _ < inr _ always, and otherwise
--   we lift the order from A and B
--
-- TODO: change that to LSum [OrdTy a] (this would allow to get rid of Zero and
-- would be more elegant/not more painful to deal with I think)
--
--
-- ## The shuffle operator
--
-- If n = 1, it is just the lexicogrphic product
--    F ↦ η · F
-- Otherwise, it is realised as follows:
-- take a coloring α : ℚ → {1, ..., n} where
-- every color occurs densely
-- Then if each color i is replaced by a
-- realizer for F_i, we get a realizer for
-- {F₁, ..., F_n}^η
-- (maybe a more pleasant way to phrase it is
-- as a lexicographic sum over ℚ, but it seems
-- that the essence of what I want to say always
-- gets lost in pedantry if I go this way)


-- Okay below is the standard Monad boilerplate for term syntax
instance Functor OrdTy where
  fmap f (OVar x) = OVar (f x)
  fmap f (LProdOm o) = LProdOm (fmap f o)
  fmap f (LProdOmOp o) = LProdOmOp (fmap f o)
  fmap f (LSum o r) = LSum (fmap f o) (fmap f r)
  fmap f (Shuffle os) = Shuffle (map (fmap f) os)
  fmap _ OOne = OOne
  fmap _ OZero = OZero

instance Applicative OrdTy where
  pure = OVar
  tf <*> tx = tf >>= \f ->
              tx >>= \x ->
              pure (f x)

instance Monad OrdTy where
  (OVar x) >>= f = f x
  (LProdOm o) >>= f = LProdOm (o >>= f)
  (LProdOmOp o) >>= f = LProdOmOp (o >>= f)
  (LSum o r) >>= f = LSum (o >>= f) (r >>= f)
  (Shuffle os) >>= f = Shuffle (map (>>= f) os)
  OOne >>= f = OOne
  OZero >>= f = OZero


-- Pretty-printing; in particular shuffles for n = 1 are simplified
-- as well as basic operations with OOne, and unneeded parentheses up to
-- associativity are dropped. However the optimizations are not too aggressive
-- and do not attempt to simplify terms that cannot be rewritten to simpler
-- terms.
--
-- Basic order types: 0,1, ω, -ω (so careful, - is not a binary operator), η
--   * ω is the order type of (ℕ,<)
--   * -ω is is the order type of (ℕ,>)
--   * η is the order type of (ℚ, <) (the unique dense linear order)
-- Binary operators: +, · 
-- Shuffle operator(k ≠ 1): {τ₁, ..., τ_k}η
showOrdTy :: Show a => OrdTy a -> String
showOrdTy OZero = "0"
showOrdTy OOne  = "1"
showOrdTy (LProdOm OOne) = "ω"
showOrdTy (LProdOmOp OOne) = "-ω"
showOrdTy (LProdOm x) = strCDot "ω" $ showOrdTyG x
showOrdTy (LProdOmOp x) = strCDot "-ω" $ showOrdTyG x
showOrdTy (Shuffle [OOne]) = "η"
showOrdTy (Shuffle [x])    = strCDot "η" $ showOrdTyG x
showOrdTy (Shuffle os) = "{ " ++ strList "," (map showOrdTy os) ++ " }η"
showOrdTy (OVar s) = show s
showOrdTy (LSum x y) = showOrdTy x ++ " + " ++ showOrdTy y

-- helper function for when adding parentheses might be necessary
showOrdTyG :: Show a => OrdTy a -> String
showOrdTyG (LSum x y) = strPar (showOrdTy (LSum x y))
showOrdTyG o          = showOrdTy o

-- Is the represented order type equal to 0?
isZero :: (t -> Bool) -> OrdTy t -> Bool
isZero p (OVar x) = p x
isZero p OZero = True
isZero p OOne  = False
isZero p (LSum o r) = isZero p o && isZero p r
isZero p (LProdOm o) = isZero p o
isZero p (LProdOmOp o) = isZero p o
isZero p (Shuffle os) = all (isZero p) os

-- Order type obtained by reversing the order
dualize :: OrdTy a -> OrdTy a
dualize (OVar x) = OVar x
dualize OOne = OOne
dualize (LProdOm o) = LProdOmOp (dualize o)
dualize (LProdOmOp o) = LProdOm (dualize o)
dualize OZero = OZero
dualize (Shuffle os) = Shuffle (map dualize os)
dualize (LSum o r) = LSum (dualize r) (dualize o)

-- n-ary sums
osum :: [OrdTy a] -> OrdTy a
osum []  = OZero
osum [o] = o
osum (o : os) = LSum o (osum os)

-- partial inverse to our bespoke n-ary function
osumInv :: OrdTy a -> [OrdTy a]
osumInv (LSum x y) = osumInv x ++ osumInv y
osumInv o = [o]

-- Is the order type finite? (the first argument says whether variables
-- are meant to be finite (not a very useful features :/))
oFinite :: (t -> Bool) -> OrdTy t -> Bool
oFinite p OZero = True
oFinite p OOne = True
oFinite p (LSum x y) = oFinite p x && oFinite p y
oFinite p (LProdOm x) = isZero p x
oFinite p (LProdOmOp x) = isZero p x
oFinite p (Shuffle os) = all (isZero p) os
oFinite p (OVar x) = p x

-- absorbsl τ σ is true if and only if τ · σ = σ
absorbsl :: Eq a => OrdTy a -> OrdTy a -> Bool
absorbsl OZero _ = True
absorbsl x (LProdOm y) = x == y || absorbsl x y
absorbsl OOne _ = False
absorbsl (OVar _) _ = False
absorbsl (LSum x y) z = absorbsl y z && absorbsl x z
absorbsl (Shuffle os) (Shuffle os') = os == os'
absorbsl (Shuffle _) _ = False
absorbsl _ _ = False

-- absorbsl τ σ is true if and only if σ · τ = σ
absorbsr :: Eq a => OrdTy a -> OrdTy a -> Bool
absorbsr x y = absorbsl (dualize x) (dualize y)

-- absorbsl τ σ is true if and only if σ · τ · σ = σ
absorbsi :: Eq a => OrdTy a -> OrdTy a -> OrdTy a -> Bool
absorbsi x (Shuffle osl) (Shuffle osr)
   | x `elem` osl && x `elem` osr = True
absorbsi x l r = any (\(xl, xr) -> absorbsr (osum xl) l && absorbsl (osum xr) r) (splits (osumInv x))
  where splits [] = [([],[])]
        splits (x : xs) = ([], x : xs) : map (\(a,b) -> (x:a, b)) (splits xs)

-- This is supposed to find a top-level rewriting to a simpler term and
-- just do it.
simplifyStep :: Ord a => OrdTy a -> OrdTy a
simplifyStep (LSum x y) | absorbsl x y = y
                        | absorbsr y x = x
simplifyStep (LProdOm OZero) = OZero
simplifyStep (LProdOmOp OZero) = OZero
simplifyStep (LProdOm o)
    | not (isZero (const True) o) && oFinite (const False) o
        = LProdOm OOne
simplifyStep (LProdOmOp o)
    | not (isZero (const True) o) && oFinite (const False) o
        = LProdOmOp OOne
simplifyStep (LProdOm (Shuffle os)) = Shuffle os
simplifyStep (LProdOmOp (LSum x y))
    | absorbsr x y = LProdOmOp y
    | absorbsi y x x = LSum (LProdOmOp x) y
simplifyStep (LProdOm (LSum x y))
    | absorbsl y x = LProdOm x
    | absorbsi x y y = LSum x (LProdOm y)
simplifyStep (LProdOm (LSum (Shuffle os) x))
    | x `elem` os = Shuffle os 
simplifyStep (LProdOmOp (LSum x (Shuffle os)))
    | x `elem` os = Shuffle os 
{- simplifyStep (LProdOm x) | osumInv x' /= osumInv x'' = LProdOm x''
  where x' = LSum x x
        x'' = simplifyStep x'
simplifyStep (LProdOmOp x) | osumInv x' /= osumInv x'' = LProdOmOp x''
  where x' = LSum x x
        x'' = simplifyStep x'
-}
simplifyStep (LSum y (LSum x z))
   | absorbsi x y z = LSum y z
simplifyStep (Shuffle (x : os)) =
      Shuffle (normalizeShuffle $ tryReduceShuffle [] x os)
     where tryReduceShuffleWith x os =
                extractOuterShuffle x >>= \(l,i,r) ->
                if l `sin` i && r `sin` i &&
                   all (\z -> z `sin` i || z `scompat` i) os then
                  Just i
                else
                  Nothing
           tryReduceShuffle os x os' =
             case tryReduceShuffleWith x (os ++ os') of
               Just is -> is
               Nothing -> case os' of
                           [] -> x : os
                           (y : ys) -> tryReduceShuffle (x : os) y ys
           normalizeShuffle = sort . nub . delete OZero
           sin z i = z `elem` i || z == OZero
           -- scompat is probably the implementation of the most subtle shuffle
           -- equation in the equational theory of those regular countable
           -- linear order types
           scompat z i = case extractOuterShuffle z of
                          Just (l, i', r) -> l `sin` i && r `sin` i &&
                                             l `sin` i' && r `sin` i' &&
                                             all (`sin` i) i' &&
                                             all (`sin` i') i
                          Nothing -> False
simplifyStep (Shuffle []) = OZero
-- if we are in none of these cases, we try to look for a sum pattern of size
-- two up to associativity and simplify that, otherwise same with a pattern
-- of size 3 (not super nice, could be beautified, but I just wanted to
-- point out that this is not very interesting)
simplifyStep o = if o == o' then
                   foldZip trySimplifyStepTriple (const o) (consTriples os)
                 else o'
  where o' = foldZip trySimplifyStepPair (const o) (consPairs os)
        os = osumInv o
        consPairs xs | length xs >= 3 = zip xs (tail xs)
                     | otherwise      = []
        consTriples xs | length xs >= 4 =
                                   zip (zip xs (tail xs)) (tail $ tail xs)
                       | otherwise      = []
        trySimplifyStepPair pre (o, o') post =
             if o''' == o'' then
               Nothing
             else
               Just . osum $ (reverse . map fst) pre ++ o''' : map snd post
          where o'' = LSum o o'
                o''' = simplifyStep o''
        trySimplifyStepTriple pre ((o, o'), o'') post =
             if osu == osus then
               Nothing
             else
               Just . osum $ (reverse . map (fst . fst)) pre ++ osus : map snd post
          where osu = LSum o (LSum o' o'')
                osus = simplifyStep osu

-- This is a helper function for simplifyStep that flattens expressions for
-- expressions that have the shape
--      τ + P^η + σ
--  into a more well behaved value Just (τ, P, σ) when possible
extractOuterShuffle :: OrdTy a -> Maybe (OrdTy a, [OrdTy a], OrdTy a)
extractOuterShuffle (LSum x (LSum (Shuffle os) y)) = Just (x, os, y)
extractOuterShuffle (Shuffle os) = Just (OZero, os, OZero)
extractOuterShuffle (LSum x (Shuffle os)) = Just (x, os, OZero)
extractOuterShuffle (LSum (Shuffle os) x) = Just (OZero, os, x)
extractOuterShuffle _ = Nothing

-- Rewrite the associativity of + one way
rewriteAssocStep :: OrdTy a -> OrdTy a
rewriteAssocStep (LSum (LSum x y) z) = LSum x (LSum y z)
rewriteAssocStep o = o

-- Rewrite the associativity of + the other way
rewriteAssocStepRev :: OrdTy a -> OrdTy a
rewriteAssocStepRev (LSum x (LSum y z)) = LSum (LSum x y) z
rewriteAssocStepRev o = o

-- Saturating up to congruence a function
saturateOrdTy :: (OrdTy a -> OrdTy a) -> OrdTy a -> OrdTy a
saturateOrdTy f (LSum x y) = f (LSum (saturateOrdTy f x) (saturateOrdTy f y))
saturateOrdTy f (LProdOm x) = f (LProdOm (saturateOrdTy f x))
saturateOrdTy f (LProdOmOp x) = f (LProdOmOp (saturateOrdTy f x))
saturateOrdTy f (Shuffle xs) = f (Shuffle (map (saturateOrdTy f) xs))
saturateOrdTy f o = f o

-- The overall simplification algorithm is essentially saturating associativity
-- rewriting for + everywhere and the bespoke simplifyStep above
simplify :: Ord a => OrdTy a -> OrdTy a
simplify = fixFin (saturateOrdTy rewriteAssocStep) .
           fixFin (saturateOrdTy simplifyStep) .
           fixFin (saturateOrdTy rewriteAssocStepRev) .
           fixFin (saturateOrdTy simplifyStep) .
           fixFin (saturateOrdTy rewriteAssocStep)
