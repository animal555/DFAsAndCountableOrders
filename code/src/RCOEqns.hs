{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

-- This is probably the most interesting module in terms of maths hidden
-- under the carpet (besides the simplification algo maybe, but that's not
-- supposed to be the focus).
--
-- Here we look at solving systems of equations of order types of the kind
--
-- X₁  = τ₁(X₁,...,X_n)
-- ...
-- X_n = τ_n(X₁,...,X_n)
--
-- where τ_i are regular countable linear order terms. It turns out we can
-- find closed terms σ₁, ..., σ_n such that
-- σ₁  = τ₁(σ₁, ..., σ_n)
-- ...
-- σ_n = τ_n(σ₁, ..., σ_n)
--
-- These tuples of terms are not unique (think of X = 1 + X), but there is a
-- canonical minimal one. To define it properly, one should regard that system
-- of equations as an endofunctor of the category LinOrd × ... × LinOrd and
-- say that this corresponds to the carriers initial algebras for it. But there
-- is probably also a way to define a metric on the order types and say
-- "minimal", although that sounds lamer and to assume much more work (e.g.,
-- that the simplification algo in the other file is correct, etc).
--
-- I don't like the historic solution by Heilbrunner that still seems to be in
-- use in the 2010s for aesthetics reasons. It sort of does a tedious analysis
-- of the dependency graph of the variables, and solve iteratively strongly
-- connected components by doing a disstressing amount of substitutions. But it
-- seems it can lead to some PTIME algorithms to decide the isomorphism of
-- order types given by automata if we do some smart succint representation of
-- those regular order types.
--
-- Here I use a solution I came up with, which I suspect was already known
-- (probably by Blum/Esik among others I would think?)
-- Maybe there is some advantage to Heilbrunner's solution, but it is not
-- obvious to me; without modification to the grammar of regular order types,
-- they are both exponential (that can be size of the solution). But it might
-- be that there is already huge gains already if we do hash-consing (and it
-- is not clear to me if this can lead to a polytime solution to the
-- isomorphism problem without having to introduce more non-typically-haskelly
-- technology)
--
-- This solutions is easier to understand: we solve parameterized equations
--    X = τ(X, Y₁, ..., Y_k)
-- i.e., we find a minimal σ(Y₁, ..., Y_k) such that
--    σ(Y₁, ..., Y_k) = τ(σ(Y₁,...,Y_k), Y₁, ..., Y_k)
--
-- (formally we look at this as an endofunctor over (LinOrd^k → LinOrd) and
-- compute part of a representation for the initial algebra)
--
-- Turns out that doing that is fairly cute and easy actually! And the
-- generalization is worthwhile I think, since it is not about just initial
-- algebras, but parameterized initial algebras.

module RCOEqns where

import MyPrelude
import Data.List
import Data.Maybe
import RCO


-- Helper function to get the list of variables in a term (with multiplicities,
-- although the order should not be regarded as *too* meaningful)
getVars :: OrdTy b -> [b]
getVars (OVar x) = [x]
getVars (LProdOm o) = getVars o
getVars (LProdOmOp o) = getVars o
getVars (LSum o r) = getVars o ++ getVars r
getVars (Shuffle os) = concatMap getVars os
getVars _ = []

-- Does a variable occur in a term?
occurs :: Eq a => a -> OrdTy a -> Bool
occurs x o = x `elem` getVars o

-- Does a variable occur exactly once in a term?
occursOnce :: Eq a => a -> OrdTy a -> Bool
occursOnce x o = length (filter (== x) $ getVars o) == 1

-- In what follows, a term t of type OrdTy(Maybe a) will be regarded as
-- a term with a special variable Nothing, while the variables Just a will be
-- thought of as parameters.
--
-- We will be looking to compute a solution to "Nothing = t" using the
-- non-Nothing variables essentially

-- What is the largest prefix of the parameterized order type before the
-- variable Nothing occurs?
nPrefix :: Eq b => OrdTy (Maybe b) -> OrdTy b
nPrefix (OVar Nothing) = OZero
nPrefix o | not $ occurs Nothing o = fmap fromJust o
nPrefix (LSum o r) | occurs Nothing o = nPrefix o
                   | otherwise = LSum (nPrefix o) (nPrefix r)
nPrefix (LProdOm o) = nPrefix o
nPrefix (LProdOmOp o) = OZero
nPrefix (Shuffle os) = OZero
nPrefix o = fmap fromJust o


-- Dual problem 
nSuffix :: Eq a => OrdTy (Maybe a) -> OrdTy a
nSuffix = dualize . nPrefix . dualize

-- Now what are the order types that may occur *between* two occurences of
-- Nothing?
nInfixes :: Eq b => OrdTy (Maybe b) -> [OrdTy b]
nInfixes (LSum o r) = nInfixes o ++ nInfixes r ++ interstice
  where interstice | occurs Nothing o &&
                     occurs Nothing r = [LSum (nSuffix o) (nPrefix r)]
                   | otherwise = []
nInfixes (LProdOm o)   = nInfixes (LSum o o)
nInfixes (LProdOmOp o) = nInfixes (LSum o o)
nInfixes (Shuffle os) = concatMap nInfixes os
nInfixes _ = []


-- Is there a minimal occurence of Nothing in the term?
-- Note that having an occurence does not guarantee having a minimal one.
-- For instance, there is no minimal occurence of X in -ω · X! But there is
-- in, say η · Y + ω · (1 + X) 
hasMinimalEVar :: Eq a => OrdTy (Maybe a) -> Bool
hasMinimalEVar (OVar Nothing) = True
hasMinimalEVar (LSum o o') = hasMinimalEVar o ||
                             not (occurs Nothing o) &&
                             hasMinimalEVar o'
hasMinimalEVar OOne = False
hasMinimalEVar OZero = False
hasMinimalEVar (LProdOm o) = hasMinimalEVar o
hasMinimalEVar (LProdOmOp _) = False
hasMinimalEVar (Shuffle _) = False
hasMinimalEVar (OVar _) = False

-- Dual problem
hasMaximalEvar :: Eq a => OrdTy (Maybe a) -> Bool
hasMaximalEvar = hasMinimalEVar . dualize 

-- subst t x u is t[u/x] as usual
subst :: Eq b => OrdTy b -> b -> OrdTy b -> OrdTy b
subst o x o' = o >>= \z -> if z == x then o' else OVar z

-- The workhorse that allows to compute parameterized solutions!
-- It's fun maths, but maybe a bit long for a thorough explanation in a
-- comment
initialSol :: Ord a => OrdTy (Maybe a) -> OrdTy a
initialSol o | not $ occurs Nothing o = fmap fromJust o
             | otherwise              = osum [pre, mid, post]
      where pre  | hasMinimalEVar o = LProdOm (nPrefix o)
                 | otherwise        = nPrefix o
            post | hasMaximalEvar o = LProdOmOp (nSuffix o)
                 | otherwise        = nSuffix o
            mid = Shuffle (nInfixes (subst o Nothing oneStepUnroll))
            oneStepUnroll = osum [fmap Just pre, OVar Nothing, fmap Just post]

-- OK now the rest of the file is the boring part of just using this + a bunch
-- of substitutions to get solutions to system of equations. Since the size
-- of intermediate expressions get big (and inspected by all the helpers
-- functions above), I simplify intermediate parameterized solutions to gain
-- a bit in efficiency (although simplifying is not that trivial either).
--
-- It would be faster to do hash-consing + memoization for all functions
-- without simplifying probably, but I am too lazy to do that

solveEqnSys :: Ord a => [(a, OrdTy a)] -> [(a, OrdTy Void)]
solveEqnSys eqns = map (\(v,s) -> (v, s >> OZero)) $ solveEqnSysR eqns

solveEqnSysR :: Ord a => [(a, OrdTy a)] -> [(a, OrdTy a)]
solveEqnSysR [] = []
solveEqnSysR ((var , rhs) : eqns) = (var, sol) : sols 
  where
    paramSol  = simplify . initialSol . simplify $ rhs'
    rhs'      = eqnToHoleOrdTy var rhs
    eqns'     = map (\(v, rhs) -> (v, subst rhs var paramSol)) eqns
    sols      = solveEqnSysR eqns'
    sol       = foldr (\(v, sol') e -> subst e v sol') paramSol sols

eqnToHoleOrdTy :: (Functor f, Eq a) => a -> f a -> f (Maybe a)
eqnToHoleOrdTy var =
    fmap (\z -> if z == var then Nothing else Just z) 
