-- A few helper functions. Maybe it should be split around and merged with
-- other things, but eh.


module MyPrelude where
import Data.List


-- Meant to represent an empty datatype; did not check how Haskell dealt with
-- pattern-matching over empty datatypes, assumed pessimistically that the
-- situation was as dismal as 2012 OCaml and just did whatever
data Void

instance Show Void where
  show x = error "aaaa"

instance Eq Void where
  x == y = error "aaaa"

instance Ord Void where
  x <= y = error "aaaa"

foldZip :: ([a] -> a -> [a] -> Maybe b)-> ([a] -> b) -> [a] -> b
foldZip it end xs = foldZipAcc [] xs
  where foldZipAcc acc [] = end acc
        foldZipAcc acc (x : xs) = case it acc x xs of
                                   Just r  -> r
                                   Nothing -> foldZipAcc (x : acc) xs

funOfList :: Eq a => [(a,b)] -> a -> Maybe b
funOfList xs a = find ((== a) . fst) xs >>= \(_,b) -> Just b

tFunOfList :: (Eq a, Eq b1) => [(a, b1, b2)] -> a -> Maybe b1 -> Maybe b2
tFunOfList xs a q = q >>= \r -> funOfList [((x,y), z) | (x,y,z) <- xs] $ (a,r)

-- Stuff for pretty printing below

-- For (lexicographic) product of order types
strCDot :: [Char] -> [Char] -> [Char]
strCDot x y = x ++ " · " ++ y

-- Parenthesizing
strPar :: [Char] -> [Char]
strPar x = "(" ++ x ++ ")"

-- bla-separated lists; first argument is the delimiter type
strList :: [Char] -> [[Char]] -> [Char]
strList delim [] = ""
strList delim [x] = x
strList delim (x : xs) = x ++ delim ++ " " ++ strList delim xs

-- A finitary fixpoint combinator
fixFin :: Eq t => (t -> t) -> t -> t
fixFin f x | f x == x  = x
           | otherwise = fixFin f (f x)
