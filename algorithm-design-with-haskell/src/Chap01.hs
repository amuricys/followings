{-# LANGUAGE NoImplicitPrelude #-}

module Chap01 where

import Prelude (Ord, Maybe(..), (>), (-), (+), (*), (^), Int, Bool(..), flip, (.), undefined, (==), (&&), (/), Double, fromIntegral, ($))
import Data.List (foldl, foldr, (++), null, concat)

head' :: [a] -> a
head' = foldr (<<) undefined
  where x << _ = x

{-
head' (x:xs) = foldr (<<) undefined (x:xs)
            = x << foldr (<<) undefined xs
            = x -- << ignores its second argument
-}

concat1,concat2 ::[[a]] -> [a] 
concat1 = foldr (++) []
concat2 = foldl (++) []

perms1 :: [a] -> [[a]]
perms1 [] = [[]]
perms1 (x:xs) = [zs | ys <- perms1 xs, zs <- inserts x ys]

inserts :: a -> [a] -> [[a]]
inserts x [] = [[x]]
inserts x (h:hs) = (x : h : hs) : map (h :) (inserts x hs)

perms2 :: [a] -> [[a]]
perms2 xs = [x : zs | (x, ys) <- picks xs, zs <- perms2 ys]

picks :: [a] -> [(a, [a])]
picks [] = []
picks (x:xs) = (x,xs) : [(y, x : ys) | (y, ys) <- picks xs]

hmm :: (a -> c -> c) -> c -> [[a]] -> c
hmm f e l = foldr f e . concat $ l
  where
    k = map (foldr f e) l 

well f e xs ys = foldr f e (xs ++ ys)
  where
      obv = foldr f (foldr f e ys) xs

----- Exercises
-- 1.1
maximum :: Ord a => [a] -> Maybe a
maximum [] = Nothing
maximum (x:xs) = Just (foldl (\acc x -> if x > acc then x else acc) x xs)
take' :: [a] -> Int -> [a]
take' x      0 = x
take' []     _ = []
take' (x:xs) n = x : take' xs (n - 1)

-- 1.2
uncons :: [a] -> Maybe (a, [a])
uncons [] = Nothing
uncons (x:xs) = Just (x, xs)

-- 1.3
wrap :: a -> [a]
wrap = (: [])
unwrap :: [a] -> a
unwrap [x] = x -- tf? terrible
single :: [a] -> Bool
single [_] = True
single _ = False

-- 1.4
-- traverses list and builds up the output
reverse :: [a] -> [a]
reverse = foldl (flip (:)) []

-- 1.5
map :: (a -> b) -> [a] -> [b]
map f = foldr (\x acc -> f x : acc) []
filter :: (a -> Bool) -> [a] -> [a]
filter p = foldr (\x acc -> if p x then x : acc else acc) []
-- 1.6
foldfilter :: (a -> b -> b) -> (a -> Bool) -> b -> [a] -> b
foldfilter f p = 
    -- this: `foldr f e . filter p` as a single fold is
    foldr (\x acc -> if p x then f x acc else acc)
-- 1.7
takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile p = foldr (<<) []
  where x << k = if p x then x : k else [] -- very nice
-- 1.8
dropWhileEnd :: (a -> Bool) -> [a] -> [a]
dropWhileEnd p = foldr (<<) []
  where x << k = if p x && null k then k else x : k -- had to get tip to use null k
-- 1.9
{-
Pretty sure it's that it traverses the list a billion times.
every init call has to go to the final element so n + n - 1 + n - 2...
operations.
-}
-- 1.10
{-
When ⊕ is commutative and associative you have it,
and also when ⊕ is associative and _ ⊕ e = id.
-}
-- 1.11
-- using shiftl and shiftr would have been much better
integer :: [Int] -> Int
integer = snd . foldr (\x (i,s) -> (i + 1, (x * 10 ^ i) + s)) (0,0)
  where snd (_, a) = a
fraction :: [Int] -> Double
fraction = snd . foldl (\(i,s) x -> (i + 1, (fromIntegral x / (10 ^ fromIntegral i)) + s)) (0,0.0)
  where snd (_, a) = a
