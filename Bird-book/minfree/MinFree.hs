module Main where

import Data.Array

--------------------------------------

-- Specification

minfree :: [Int] -> Int
minfree xs = head ([0..] \\ xs)

(\\) :: Eq a => [a] -> [a] -> [a]
us \\ vs = filter (`notElem` vs) us

--------------------------------------

minfree2 :: [Int] -> Int
minfree2 = search . checklist

search :: Array Int Bool -> Int
search = length . takeWhile id . elems

checklist :: [Int] -> Array Int Bool
checklist xs = let n = length xs
                in accumArray
                     (||)  -- element update function
                     False -- initial value of each element
                     (0,n) -- index range
                     (zip (filter (<= n) xs) (repeat True)) -- list of elements to update

--------------------------------------

{-# RULES "removing-dist " forall as bs cs. (as ++ bs) \\ cs = (as \\ cs) ++ (bs \\ cs) #-}
{-# RULES "removing-split" forall as bs cs. as \\ (bs ++ cs) = (as \\ bs) \\ cs         #-}
{-# RULES "removing-assoc" forall as bs cs. (as \\ bs) \\ cs = (as \\ cs) \\ bs         #-}

--------------------------------------

eg6 :: [Int]
eg6 = [0,5,3,4,1,7,2,8]

test6 :: Bool
test6 =    minfree  eg6 == 6
        && minfree2 eg6 == 6

--------------------------------------
