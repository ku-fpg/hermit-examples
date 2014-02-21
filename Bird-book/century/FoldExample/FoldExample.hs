module FoldExample where

-- | foldr fusion
--
-- strict f    /\    f a = b    /\    forall x y. f (g x y) = h x (f y)
-----------------------------------------------------------------------
--           f . foldr g a = foldr h b
--

{-# RULES "Fusion Condition 1" [1]  f undefined = undefined  #-}

{-# RULES "Fusion Condition 2" [1]  f a = b  #-}

{-# RULES "Fusion Condition 3" [1]  forall x y.  f (g x y) = h x (f y)  #-}

data A = A1 | A2
data B = B1 | B2

f :: A -> B
f A1 = B1
f A2 = B2

g :: Int -> A -> A
g n a0 = if n > 0 then A2 else a0

h :: Int -> B -> B
h n b0 = if n > 0 then B2 else b0

a :: A
a = A1

b :: B
b = B1

lr :: [Int] -> B
lr = f . foldr g a

rl :: [Int] -> B
rl = foldr h b
