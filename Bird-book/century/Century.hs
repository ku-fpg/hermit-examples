module Century where

import Prelude hiding (zip,unzip,map,id,filter)

import Data.List (intercalate)

-------------------------------------------------

{-# RULES "comp-id-L"     [1] forall f.     id . f      = f              #-}
{-# RULES "comp-id-R"     [1] forall f.     f . id      = f              #-}
{-# RULES "comp-assoc"    [1] forall f g h. (f . g) . h = f . (g . h)    #-}

-- This is ugly.
{-# RULES "comp-assoc4"   [1] forall f g h k l.  f . g . h . k . l  = (f . g . h . k) . l  #-}

{-# RULES "map-fusion"     [1] forall f g.     map (f . g)    = map f . map g       #-}
{-# RULES "map-fusion-eta" [1] forall f g xs.  map (f . g) xs = (map f . map g) xs  #-}

{-# RULES "map-id"        [1]               map id      = id   #-}
{-# RULES "map-id-eta"    [1] forall xs.    map id xs   = xs   #-}

{-# RULES "map-strict"    [1] forall f.  map f undefined    = undefined  #-}
{-# RULES "filter-strict" [1] forall p.  filter p undefined = undefined  #-}

{-# RULES "6.5a"  [1] forall f g.     fst . fork (f,g)     = f                             #-}
{-# RULES "6.5b"  [1] forall f g.     snd . fork (f,g)     = g                             #-}
{-# RULES "6.6"   [1] forall f g h.   fork (f,g) . h       = fork (f . h, g . h)           #-}
{-# RULES "6.7"   [1] forall f g h k. fork (f . h, g . k)  = cross (f,g) . fork (h,k)      #-}
{-# RULES "6.8"   [1] forall f g.     fork (map f , map g) = unzip . map (fork (f , g))    #-}

{-# RULES "6.9"     [1] forall f g.     map (fork (f , g))      =  zip . fork (map f , map g)   #-}
{-# RULES "6.9-eta" [1] forall f g xs.  map (fork (f , g)) xs   =  zip (map f xs , map g xs)    #-}

{-# RULES "fork-fst-snd" [1]  fork (fst , snd)  =  id  #-}
{-# RULES "zip-unzip"    [1]  zip . unzip  =  id       #-}

{-# RULES "6.10"      [1] forall f g p.      map (fork (f,g)) . filter (p . g)     =  filter (p . snd) . map (fork (f,g))     #-}
{-# RULES "6.10-eta"  [1] forall f g p xs.   map (fork (f,g)) (filter (p . g) xs)  =  filter (p . snd) (map (fork (f,g)) xs)  #-}

{-# RULES "expand-spec"  [1] forall x. map (fork (id, value)) . extend' x = expand x . map (fork (id, value)) #-}

{-# RULES "foldr-fusion-1-cond-i"    [1]  filter (ok . value) undefined  =  undefined  #-}
{-# RULES "foldr-fusion-1-cond-ii"   [1]  filter (ok . value) []         =  []         #-}
{-# RULES "foldr-fusion-1-cond-iii"  [1]  forall x y.  filter (ok . value) (extend x y)  =  extend' x (filter (ok . value) y)  #-}

{-# RULES "foldr-fusion-2-cond-i"    [1]  map (fork (id, value)) undefined  =  undefined  #-}
{-# RULES "foldr-fusion-2-cond-ii"   [1]  map (fork (id, value)) []         =  []         #-}
{-# RULES "foldr-fusion-2-cond-iii"  [1]  forall x y.  map (fork (id, value)) (extend' x y)  =  expand x (map (fork (id, value)) y)  #-}



{-# RULES "6.2"  [1]           filter (good . value)          = filter (good . value) . filter (ok . value)           #-}
{-# RULES "6.3"  [1] forall x. filter (ok . value) . extend x = filter (ok . value) . extend x . filter (ok . value)  #-}
{-# RULES "6.4"  [1] forall x. map value . extend x           = modify x . map value                                  #-}

{-# RULES "foldr-fusion-1" [1] filter (ok . value)    . foldr extend  [] = foldr extend' []  #-}
{-# RULES "foldr-fusion-2" [1] map (fork (id, value)) . foldr extend' [] = foldr expand []   #-}

-------------------------------------------------

type Expression = [Term]
type Term       = [Factor]
type Factor     = [Digit]
type Digit      = Int

type Value = (Int,Int,Int,Int)

-------------------------------------------------

c :: Int
c = 100

good :: Value -> Bool
good (k,f,t,e) = (f*t + e == c)

ok :: Value -> Bool
ok (k,f,t,e) = (f*t + e <= c)

-------------------------------------------------

valExpr :: Expression -> Int
valExpr = sum . map valTerm

valTerm :: Term -> Int
valTerm = product . map valFact

valFact :: Factor -> Int
valFact = foldl1 (\ n d -> 10 * n + d)

-------------------------------------------------

-- ds*fs + ts
--
-- ds is the digits of the leading factor
-- fs is the tail of the factors of the leading term
-- (ds*fs) is the leading term
-- ts is the tail of the terms
-- The first tuple component is the magnitude of any new digit that will be added to "ds".  E.g.  if ds = 777, then the first tuple component will be 1000.
value :: Expression -> Value
value ((ds:fs):ts) = (10^n, valFact ds, valTerm fs, valExpr ts)
  where
    n = length ds

extend :: Digit -> [Expression] -> [Expression]
extend x []  = [[[[x]]]]
extend x es  = concatMap (glue x) es

glue :: Digit -> Expression -> [Expression]
glue x ((xs : xss) : xsss) = [((x:xs):xss):xsss,
                              ([x]:xs:xss):xsss,
                              [[x]]:(xs:xss):xsss]

extend' :: Digit -> [Expression] -> [Expression]
extend' x = filter (ok . value) . extend x

expand :: Digit -> [(Expression, Value)] -> [(Expression, Value)]
expand x = filter (ok . snd) . zip . cross (extend x, modify x) . unzip

-- Note: error in the textbook on P39.
-- The textbook states:
-- modify x (k,f,t,e) = [(10*k,k*x+f,t,e),(10,x,f*t,e),(10,x,1,f*t+e)]
-- which does not type check due to the absence of concatMap

modify :: Digit -> [Value] -> [Value]
modify d = concatMap (modify' d)

modify' :: Digit -> Value -> [Value]
modify' d (k,f,t,e) = [(10*k,k*d+f,t,e),(10,d,f*t,e),(10,d,1,f*t+e)]

-- Given:  (ds * fs) + ts
-- A digit "d" can be added as follows:
--   dds * fs + ts
--   (d * ds * fs) + ts
--   d + (ds * fs) + ts

-------------------------------------------------

expressions :: [Digit] -> [Expression]
expressions = foldr extend []

solutions :: [Digit] -> [Expression]
solutions = filter (good . value) . expressions

-------------------------------------------------

solutions2 :: [Digit] -> [Expression]
solutions2 = map fst . filter (good . snd) . expressions2

expressions2 :: [Digit] -> [(Expression, Value)]
expressions2 = map (fork (id, value)) . foldr extend' []

-------------------------------------------------

id :: a -> a
id a = a

map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (a:as) = f a : map f as

filter :: (a -> Bool) -> [a] -> [a]
filter p []     = []
filter p (a:as) = let bs = filter p as
                   in if p a then a : bs else bs

fork :: (a -> b, a -> c) -> a -> (b,c)
fork (f,g) a = (f a, g a)

cross :: (a -> x, b -> y) -> (a,b) -> (x,y)
cross (f,g) (a,b) = (f a, g b)

unzip :: [(a,b)] -> ([a],[b])
unzip = fork (map fst, map snd)

zip :: ([a],[b]) -> [(a,b)]
zip (a:as,b:bs) = (a,b) : zip (as,bs)
zip (_,_)       = []

-------------------------------------------------

showExpr :: Expression -> String
showExpr =  intercalate " + " . map showTerm

showTerm :: Term -> String
showTerm =  intercalate " * " . map showFactor

showFactor :: Factor -> String
showFactor =  concatMap show

showDigit :: Digit -> String
showDigit =  show

-------------------------------------------------
