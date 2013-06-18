module Century where

import Prelude hiding (zip,unzip)

data Datum
type Data  = [Datum]

data Candidate

data Value

{-# RULES "comp-assoc-L"  forall f g h. (f . g) . h = f . (g . h)    #-}
{-# RULES "comp-assoc-R"  forall f g h. f . (g . h) = (f . g) . h    #-}
{-# RULES "map-fusion"    forall f g.   map (f . g) = map f . map g  #-}
{-# RULES "map-id"                      map id      = id             #-}
{-# RULES "id-map"                      id          = map id         #-}
{-# RULES "comp-id-L"     forall f.     id . f      = f              #-}
{-# RULES "comp-R-id"     forall x.     extend x    = extend x . id  #-}

{-# RULES "comp-hack"     forall f g h k l.  f . g . h . k . l  = (f . g . h . k) . l  #-}

{-# RULES "foldr-fusion1"  filter (ok . value)    . foldr extend  [] = foldr extend' []  #-}
{-# RULES "foldr-fusion2"  map (fork (id, value)) . foldr extend' [] = foldr expand []   #-}

{-# RULES "6.2"            filter (good . value)          = filter (good . value) . filter (ok . value)           #-}
{-# RULES "6.3"  forall x. filter (ok . value) . extend x = filter (ok . value) . extend x . filter (ok . value)  #-}
{-# RULES "6.4"  forall x. map value . extend x           = modify x . map value                                  #-}

{-# RULES "6.5a"  forall f g.     fst . fork (f,g)     = f                                                 #-}
{-# RULES "6.5b"  forall f g.     snd . fork (f,g)     = g                                                 #-}
{-# RULES "6.6"   forall f g h.   fork (f,g) . h       = fork (f . h, g . h)                               #-}
{-# RULES "6.7"   forall f g h k. fork (f . h, g . k)  = cross (f,g) . fork (h,k)                          #-}
{-# RULES "6.8"   forall f g.     fork (map f , map g) = unzip . map (fork (f , g))                        #-}
{-# RULES "6.9"   forall f g.     map (fork (f , g))   = zip . fork (map f , map g)                        #-}
{-# RULES "6.10"  forall f g p.   map (fork (f,g)) . filter (p . g) = filter (p . snd) . map (fork (f,g))  #-}

-------------------------------------------------

solutions :: Data -> [Candidate]
solutions = filter (good . value) . candidates

candidates :: Data -> [Candidate]
candidates = foldr extend []

-------------------------------------------------

solutions2 :: Data -> [Candidate]
solutions2 = map fst . filter (good . snd) . candidates2

candidates2 :: Data -> [(Candidate, Value)]
candidates2 = map (fork (id, value)) . foldr extend' []

-------------------------------------------------

value :: Candidate -> Value
value = undefined

good :: Value -> Bool
good = undefined

ok :: Value -> Bool
ok = undefined

extend :: Datum -> [Candidate] -> [Candidate]
extend = undefined

extend' :: Datum -> [Candidate] -> [Candidate]
extend' x = filter (ok . value) . extend x

expand :: Datum -> [(Candidate, Value)] -> [(Candidate, Value)]
expand x = filter (ok . snd) . zip . cross (extend x, modify x) . unzip

-- This proof derives a definition of expand that validates RULE "foldr-fusion2"
{-# RULES "expand-spec"  forall x. map (fork (id, value)) . extend' x = expand x . map (fork (id, value)) #-}
expandSpecProof :: Datum -> [Candidate] -> [(Candidate, Value)]
expandSpecProof x =  map (fork (id, value)) . extend' x
                --   <=>
                --   expand x . map (fork (id, value))

modify :: Datum -> [Value] -> [Value]
modify = undefined

-------------------------------------------------

fork :: (a -> b, a -> c) -> a -> (b,c)
fork (f,g) a = (f a, g a)

cross :: (a -> x, b -> y) -> (a,b) -> (x,y)
cross (f,g) (a,b) = (f a, g b)

unzip :: [(a,b)] -> ([a],[b])
unzip = fork (map fst, map snd)

zip :: ([a],[b]) -> [(a,b)]
zip (a:as,b:bs) = (a,b) : zip (as,bs)

-------------------------------------------------