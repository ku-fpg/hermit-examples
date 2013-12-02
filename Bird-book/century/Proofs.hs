module Proofs where

import Century

-------------------------------------------------

-- These definitions are just for testing the proofs.

-- This proof derives a definition of expand that validates RULE "foldr-fusion2"
-- See file "FusionPrecondition"
proofExpandSpec :: Datum -> [Candidate] -> [(Candidate, Value)]
proofExpandSpec x =  map (fork (id, value)) . extend' x
                --   <=>
                --   expand x . map (fork (id, value))

proof_6_5a :: (a -> b) -> (a -> c) -> a -> b
proof_6_5a = \ f g -> fst . fork (f,g)
           -- =>
           -- f

proof_6_5b :: (a -> b) -> (a -> c) -> a -> c
proof_6_5b = \ f g -> snd . fork (f,g)
           -- =>
           -- g

proof_6_6 :: (b -> c) -> (b -> d) -> (a -> b) -> a -> (c,d)
proof_6_6 = \ f g h -> fork (f,g) . h
          -- =>
          -- fork (f . h, g . h)

proof_6_6' :: (b -> c) -> (b -> d) -> (a -> b) -> a -> (c,d)
proof_6_6' = \ f g h -> fork (f . h, g . h)
           -- =>
           -- fork (f,g) . h

proof_6_7 :: (b -> y) -> (c -> z) -> (a -> b) -> (a -> c) -> a -> (y,z)
proof_6_7 = \ f g h k -> fork (f . h, g . k)
          -- =>
          -- cross (f,g) . fork (h,k)

proof_6_7' :: (b -> y) -> (c -> z) -> (a -> b) -> (a -> c) -> a -> (y,z)
proof_6_7' = \ f g h k -> cross (f,g) . fork (h,k)
           -- =>
           -- fork (f . h, g . k)

-------------------------------------------------
