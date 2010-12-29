{- 
    Copyright 2010 Mario Blazevic

    This file is part of the Streaming Component Combinators (SCC) project.

    The SCC project is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
    License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later
    version.

    SCC is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
    of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along with SCC.  If not, see
    <http://www.gnu.org/licenses/>.
-}

-- | This module defines incremental parser. The exported 'Parser' type can provide partially constructed results at any
-- point during the parse.
-- 
-- Implementation is based on Brzozowski derivatives.

--{-# LANGUAGE Rank2Types, ExistentialQuantification #-}

module Text.ParserCombinators.Incremental
   (
    -- * The Parser type
    Parser, 
    -- * Using a Parser
    cofmapInput, feed, feedEof, feedAll, feedLongestPrefix, feedShortestPrefix, results, partialResults,
    -- * Parser primitives
    empty, eof, anyToken, acceptAll, count, prefixOf, whilePrefixOf, while,
    skip, optional, many, many1, manyTill,
    -- * Parser combinators
    choice, sequence, lookAhead, lookAheadNot, and
   )
where

import Prelude hiding (and, foldl, sequence)
import Control.Applicative (Applicative, pure, (<*>))
import Control.Monad (liftM2)
import Data.Monoid (Monoid, mempty, mappend)
import Data.Foldable (Foldable, foldl)

-- | This is a cofunctor data type for selecting a prefix of an input stream. If the next input item is acceptable, the
-- ticker function returns the ticker for the rest of the stream. If not, it returns 'Nothing'.
data Parser s r = Failure
                | Result r
                | ResultPart (r -> r) (Parser s r)
                | Choice (Parser s r) (Parser s r)
                | More (s -> Parser s r)
                | LookAhead (Parser s r)
                | LookAheadNot r (Parser s r)

feed :: s -> Parser s r -> Parser s r
feed _ Failure = Failure
feed _ Result{} = Failure
feed x (ResultPart r p) = resultPart r (feed x p)
feed x (Choice p1 p2) = choice (feed x p1) (feed x p2)
feed x (More f) = f x
feed x (LookAhead p) = lookAhead  (feed x p)
feed x (LookAheadNot r p) = lookAheadNot r (feed x p)

feedEof :: Parser s r -> Parser s r
feedEof Failure = Failure
feedEof p@Result{} = p
feedEof (ResultPart r p) = resultPart r (feedEof p)
feedEof (Choice p1 p2) = choice (feedEof p1) (feedEof p2)
feedEof More{} = Failure
feedEof (LookAhead p) = lookAhead (feedEof p)
feedEof (LookAheadNot r p) = lookAheadNot r (feedEof p)

feedAll :: Foldable f => f s -> Parser s r -> Parser s r
feedAll s p = foldl (flip feed) p s

feedShortestPrefix :: Foldable f => f s -> Parser s r -> ([s], Parser s r)
feedShortestPrefix s p = case foldl feedOrStore (Nothing, p) s
                         of (Nothing, p') -> ([], p')
                            (Just f, p') -> (f [], p')
   where feedOrStore :: (Maybe ([s] -> [s]), Parser s r) -> s -> (Maybe ([s] -> [s]), Parser s r)
         feedOrStore (Nothing, p) x = if null (results p) then (Nothing, feed x p) else (Just (x :), p)
         feedOrStore (Just store, p) x = (Just (store . (x :)), p)

feedLongestPrefix :: Foldable f => f s -> Parser s r -> ([s], Parser s r)
feedLongestPrefix s p = case foldl feedOrStore (Nothing, p) s
                        of (Nothing, p') -> ([], p')
                           (Just f, p') -> (f [], p')
   where feedOrStore :: (Maybe ([s] -> [s]), Parser s r) -> s -> (Maybe ([s] -> [s]), Parser s r)
         feedOrStore (Nothing, Failure) x = (Just (x :), Failure)
         feedOrStore (Nothing, p@Result{}) x = (Just (x :), p)
         feedOrStore (Nothing, p) x = case feed x p 
                                      of Failure -> (Just (x :), p)
                                         p'@Result{} -> (Just id, p')
                                         p' -> (Nothing, p')
         feedOrStore (Just store, p) x = (Just (store . (x :)), p)

feedListPrefix :: Parser s r -> [s] -> Either ([r], [s], Parser s r) (Parser s r)
feedListPrefix p l = case results p 
                     of [] -> case l of [] -> Right p
                                        x:xs -> feedListPrefix (feed x p) xs
                        rs -> Left (rs, l, p)

cofmapInput :: (a -> b) -> Parser b r -> Parser a r
cofmapInput f Failure = Failure
cofmapInput f (Result r) = Result r
cofmapInput f (ResultPart r p) = ResultPart r (cofmapInput f p)
cofmapInput f (Choice p1 p2) = Choice (cofmapInput f p1) (cofmapInput f p2)
cofmapInput f (More g) = More (cofmapInput f . g . f)
cofmapInput f (LookAhead p) = LookAhead (cofmapInput f p)
cofmapInput f (LookAheadNot r p) = LookAheadNot r (cofmapInput f p)

instance Functor (Parser s) where
   fmap f Failure = Failure
   fmap f (Result r) = Result (f r)
   fmap f p@ResultPart{} = resolve (fmap f) p
   fmap f (Choice p1 p2) = Choice (fmap f p1) (fmap f p2)
   fmap f (More g) = More (fmap f . g)
   fmap f (LookAhead p) = LookAhead (fmap f p)
   fmap f (LookAheadNot r p) = LookAheadNot (f r) (fmap f p)

instance Monad (Parser s) where
   return = Result
   Failure >>= _ = Failure
   Result r >>= f = f r
   Choice p1 p2 >>= f = choice (p1 >>= f) (p2 >>= f)
   More f >>= g = More (\x-> f x >>= g)
   p >>= f = resolve (>>= f) p

instance Applicative (Parser s) where
   pure = Result
   Failure <*> _ = Failure
   Result f <*> p = fmap f p
   Choice p1a p1b <*> p2 = choice (p1a <*> p2) (p1b <*> p2)
   More f <*> p = More (\x-> f x <*> p)
   p1 <*> p2 = resolve (<*> p2) p1

instance (Monoid r, Show r) => Show (Parser s r) where
   show Failure = "Failure"
   show (Result r) = "Result " ++ show r
   show (ResultPart f p) = "(ResultPart " ++ shows (f mempty) (" " ++ shows p ")")
   show (Choice p1 p2) = "(Choice " ++ shows p1 (" " ++ shows p2 ")")
   show (More f) = "More"
   show (LookAhead p) = "(LookAhead " ++ shows p ")"
   show (LookAheadNot r p) = "(LookAheadNot " ++ shows r (" " ++ shows p ")")

resolve :: (Parser s a -> Parser s b) -> Parser s a -> Parser s b
resolve f p = choice (f (feedEof p)) (More (\x-> f (feed x p))) 

results :: Parser s r -> [r]
results (Result r) = [r]
results (Choice p1 p2) = results p1 ++ results p2
results _ = []

partialResults :: Monoid r => Parser s r -> [(r, Parser s r)]
partialResults p = collect p [(mempty, p)]
   where collect (ResultPart f p) rest = [(f r, p') | (r, p') <- partialResults p] ++ rest
         collect (Choice p1 p2) rest = collect p1 (collect p2 rest)
         collect p rest = rest

choice :: Parser s r -> Parser s r -> Parser s r
choice Failure p = p
choice p Failure = p
choice (More f) (More g) = More (\x-> choice (f x) (g x))
choice p1 p2 = Choice p1 p2

lookAhead  :: Parser s r -> Parser s r
lookAhead  Failure = Failure
lookAhead  p@Result{} = p
lookAhead  (ResultPart r p) = resultPart r (lookAhead  p)
lookAhead  p@LookAhead{} = p
lookAhead  p@LookAheadNot{} = p
lookAhead  (Choice p1 p2) = choice (lookAhead p1) (lookAhead p2)
lookAhead  p = LookAhead p

lookAheadNot :: r -> Parser s r' -> Parser s r
lookAheadNot r Failure = Result r
lookAheadNot r Result{} = Failure
lookAheadNot r (ResultPart _ p) = lookAheadNot r p
lookAheadNot r (LookAhead p) = lookAheadNot r p
lookAheadNot r (LookAheadNot _ p) = lookAhead (fmap (const r) p)
lookAheadNot r p = LookAheadNot r (fmap (const r) p)

resultPart :: (r -> r) -> Parser s r -> Parser s r
resultPart _ Failure = Failure
resultPart f (Result r) = Result (f r)
resultPart f (ResultPart g p) = ResultPart (f . g) p
resultPart f p = ResultPart f p

sequence :: Monoid r => Parser s r -> Parser s r -> Parser s r
sequence Failure _ = Failure
sequence (Result r) p = resultPart (mappend r) p
sequence (ResultPart r p1) p2 = resultPart r (sequence p1 p2)
sequence (Choice p1a p1b) p2 = choice (sequence p1a p2) (sequence p1b p2)
sequence (More f) p = More (\x-> sequence (f x) p)
sequence p1@LookAhead{} p2 = choice (sequence (feedEof p1) p2) (More (\x-> sequence (feed x p1) (feed x p2)))
sequence p1@LookAheadNot{} p2 = choice (sequence (feedEof p1) p2) (More (\x-> sequence (feed x p1) (feed x p2)))

-- | A parser that succeeds without consuming any input.
empty :: Monoid r => Parser s r
empty = Result mempty

-- | A parser that fails on any input.
eof :: Monoid r => Parser s r
eof = lookAheadNot mempty anyToken

-- | A parser that accepts a single input item.
anyToken :: Parser s s
anyToken = More Result

-- | A parser that accepts a given number of input items.
count :: Int -> Parser s [s]
count n | n > 0 = More (\x-> resultPart (x:) $ count (pred n))
        | otherwise = Result []

-- | A parser that accepts the longest prefix of input that matches a prefix of the argument list.
prefixOf :: Eq x => [x] -> Parser x [x]
prefixOf list = whilePrefixOf (map (==) list)

-- | A parser that accepts a prefix of input as long as each item satisfies the predicate at the same position in the
-- argument list. The length of the predicate list thus determines the maximum number of acepted values.
whilePrefixOf :: [x -> Bool] -> Parser x [x]
whilePrefixOf (p : rest) = 
   Choice (More $ \x-> if p x then resultPart (x:) (whilePrefixOf rest) else Failure) (Result [])
whilePrefixOf [] = Result []

-- | A parser that accepts all input as long as it matches the given predicate.
while :: (x -> Bool) -> Parser x [x]
while p = t
   where t = Choice (More (\x-> if p x then ResultPart (x:) t else Failure)) (Result [])

optional :: Monoid r => Parser s r -> Parser s r
optional p = Choice p (Result mempty)

skip :: Monoid r => Parser s r' -> Parser s r
skip p = fmap (const mempty) p

many :: Monoid r => Parser s r -> Parser s r
many p = optional (many1 p)

many1 :: Monoid r => Parser s r -> Parser s r
many1 p = sequence p (many p)

manyTill :: Monoid r => Parser s r -> Parser s r' -> Parser s r
manyTill next end = t
   where t = choice (skip end) (sequence next t)

-- | A parser that accepts all input.
acceptAll :: Parser s [s]
acceptAll = choice (More $ \x-> ResultPart (x:) acceptAll) (Result mempty)

-- | Parallel parser conjunction: the result of the combinator keeps accepting input as long as both arguments do.
and :: (Monoid r1, Monoid r2) => Parser s r1 -> Parser s r2 -> Parser s (r1, r2)
Failure `and` _ = Failure
_ `and` Failure = Failure
p `and` Result r = fmap (\x-> (x, r)) (feedEof p)
Result r `and` p = fmap (\x-> (r, x)) (feedEof p)
ResultPart f p1 `and` p2 = fmap (\(r1, r2)-> (f r1, r2)) (p1 `and` p2)
p1 `and` ResultPart f p2 = fmap (\(r1, r2)-> (r1, f r2)) (p1 `and` p2)
Choice p1a p1b `and` p2 = choice (p1a `and` p2) (p1b `and` p2)
p1 `and` Choice p2a p2b = choice (p1 `and` p2a) (p1 `and` p2b)
More f `and` p = More (\x-> f x `and` feed x p)
p `and` More f = More (\x-> feed x p `and` f x)
p1 `and` p2 = choice (feedEof p1 `and` feedEof p2) (More (\x-> feed x p1 `and` feed x p2))
