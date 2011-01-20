{- 
    Copyright 2010-2011 Mario Blazevic

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
    feed, feedEof, feedAll, feedListPrefix, feedLongestPrefix, feedShortestPrefix, results, resultPrefix,
    -- * Parser primitives
    empty, eof, anyToken, count, acceptAll, string, prefixOf, whilePrefixOf, while,
    skip, optional, optionMaybe, many, many1, manyTill,
    -- * Parser combinators
    (><), (>><), lookAhead, lookAheadNot, longest, and, andThen
   )
where

import Prelude hiding (and, foldl)
import Control.Applicative (Applicative (pure, (<*>)), Alternative (empty, (<|>), some, many))
import Control.Monad (Functor (fmap), Monad (return, (>>=), (>>)), MonadPlus (mzero, mplus), liftM2)
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid, mempty, mappend)
import Data.Foldable (Foldable, foldl, toList)

-- | This is a cofunctor data type for selecting a prefix of an input stream. If the next input item is acceptable, the
-- ticker function returns the ticker for the rest of the stream. If not, it returns 'Nothing'.
data Parser s r = Failure
                | Result (InputTail s) r
                | ResultPart (r -> r) (Parser s r)
                | Choice (Parser s r) (Parser s r)
                | CommitedLeftChoice (Parser s r) (Parser s r)
                | More (s -> Parser s r)
                | LookAhead (InputTail s) (Parser s r)
                | LookAheadNot (InputTail s) r (Parser s r)

type InputTail s = [s] -> [s]

feed :: s -> Parser s r -> Parser s r
feed _ Failure = Failure
feed x (Result t r) = Result (t . (x:)) r
feed x (ResultPart r p) = resultPart r (feed x p)
feed x (Choice p1 p2) = feed x p1 <|> feed x p2
feed x (CommitedLeftChoice p1 p2) = feed x p1 <<|> feed x p2
feed x (More f) = f x
feed x (LookAhead t p) = lookAheadInto (t . (x:)) (feed x p)
feed x (LookAheadNot t r p) = lookAheadNotInto (t . (x:)) r (feed x p)

feedEof :: Parser s r -> Parser s r
feedEof Failure = Failure
feedEof p@Result{} = p
feedEof (ResultPart r p) = resultPart r (feedEof p)
feedEof (Choice p1 p2) = feedEof p1 <|> feedEof p2
feedEof (CommitedLeftChoice p1 p2) = feedEof p1 <<|> feedEof p2
feedEof More{} = Failure
feedEof (LookAhead t p) = lookAheadInto t (feedEof p)
feedEof (LookAheadNot t r p) = lookAheadNotInto t r (feedEof p)

feedAll :: Foldable f => f s -> Parser s r -> Parser s r
feedAll s p = foldl (flip feed) p s

feedShortestPrefix :: Foldable f => f s -> Parser s r -> ([s], Parser s r)
feedShortestPrefix s p = case foldl feedOrStore (Nothing, p) s
                         of (Nothing, p') -> ([], p')
                            (Just f, p') -> (f [], p')
   where feedOrStore :: (Maybe ([s] -> [s]), Parser s r) -> s -> (Maybe ([s] -> [s]), Parser s r)
         feedOrStore (Nothing, p) x = if null (results p) then (Nothing, feed x p) else (Just (x :), p)
         feedOrStore (Just store, p) x = (Just (store . (x :)), p)

feedLongestPrefix :: (Foldable f, Monoid r) => f s -> Parser s r -> (Parser s r, [s])
feedLongestPrefix s p = case feedEof $ feedAll s $ duplicate p
                        of Failure -> (Failure, toList s)
                           Result t r -> (r, t [])

feedListPrefix :: [s] -> [s] -> Parser s r -> (Parser s r, [s])
feedListPrefix whole chunk p = feedRest chunk p
   where feedRest rest (Result t r) = (Result id r, t rest)
         feedRest _ Failure = (Failure, whole)
         feedRest [] p = (p, [])
         feedRest (x:xs) p = feedRest xs (feed x p)

instance Functor (Parser s) where
   fmap f Failure = Failure
   fmap f (Result t r) = Result t (f r)
   fmap f p@ResultPart{} = resolve (fmap f) p
   fmap f (Choice p1 p2) = Choice (fmap f p1) (fmap f p2)
   fmap f (CommitedLeftChoice p1 p2) = CommitedLeftChoice (fmap f p1) (fmap f p2)
   fmap f (More g) = More (fmap f . g)
   fmap f (LookAhead t p) = LookAhead t (fmap f p)
   fmap f (LookAheadNot t r p) = LookAheadNot t (f r) (fmap f p)

instance Applicative (Parser s) where
   pure = Result id
   Failure <*> _ = Failure
   Result t f <*> p = fmap f (feedAll (t []) p)
   Choice p1a p1b <*> p2 = (p1a <*> p2) <|> (p1b <*> p2)
   More f <*> p = More (\x-> f x <*> p)
   p1 <*> p2 = resolve (<*> p2) p1

instance Alternative (Parser s) where
   -- | A parser that succeeds without consuming any input.
   empty = Failure
   
   Failure <|> p = p
   p <|> Failure = p
   More f <|> More g = More (\x-> f x <|> g x)
   p1@Result{} <|> p2 = Choice p1 p2
   p1 <|> p2@Result{} = Choice p2 p1
   Choice p1a@Result{} p1b <|> p2 = Choice p1a (Choice p1b p2)
   p1 <|> Choice p2a@Result{} p2b = Choice p2a (Choice p1 p2b)
   p1 <|> p2 = Choice p1 p2

instance Monad (Parser s) where
   return = Result id

   Failure >>= _ = Failure
   Result t r >>= f = feedAll (t []) (f r)
   Choice p1 p2 >>= f = (p1 >>= f) <|> (p2 >>= f)
   More f >>= g = More (\x-> f x >>= g)
   p >>= f = resolve (>>= f) p

   Failure >> _ = Failure
   Result t _ >> p = feedAll (t []) p
   ResultPart r p1 >> p2 = p1 >> p2
   Choice p1a p1b >> p2 = (p1a >> p2) <|> (p1b >> p2)
   More f >> p = More (\x-> f x >> p)
   (LookAhead t p1) >> p2 = (feedEof p1 >> p2) <|> More (\x-> lookAheadInto id (feed x p1) >> feedAll (t [x]) p2)
   (LookAheadNot t r p1) >> p2 =
      (feedEof p1 >> p2) <|> More (\x-> lookAheadNotInto id r (feed x p1) >> feedAll (t [x]) p2)
   p1 >> p2 = resolve (>> p2) p1

instance MonadPlus (Parser s) where
   mzero = Failure
   mplus = (<|>)

instance (Monoid r, Show r, Show s) => Show (Parser s r) where
   show Failure = "Failure"
   show (Result t r) = "(Result " ++ shows (t []) (" " ++ shows r ")")
   show (ResultPart f p) = "(ResultPart " ++ shows (f mempty) (" " ++ shows p ")")
   show (Choice p1 p2) = "(Choice " ++ shows p1 (" " ++ shows p2 ")")
   show (CommitedLeftChoice p1 p2) = "(CommitedLeftChoice " ++ shows p1 (" " ++ shows p2 ")")
   show (More f) = "More"
   show (LookAhead t p) = "(LookAhead " ++ shows (t []) (" " ++ shows p ")")
   show (LookAheadNot t r p) = "(LookAheadNot " ++ shows (t []) (" " ++ shows r (" " ++ shows p ")"))

instance Monoid r => Monoid (Parser s r) where
   mempty = return mempty
   mappend = (><)

resolve :: (Parser s a -> Parser s b) -> Parser s a -> Parser s b
resolve f p@CommitedLeftChoice{} = CommitedLeftChoice (More (\x-> f (feed x p))) (feedEof $ f $ feedEof p)
resolve f p = f (feedEof p) <|> More (\x-> f (feed x p))

results :: Parser s r -> [(r, [s] -> [s])]
results (Result t r) = [(r, t)]
results (ResultPart f p) = map (\(r, t)-> (f r, t)) (results p)
results (Choice p1@Result{} p2) = results p1 ++ results p2
results _ = []

hasResult :: Parser s r -> Bool
hasResult (Result _ r) = True
hasResult (ResultPart _ p) = hasResult p
hasResult (Choice p1@Result{} _) = True
hasResult (CommitedLeftChoice _ p) = hasResult p
hasResult _ = False

resultPrefix :: Monoid r => Parser s r -> (Maybe r, Parser s r)
resultPrefix (Result t r) = (Just r, Result t mempty)
resultPrefix (ResultPart f p) = (Just (f $ fromMaybe mempty r), p')
   where (r, p') = resultPrefix p
resultPrefix p = (Nothing, p)

partialResults :: Monoid r => Parser s r -> [(r, Parser s r)]
partialResults p = collect p [(mempty, p)]
   where collect (ResultPart f p) rest = [(f r, p') | (r, p') <- partialResults p] ++ rest
         collect (Choice p1 p2) rest = collect p1 (collect p2 rest)
         collect (CommitedLeftChoice p1 p2) rest = case collect p1 [] of [] -> collect p2 rest
                                                                         r -> r ++ rest
         collect p rest = rest

(<<|>) :: Parser s r -> Parser s r -> Parser s r
Failure <<|> p = p
p <<|> Failure = p
p <<|> _ | hasResult p = p
CommitedLeftChoice p1a p1b <<|> p2 = CommitedLeftChoice p1a (p1b <<|> p2)
ResultPart f (CommitedLeftChoice p1a p1b) <<|> p2 = CommitedLeftChoice (resultPart f p1a) (resultPart f p1b <<|> p2)
More f <<|> More g = More (\x-> f x <<|> g x)
p1 <<|> p2 = CommitedLeftChoice p1 p2

lookAhead :: Parser s r -> Parser s r
lookAhead = lookAheadInto id

lookAheadNot :: r -> Parser s r -> Parser s r
lookAheadNot = lookAheadNotInto id

lookAheadInto :: InputTail s -> Parser s r -> Parser s r
lookAheadInto _ Failure = Failure
lookAheadInto t (Result _ r) = Result t r
lookAheadInto t (ResultPart r p) = resultPart r (lookAheadInto t p)
lookAheadInto t (LookAhead _ p) = LookAhead t p
lookAheadInto t (LookAheadNot _ r p) = LookAheadNot t r p
lookAheadInto t (Choice p1 p2) = lookAheadInto t p1 <|> lookAheadInto t p2
lookAheadInto t p = LookAhead t p

lookAheadNotInto :: InputTail s -> r -> Parser s r' -> Parser s r
lookAheadNotInto t r Failure = Result t r
lookAheadNotInto _ _ Result{} = Failure
lookAheadNotInto t r (ResultPart _ p) = lookAheadNotInto t r p
lookAheadNotInto t r (LookAhead _ p) = lookAheadNotInto t r p
lookAheadNotInto t r (LookAheadNot _ _ p) = lookAheadInto t (fmap (const r) p)
lookAheadNotInto t r p = LookAheadNot t r (fmap (const r) p)

resultPart :: (r -> r) -> Parser s r -> Parser s r
resultPart _ Failure = Failure
resultPart f (Result t r) = Result t (f r)
resultPart f (ResultPart g p) = ResultPart (f . g) p
resultPart f p = ResultPart f p

(><) :: Monoid r => Parser s r -> Parser s r -> Parser s r
Failure >< _ = Failure
Result t r >< p = resultPart (mappend r) (feedAll (t []) p)
ResultPart r p1 >< p2 = resultPart r (p1 >< p2)
Choice p1a p1b >< p2 = (p1a >< p2) <|> (p1b >< p2)
More f >< p = More (\x-> f x >< p)
(LookAhead t p1) >< p2 = (feedEof p1 >< p2) <|> More (\x-> lookAheadInto id (feed x p1) >< feedAll (t [x]) p2)
(LookAheadNot t r p1) >< p2 = 
   (feedEof p1 >< p2) <|> More (\x-> lookAheadNotInto id r (feed x p1) >< feedAll (t [x]) p2)
p1 >< p2 = resolve (>< p2) p1

(>><) :: Monoid r => Parser s r -> Parser s r -> Parser s r
Failure >>< _ = Failure
Result t r >>< p = resultPart (mappend r) (feedAll (t []) p)
ResultPart r p1 >>< p2 = resultPart r (p1 >>< p2)
Choice p1a p1b >>< p2 = (p1a >>< p2) <|> (p1b >>< p2)
p1@CommitedLeftChoice{} >>< p2 = 
   CommitedLeftChoice
      (More (\x-> (feed x p1 >>< p2) <<|> (feedEof p1 >>< feed x p2))) 
      (feedEof p1 >>< feedEof p2)
More f >>< p = More (\x-> f x >>< feed x p)
(LookAhead t p1) >>< p2 = (feedEof p1 >>< p2) <|> More (\x-> lookAheadInto id (feed x p1) >>< feedAll (t [x]) p2)
(LookAheadNot t r p1) >>< p2 = 
   (feedEof p1 >>< p2) <|> More (\x-> lookAheadNotInto id r (feed x p1) >>< feedAll (t [x]) p2)

longest :: Parser s r -> Parser s r
longest Failure = Failure
longest p@Result{} = p
longest (ResultPart r p) = resultPart r (longest p)
longest (More f) = More (longest . f)
longest (Choice p1 p2@LookAhead{}) = p1 <<|> p2
longest (Choice p1@LookAhead{} p2) = p2 <<|> p1
longest (Choice p1 p2@Result{}) = p1 <<|> p2
longest (Choice p1@Result{} p2) = p2 <<|> p1
longest p = More (\x-> longest $ feed x p) <<|> longest (feedEof p)

duplicate :: Parser s r -> Parser s (Parser s r)
duplicate Failure = Failure
duplicate p@Result{} = Result id p
duplicate p = CommitedLeftChoice (More $ \x-> duplicate (feed x p)) (return p)

-- | A parser that fails on any input.
eof :: Monoid r => Parser s r
eof = lookAheadNotInto id mempty anyToken

-- | A parser that accepts a single input item.
anyToken :: Parser s s
anyToken = More return

-- | A parser that accepts a given number of input items.
count :: Int -> Parser s [s]
count n | n > 0 = More (\x-> resultPart (x:) $ count (pred n))
        | otherwise = return []

string :: Eq s => [s] -> Parser s [s]
string whole = stringRest whole
   where stringRest [] = return whole
         stringRest (x : rest) = More (\y-> if x == y then stringRest rest else Failure)

-- | A parser that accepts the longest prefix of input that matches a prefix of the argument list.
prefixOf :: Eq x => [x] -> Parser x [x]
prefixOf list = whilePrefixOf (map (==) list)

-- | A parser that accepts a prefix of input as long as each item satisfies the predicate at the same position in the
-- argument list. The length of the predicate list thus determines the maximum number of acepted values.
whilePrefixOf :: [x -> Bool] -> Parser x [x]
whilePrefixOf (p : rest) = 
   CommitedLeftChoice (More $ \x-> if p x then resultPart (x:) (whilePrefixOf rest) else Failure) (return [])
whilePrefixOf [] = return []

-- | A parser that accepts all input as long as it matches the given predicate.
while :: (x -> Bool) -> Parser x [x]
while p = t
   where t = CommitedLeftChoice (More (\x-> if p x then resultPart (x:) t else Failure)) (return [])

optional :: Monoid r => Parser s r -> Parser s r
optional p = Choice p (return mempty)

optionMaybe :: Parser s r -> Parser s (Maybe r)
optionMaybe p = fmap Just p <<|> return Nothing

skip :: Monoid r => Parser s r' -> Parser s r
skip p = fmap (const mempty) p

many0 :: Monoid r => Parser s r -> Parser s r
many0 p = optional (many1 p)

many1 :: Monoid r => Parser s r -> Parser s r
many1 p = p >>< many0 p

manyTill :: Monoid r => Parser s r -> Parser s r' -> Parser s r
manyTill next end = t
   where t = skip end <<|> (next >>< t)

-- | A parser that accepts all input.
acceptAll :: Parser s [s]
acceptAll = CommitedLeftChoice (More $ \x-> resultPart (x:) acceptAll) (return [])

-- | Parallel parser conjunction: the result of the combinator keeps accepting input as long as both arguments do.
and :: (Monoid r1, Monoid r2) => Parser s r1 -> Parser s r2 -> Parser s (r1, r2)
Failure `and` _ = Failure
_ `and` Failure = Failure
p `and` Result _ r = fmap (\x-> (x, r)) (feedEof p)
Result _ r `and` p = fmap (\x-> (r, x)) (feedEof p)
ResultPart f p1 `and` p2 = fmap (\(r1, r2)-> (f r1, r2)) (p1 `and` p2)
p1 `and` ResultPart f p2 = fmap (\(r1, r2)-> (r1, f r2)) (p1 `and` p2)
Choice p1a p1b `and` p2 = (p1a `and` p2) <|> (p1b `and` p2)
p1 `and` Choice p2a p2b = (p1 `and` p2a) <|> (p1 `and` p2b)
More f `and` p = More (\x-> f x `and` feed x p)
p `and` More f = More (\x-> feed x p `and` f x)
p1 `and` p2 = (feedEof p1 `and` feedEof p2) <|> More (\x-> feed x p1 `and` feed x p2)

andThen :: (Monoid r1, Monoid r2) => Parser s r1 -> Parser s r2 -> Parser s (r1, r2)
Failure `andThen` _ = Failure
Result t r `andThen` p = resultPart (mappend (r, mempty)) (feedAll (t []) (fmap ((,) mempty) p))
ResultPart f p1 `andThen` p2 = resultPart (\(r1, r2)-> (f r1, r2)) (p1 `andThen` p2)
Choice p1a p1b `andThen` p2 = (p1a `andThen` p2) <|> (p1b `andThen` p2)
More f `andThen` p = More (\x-> f x `andThen` p)
(LookAhead t p1) `andThen` p2 =
   (feedEof p1 `andThen` p2) <|> More (\x-> lookAheadInto id (feed x p1) `andThen` feedAll (t [x]) p2)
(LookAheadNot t r p1) `andThen` p2 =
   (feedEof p1 `andThen` p2) <|> More (\x-> lookAheadNotInto id r (feed x p1) `andThen` feedAll (t [x]) p2)
p1 `andThen` p2 = resolve (`andThen` p2) p1
