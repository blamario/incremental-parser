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

-- | This module defines incremental parsers. 
-- 
-- The exported 'Parser' type can provide partial parsing results from partial input, as long as the output is a
-- 'Monoid'. Construct a parser using the primitives and combinators, supply it with input using functions 'feed' and
-- 'feedEof', and extract the parsed output using 'results'.
-- 
-- Implementation is based on Brzozowski derivatives.

{-# LANGUAGE ScopedTypeVariables, Rank2Types, ExistentialQuantification #-}

module Text.ParserCombinators.Incremental (
   -- * The Parser type
   Parser,
   -- * Using a Parser
   feed, feedEof, results, completeResults, resultPrefix,
   -- * Parser primitives
   eof, anyToken, token, satisfy, acceptAll, string, takeWhile, takeWhile1,
   -- * Parser combinators
   count, skip, option, many0, many1, manyTill,
   mapIncremental, (><), (<<|>), lookAhead, notFollowedBy, and, andThen,
   -- * Utilities
   showWith
   )
where

import Prelude hiding (and, foldl, takeWhile)
import Control.Applicative (Applicative (pure, (<*>), (*>), (<*)), Alternative (empty, (<|>), some, many), 
                            optional, liftA2)
import Control.Monad (Functor (fmap), Monad (return, (>>=), (>>)), MonadPlus (mzero, mplus), liftM2)
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid, mempty, mappend)
import Data.Monoid.Cancellative (LeftCancellativeMonoid (mstripPrefix))
import Data.Monoid.Factorial (FactorialMonoid (splitPrimePrefix, mfoldr), mspan)
import Data.Monoid.Null (MonoidNull(mnull))
import Data.Foldable (Foldable, foldl, toList)

-- | The central parser type. Its first parameter is the input monoid, the second the output.
data Parser s r = Failure
                | Result s r
                | ResultPart (r -> r) (Parser s r)
                | Choice (Parser s r) (Parser s r)
                | CommitedLeftChoice (Parser s r) (Parser s r)
                | More (s -> Parser s r)
                | forall r'. Apply (Parser s r' -> Parser s r) (Parser s r')
                | forall r'. ApplyInput (s -> Parser s r' -> Parser s r) (Parser s r')

-- | Feeds a chunk of the input to the parser.
feed :: Monoid s => s -> Parser s r -> Parser s r
feed _ Failure = Failure
feed s (Result t r) = Result (mappend t s) r
feed s (ResultPart r p) = resultPart r (feed s p)
feed s (Choice p1 p2) = feed s p1 <|> feed s p2
feed s (CommitedLeftChoice p1 p2) = feed s p1 <<|> feed s p2
feed s p@(More f) = f s
feed s (Apply f p) = f (feed s p)
feed s (ApplyInput f p) = f s (feed s p)

-- | Signals the end of the input.
feedEof :: Monoid s => Parser s r -> Parser s r
feedEof Failure = Failure
feedEof p@Result{} = p
feedEof (ResultPart r p) = prepend r (feedEof p)
   where prepend r (Result t r') = Result t (r r')
         prepend r (Choice p1 p2) = prepend r p1 <|> prepend r p2
         prepend r Failure = Failure
feedEof (Choice p1 p2) = feedEof p1 <|> feedEof p2
feedEof (CommitedLeftChoice p1 p2) = feedEof p1 <<|> feedEof p2
feedEof More{} = Failure
feedEof (Apply f p) = feedEof (f $ feedEof p)
feedEof (ApplyInput f p) = feedEof (f mempty $ feedEof p)

-- | Extracts all available parsing results. The first component of the result pair is a list of complete results
-- together with the unconsumed remainder of the input. If the parsing can continue further, the second component of the
-- pair provides the partial result prefix together with the parser for the rest of the input.
results :: Monoid r => Parser s r -> ([(r, s)], Maybe (r, Parser s r))
results Failure = ([], Nothing)
results (Result t r) = ([(r, t)], Nothing)
results (ResultPart f p) = (map prepend results', fmap prepend rest)
   where (results', rest) = results p
         prepend (x, y) = (f x, y)
results (Choice p1@Result{} p2) = (results1 ++ results2, combine rest1 rest2)
   where (results1, rest1) = results p1
         (results2, rest2) = results p2
         combine Nothing rest2 = rest2
         combine rest1 Nothing = rest1
         combine (Just (r1, p1)) (Just (r2, p2)) = 
            Just (mempty, Choice (ResultPart (mappend r1) p1) (ResultPart (mappend r2) p2))
results p = ([], Just (mempty, p))

-- | Like 'results', but returns only the complete results with the corresponding unconsumed inputs.
completeResults :: Parser s r -> [(r, s)]
completeResults (Result t r) = [(r, t)]
completeResults (ResultPart f p) = map (\(r, t)-> (f r, t)) (completeResults p)
completeResults (Choice p1@Result{} p2) = completeResults p1 ++ completeResults p2
completeResults _ = []

-- | Determines if there are any complete results available.
hasResult :: Parser s r -> Bool
hasResult Result{} = True
hasResult (ResultPart _ p) = hasResult p
hasResult (Choice Result{} _) = True
hasResult (CommitedLeftChoice _ p) = hasResult p
hasResult _ = False

-- | Like 'results', but returns only the partial result prefix.
resultPrefix :: Monoid r => Parser s r -> (r, Parser s r)
resultPrefix (Result t r) = (r, Result t mempty)
resultPrefix (ResultPart f p) = (f r, p')
   where (r, p') = resultPrefix p
resultPrefix p = (mempty, p)

-- | Behaves like the argument parser, but without consuming any input.
lookAhead :: Monoid s => Parser s r -> Parser s r
lookAhead p = lookAheadInto mempty p

-- | Does not consume any input; succeeds (with 'mempty' result) iff the argument parser fails.
notFollowedBy :: (Monoid s, Monoid r) => Parser s r' -> Parser s r
notFollowedBy = lookAheadNotInto mempty

lookAheadInto :: Monoid s => s -> Parser s r -> Parser s r
lookAheadInto t Failure               = Failure
lookAheadInto t (Result _ r)          = Result t r
lookAheadInto t (ResultPart r p)      = resultPart r (lookAheadInto t p)
lookAheadInto t (More f)              = More (\s-> lookAheadInto (mappend t s) (f s))
lookAheadInto t (Choice p1 p2)        = lookAheadInto t p1 <|> lookAheadInto t p2
lookAheadInto t p                     = ApplyInput (\t' p'-> lookAheadInto (mappend t t') p') p

lookAheadNotInto :: (Monoid s, Monoid r) => s -> Parser s r' -> Parser s r
lookAheadNotInto t Failure               = Result t mempty
lookAheadNotInto t (Result _ r)          = Failure
lookAheadNotInto t (Choice (Result _ r) _) = Failure
lookAheadNotInto t (ResultPart r p)      = lookAheadNotInto t p
lookAheadNotInto t p                     = ApplyInput (\t' p'-> lookAheadNotInto (mappend t t') p') p

-- | Provides a partial parsing result.
resultPart :: (r -> r) -> Parser s r -> Parser s r
resultPart _ Failure = Failure
resultPart f (Result t r) = Result t (f r)
resultPart f (Choice (Result t r) p) = Choice (Result t (f r)) (resultPart f p)
resultPart f (ResultPart g p) = ResultPart (f . g) p
resultPart f p = ResultPart f p

-- | Usage of 'fmap' destroys the incrementality of parsing results, if you need it use 'mapIncremental' instead.
instance Monoid s => Functor (Parser s) where
   fmap f Failure = Failure
   fmap f (Result t r) = Result t (f r)
   fmap f (Choice p1 p2) = fmap f p1 <|> fmap f p2
   fmap f (CommitedLeftChoice p1 p2) = fmap f p1 <<|> fmap f p2
   fmap f (More g) = More (fmap f . g)
   fmap f p = Apply (fmap f) p

-- | The '<*>' combinator requires its both arguments to provide complete parsing results, takeWhile '*>' and '<*' preserve
-- the incremental results.
instance Monoid s => Applicative (Parser s) where
   pure = Result mempty
   Failure <*> _ = Failure
   Result t f <*> p = fmap f (feed t p)
   Choice p1a p1b <*> p2 = (p1a <*> p2) <|> (p1b <*> p2)
   More f <*> p = More (\x-> f x <*> p)
   p1 <*> p2 = Apply (<*> p2) p1

   (*>) = (>>)

   Failure <* _ = Failure
   Result t r <* p = feed t p *> pure r
   ResultPart r p1 <* p2 = ResultPart r (p1 <* p2)
   Choice p1a p1b <* p2 = (p1a <* p2) <|> (p1b <* p2)
   More f <* p = More (\x-> f x <* p)
   p1 <* p2 = Apply (<* p2) p1

-- | The '<|>' choice combinator is symmetric.
instance Monoid s => Alternative (Parser s) where
   empty = Failure
   
   Failure <|> p = p
   p <|> Failure = p
   More f <|> More g = More (\x-> f x <|> g x)
   p1@Result{} <|> p2 = Choice p1 p2
   Choice p1a@Result{} p1b <|> p2 = Choice p1a (p1b <|> p2)
   p1 <|> p2@Result{} = Choice p2 p1
   p1 <|> Choice p2a@Result{} p2b = Choice p2a (p1 <|> p2b)
   p1 <|> p2 = Choice p1 p2

-- | Usage of '>>=' destroys the incrementality of its left argument's parsing results, but '>>' is safe to use.
instance Monoid s => Monad (Parser s) where
   return = Result mempty

   Failure >>= _ = Failure
   Result t r >>= f = feed t (f r)
   Choice p1 p2 >>= f = (p1 >>= f) <|> (p2 >>= f)
   More f >>= g = More (\x-> f x >>= g)
   p >>= f = Apply (>>= f) p

   Failure >> _ = Failure
   Result t _ >> p = feed t p
   ResultPart r p1 >> p2 = p1 >> p2
   Choice p1a p1b >> p2 = (p1a >> p2) <|> (p1b >> p2)
   More f >> p = More (\x-> f x >> p)
   p1 >> p2 = Apply (>> p2) p1

-- | The 'MonadPlus' and the 'Alternative' instance differ: the former's 'mplus' combinator equals the asymmetric '<<|>'
-- choice.
instance Monoid s => MonadPlus (Parser s) where
   mzero = Failure
   mplus = (<<|>)

-- | Two parsers can be sequentially joined.
instance (Monoid s, Monoid r) => Monoid (Parser s r) where
   mempty = return mempty
   mappend = (><)

-- instance (Monoid s, Monoid r, Show s, Show r) => Show (Parser s r) where
--    show = showWith (show . ($ mempty)) show

showWith :: (Monoid s, Monoid r, Show s) => ((s -> Parser s r) -> String) -> (r -> String) -> Parser s r -> String
showWith sm sr Failure = "Failure"
showWith sm sr (Result t r) = "(Result (" ++ shows t ("++) " ++ sr r ++ ")")
showWith sm sr (ResultPart f p) = "(ResultPart (mappend " ++ sr (f mempty) ++ ") " ++ showWith sm sr p ++ ")"
showWith sm sr (Choice p1 p2) = "(Choice " ++ showWith sm sr p1 ++ " " ++ showWith sm sr p2 ++ ")"
showWith sm sr (CommitedLeftChoice p1 p2) = 
   "(CommitedLeftChoice " ++ showWith sm sr p1 ++ " " ++ showWith sm sr p2 ++ ")"
showWith sm sr (More f) = "(More $ " ++ sm f ++ ")"
showWith sm sr (Apply f p) = "Apply"
showWith sm sr (ApplyInput f p) = "ApplyInput"

-- | Like 'fmap', but capable of mapping partial results, being restricted to 'Monoid' types only.
mapIncremental :: (Monoid s, Monoid a, Monoid b) => (a -> b) -> Parser s a -> Parser s b
mapIncremental f Failure = Failure
mapIncremental f (Result t r) = Result t (f r)
mapIncremental f (ResultPart r p) = ResultPart (f (r mempty) `mappend`) (mapIncremental f p)
mapIncremental f (Choice p1 p2) = mapIncremental f p1 <|> mapIncremental f p2
mapIncremental f (CommitedLeftChoice p1 p2) = mapIncremental f p1 <<|> mapIncremental f p2
mapIncremental f (More g) = More (mapIncremental f . g)
mapIncremental f p = Apply (mapIncremental f) p

-- | Left-weighted choice. The right parser is used only if the left one utterly fails.
infixl 3 <<|>
(<<|>) :: Parser s r -> Parser s r -> Parser s r
Failure <<|> p = p
p <<|> Failure = p
p <<|> _ | hasResult p = p
More f <<|> More g = More (\x-> f x <<|> g x)
p1 <<|> p2 = CommitedLeftChoice p1 p2

-- | Join operator on parsers of same type, preserving the incremental results.
infixl 5 ><
(><) :: (Monoid s, Monoid r) => Parser s r -> Parser s r -> Parser s r
Failure >< _ = Failure
Result t r >< p = resultPart (mappend r) (feed t p)
ResultPart r p1 >< p2 = resultPart r (p1 >< p2)
Choice p1a p1b >< p2 = (p1a >< p2) <|> (p1b >< p2)
More f >< p = More (\x-> f x >< p)
p1 >< p2 = Apply (>< p2) p1

-- | A parser that fails on any input and succeeds at its end.
eof :: (MonoidNull s, Monoid r) => Parser s r
eof = notFollowedBy nonEmptyInput
   where nonEmptyInput = More $ \s-> if mnull s then nonEmptyInput else return s

-- | A parser that accepts any single input atom.
anyToken :: FactorialMonoid s => Parser s s
anyToken = More f
   where f s = case splitPrimePrefix s
               of Just (first, rest) -> Result rest first
                  Nothing -> anyToken

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s) => s -> Parser s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: FactorialMonoid s => (s -> Bool) -> Parser s s
satisfy pred = p
   where p = More f
         f s = case splitPrimePrefix s
               of Just (first, rest) -> if pred first then Result rest first else Failure
                  Nothing -> p

-- | A parser that consumes and returns the given prefix of the input.
string :: (LeftCancellativeMonoid s, MonoidNull s) => s -> Parser s s
string x | mnull x = mempty
string x = More (\y-> case (mstripPrefix x y, mstripPrefix y x)
                      of (Just y', _) -> Result y' x
                         (Nothing, Nothing) -> Failure
                         (Nothing, Just x') -> string x' >> return x)

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'many0 . satisfy'.
takeWhile :: (FactorialMonoid s, MonoidNull s) => (s -> Bool) -> Parser s s
takeWhile p = CommitedLeftChoice (takeWhile1 p) mempty

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'many1 . satisfy'.
takeWhile1 :: (FactorialMonoid s, MonoidNull s) => (s -> Bool) -> Parser s s
takeWhile1 p = w
   where w = More f
         f s | mnull s = w
         f s = let (prefix, suffix) = mspan p s 
               in if mnull prefix then Failure
                  else if mnull suffix then resultPart (mappend prefix) (takeWhile p)
                       else Result suffix prefix

-- | Accepts the given number of occurrences of the argument parser.
count :: (Monoid s, Monoid r) => Int -> Parser s r -> Parser s r
count n p | n > 0 = p >< count (pred n) p
          | otherwise = mempty

-- | Like 'optional', but restricted to 'Monoid' results.
option :: (Monoid s, Monoid r) => Parser s r -> Parser s r
option p = p <|> return mempty

-- | Discards the results of the argument parser.
skip :: (Monoid s, Monoid r) => Parser s r' -> Parser s r
skip p = p >> mempty

-- | Zero or more argument occurrences like 'many', but matches the longest possible input sequence.
many0 :: (Monoid s, Monoid r) => Parser s r -> Parser s r
many0 p = many1 p <<|> return mempty

-- | One or more argument occurrences like 'some', but matches the longest possible input sequence.
many1 :: (Monoid s, Monoid r) => Parser s r -> Parser s r
many1 p = More (\s-> feed s (p >< many0 p))

-- | Repeats matching the first argument until the second one succeeds.
manyTill :: (Monoid s, Monoid r) => Parser s r -> Parser s r' -> Parser s r
manyTill next end = t
   where t = skip end <<|> (next >< t)

-- | A parser that accepts all input.
acceptAll :: Monoid s => Parser s s
acceptAll = CommitedLeftChoice (More $ \s-> resultPart (mappend s) acceptAll) (return mempty)

-- | Parallel parser conjunction: the combined parser keeps accepting input as long as both arguments do.
and :: (Monoid s, Monoid r1, Monoid r2) => Parser s r1 -> Parser s r2 -> Parser s (r1, r2)
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

-- | Parser sequence that preserves incremental results, otherwise equivalent to 'liftA2' (,)
andThen :: (Monoid s, Monoid r1, Monoid r2) => Parser s r1 -> Parser s r2 -> Parser s (r1, r2)
Failure `andThen` _ = Failure
Result t r `andThen` p = resultPart (mappend (r, mempty)) (feed t (fmap ((,) mempty) p))
ResultPart f p1 `andThen` p2 = resultPart (\(r1, r2)-> (f r1, r2)) (p1 `andThen` p2)
Choice p1a p1b `andThen` p2 = (p1a `andThen` p2) <|> (p1b `andThen` p2)
More f `andThen` p = More (\x-> f x `andThen` p)
p1 `andThen` p2 = Apply (`andThen` p2) p1
