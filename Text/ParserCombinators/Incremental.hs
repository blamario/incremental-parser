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

{-# LANGUAGE FlexibleContexts #-}

module Text.ParserCombinators.Incremental (
   -- * The Parser type
   Parser,
   -- * Using a Parser
   feed, feedEof, results, completeResults, resultPrefix,
   -- * Parser primitives
   failure, more, eof, anyToken, token, satisfy, acceptAll, string, takeWhile, takeWhile1,
   -- * Parser combinators
   count, skip, option, many0, many1, manyTill,
   mapType, mapIncremental, (<||>), (<<|>), (><), lookAhead, notFollowedBy, and, andThen,
   -- * Utilities
   showWith
   )
where

import Prelude hiding (and, foldl, takeWhile)
import Control.Applicative (Applicative (pure, (<*>), (*>), (<*)), Alternative (empty, (<|>), some, many), 
                            optional, liftA2)
import Control.Monad (Functor (fmap), Monad (return, (>>=), (>>)), MonadPlus (mzero, mplus), ap, liftM2)
import Data.Monoid (Monoid, mempty, mappend)
import Data.Monoid.Cancellative (LeftCancellativeMonoid (mstripPrefix))
import Data.Monoid.Factorial (FactorialMonoid (splitPrimePrefix, mfoldr), mspan)
import Data.Monoid.Null (MonoidNull(mnull))
import Data.Foldable (Foldable, foldl, toList)

-- | The central parser type. Its first parameter is the input monoid, the second the output.
data Parser a s r = Failure
                  | Result s r
                  | ResultPart (r -> r) (Parser a s r)
                  | Choice (Parser a s r) (Parser a s r)
                  | Delay (Parser a s r) (s -> Parser a s r)

-- | Feeds a chunk of the input to the parser.
feed :: Monoid s => s -> Parser a s r -> Parser a s r
feed _ Failure = Failure
feed s (Result t r) = Result (mappend t s) r
feed s (ResultPart r p) = resultPart r (feed s p)
feed s (Choice p1 p2) = feed s p1 <||> feed s p2
feed s (Delay e f) = f s

-- | Signals the end of the input.
feedEof :: Monoid s => Parser a s r -> Parser a s r
feedEof Failure = Failure
feedEof p@Result{} = p
feedEof (ResultPart r p) = prepend r (feedEof p)
feedEof (Choice p1 p2) = feedEof p1 <||> feedEof p2
feedEof (Delay e f) = e

-- | Extracts all available parsing results. The first component of the result pair is a list of complete results
-- together with the unconsumed remainder of the input. If the parsing can continue further, the second component of the
-- pair provides the partial result prefix together with the parser for the rest of the input.
results :: Monoid r => Parser a s r -> ([(r, s)], Maybe (r, Parser a s r))
results Failure = ([], Nothing)
results (Result t r) = ([(r, t)], Nothing)
results (ResultPart f p) = (map prepend results', fmap (fmap infallible . prepend) rest)
   where (results', rest) = results p
         prepend (x, y) = (f x, y)
results (Choice p1 p2) | isInfallible p1 = (results1 ++ results2, combine rest1 rest2)
   where (results1, rest1) = results p1
         (results2, rest2) = results p2
         combine Nothing rest2 = rest2
         combine rest1 Nothing = rest1
         combine (Just (r1, p1)) (Just (r2, p2)) = 
            Just (mempty, Choice (resultPart (mappend r1) p1) (resultPart (mappend r2) p2))
results p = ([], Just (mempty, p))

-- | Like 'results', but returns only the complete results with the corresponding unconsumed inputs.
completeResults :: Parser a s r -> [(r, s)]
completeResults (Result t r) = [(r, t)]
completeResults (ResultPart f p) = map (\(r, t)-> (f r, t)) (completeResults p)
completeResults (Choice p1 p2) | isInfallible p1 = completeResults p1 ++ completeResults p2
completeResults _ = []

-- | Like 'results', but returns only the partial result prefix.
resultPrefix :: Monoid r => Parser a s r -> (r, Parser a s r)
resultPrefix (Result t r) = (r, Result t mempty)
resultPrefix (ResultPart f p) = (f mempty, infallible p)
resultPrefix p = (mempty, p)

failure :: Parser a s r
failure = Failure

-- | Usage of 'fmap' destroys the incrementality of parsing results, if you need it use 'mapIncremental' instead.
instance Monoid s => Functor (Parser a s) where
   fmap f (Result t r) = Result t (f r)
   fmap f (ResultPart r p) = fmap f (prepend r p)
   fmap f p = apply (fmap f) p

-- | The '<*>' combinator requires its both arguments to provide complete parsing results, takeWhile '*>' and '<*'
-- preserve the incremental results.
instance Monoid s => Applicative (Parser a s) where
   pure = Result mempty
   (<*>) = ap
   (*>) = (>>)

   Result t r <* p = feed t p *> pure r
   ResultPart r p1 <* p2@ResultPart{} = resultPart r (p1 <* p2)
   p1 <* p2 = apply (<* p2) p1

-- | Usage of '>>=' destroys the incrementality of its left argument's parsing results, but '>>' is safe to use.
instance Monoid s => Monad (Parser a s) where
   return = Result mempty

   Result t r >>= f = feed t (f r)
   ResultPart r p >>= f = prepend r p >>= f
   p >>= f = apply (>>= f) p

   Result t _ >> p = feed t p
   ResultPart _ p1 >> p2 = p1 >> p2
   p1 >> p2 = apply (>> p2) p1

infixl 3 <||>
infixl 3 <<|>

(<||>) :: Parser a s r -> Parser a s r -> Parser a s r
Failure <||> p = p
p <||> Failure = p
Delay e1 f1 <||> Delay e2 f2 = Delay (e1 <||> e2) (\s-> f1 s <||> f2 s)
p1@Result{} <||> p2 = Choice p1 p2
p1@ResultPart{} <||> p2 = Choice p1 p2
Choice p1a p1b <||> p2 | isInfallible p1a = Choice p1a (p1b <||> p2)
p1 <||> p2@Result{} = Choice p2 p1
p1 <||> p2@ResultPart{} = Choice p2 p1
p1 <||> Choice p2a p2b | isInfallible p2a = Choice p2a (p1 <||> p2b)
p1 <||> p2 = Choice p1 p2

(<<|>) :: Monoid s => Parser a s r -> Parser a s r -> Parser a s r
Failure <<|> p = p
p <<|> _ | isInfallible p = p
p <<|> Failure = p
p1 <<|> p2 = if isInfallible p2 then infallible p' else p'
   where p' = Delay (feedEof p1 <<|> feedEof p2) (\s-> feed s p1 <<|> feed s p2)

-- | Two parsers can be sequentially joined.
instance (Monoid s, Monoid r) => Monoid (Parser a s r) where
   mempty = return mempty
   mappend = (><)

-- instance (Monoid s, Monoid r, Show s, Show r) => Show (Parser a s r) where
--    show = showWith (show . ($ mempty)) show

showWith :: (Monoid s, Monoid r, Show s) => ((s -> Parser a s r) -> String) -> (r -> String) -> Parser a s r -> String
showWith sm sr Failure = "Failure"
showWith sm sr (Result t r) = "(Result " ++ shows t (" " ++ sr r ++ ")")
showWith sm sr (ResultPart f p) =
   "(ResultPart (mappend " ++ sr (f mempty) ++ ") " ++ showWith sm sr p ++ ")"
showWith sm sr (Choice p1 p2) = "(Choice " ++ showWith sm sr p1 ++ " " ++ showWith sm sr p2 ++ ")"
showWith sm sr (Delay e f) = "(Delay " ++ showWith sm sr e ++ " " ++ sm f ++ ")"

-- | Like 'fmap', but capable of mapping partial results, being restricted to 'Monoid' types only.
mapIncremental :: (Monoid s, Monoid a, Monoid b) => (a -> b) -> Parser p s a -> Parser p s b
mapIncremental f (Result t r) = Result t (f r)
mapIncremental f (ResultPart r p) = resultPart (mappend $ f (r mempty)) (mapIncremental f p)
mapIncremental f p = apply (mapIncremental f) p

-- | Behaves like the argument parser, but without consuming any input.
lookAhead :: Monoid s => Parser a s r -> Parser a s r
lookAhead p = lookAheadInto mempty p
   where lookAheadInto :: Monoid s => s -> Parser a s r -> Parser a s r
         lookAheadInto t Failure          = Failure
         lookAheadInto t (Result _ r)     = Result t r
         lookAheadInto t (ResultPart r p) = resultPart r (lookAheadInto t p)
         lookAheadInto t (Choice p1 p2)   = lookAheadInto t p1 <||> lookAheadInto t p2
         lookAheadInto t (Delay e f)      = Delay (lookAheadInto t e) (\s-> lookAheadInto (mappend t s) (f s))

-- | Does not consume any input; succeeds (with 'mempty' result) iff the argument parser fails.
notFollowedBy :: (Monoid s, Monoid r) => Parser a s r' -> Parser a s r
notFollowedBy = lookAheadNotInto mempty
   where lookAheadNotInto :: (Monoid s, Monoid r) => s -> Parser a s r' -> Parser a s r
         lookAheadNotInto t Failure             = Result t mempty
         lookAheadNotInto t Result{}            = Failure
         lookAheadNotInto t ResultPart{}        = Failure
         lookAheadNotInto t (Choice p _) | isInfallible p = Failure
         lookAheadNotInto t (Delay e f) = Delay (lookAheadNotInto t e) (\s-> lookAheadNotInto (mappend t s) (f s))

-- | Provides a partial parsing result.
resultPart :: (r -> r) -> Parser a s r -> Parser a s r
resultPart _ Failure = Failure
resultPart f (Result t r) = Result t (f r)
resultPart f (ResultPart g p) = ResultPart (f . g) p
resultPart f p = ResultPart f p

infallible :: Parser a s r -> Parser a s r
infallible Failure = error "Internal contradiction"
infallible p@ResultPart{} = p
infallible p@Result{} = p
infallible p = resultPart id p

isInfallible :: Parser a s r -> Bool
isInfallible Result{} = True
isInfallible ResultPart{} = True
isInfallible (Choice p _) = isInfallible p
isInfallible _ = False

prepend :: Monoid s => (r -> r) -> Parser a s r -> Parser a s r
prepend _ Failure = Failure
prepend r1 (Result t r2) = Result t (r1 r2)
prepend r1 (ResultPart r2 p) = ResultPart (r1 . r2) p
prepend r (Choice p1 p2) = Choice (prepend r p1) (prepend r p2)
prepend r p = apply (prepend r) p

apply :: Monoid s => (Parser a s r -> Parser a s r') -> Parser a s r -> Parser a s r'
apply f Failure = Failure
apply f (Choice p1 p2) = f p1 <||> f p2
apply g (Delay e f) = Delay (feedEof $ g e) (g . f)

mapType :: (Parser a s r -> Parser b s r) -> Parser a s r -> Parser b s r
mapType _ Failure = Failure
mapType _ (Result s r) = Result s r
mapType f (ResultPart r p) = ResultPart r (f p)
mapType f (Choice p1 p2) = Choice (f p1) (f p2)
mapType g (Delay e f) = Delay (g e) (g . f)

more :: (s -> Parser a s r) -> Parser a s r
more = Delay Failure

-- | Join operator on parsers of same type, preserving the incremental results.
infixl 5 ><
(><) :: (Monoid s, Monoid r) => Parser a s r -> Parser a s r -> Parser a s r
_ >< Failure = Failure
p1 >< p2 | isInfallible p2 = appendIncremental p1 p2
   where appendIncremental :: (Monoid s, Monoid r) => Parser a s r -> Parser a s r -> Parser a s r
         appendIncremental (Result t r) p = resultPart (mappend r) (feed t p)
         appendIncremental (ResultPart r p1) p2 = resultPart r (appendIncremental p1 p2)
         appendIncremental p1 p2 = apply (`appendIncremental` p2) p1
p1 >< p2 = append p1 p2
   where append :: (Monoid s, Monoid r) => Parser a s r -> Parser a s r -> Parser a s r
         append (Result t r) p2 = prepend (mappend r) (feed t p2)
         append (ResultPart r p1) p2 = prepend r (append p1 p2)
         append p1 p2 = apply (`append` p2) p1

-- | A parser that fails on any input and succeeds at its end.
eof :: (MonoidNull s, Monoid r) => Parser a s r
eof = Delay mempty (\s-> if mnull s then eof else Failure)

-- | A parser that accepts any single input atom.
anyToken :: FactorialMonoid s => Parser a s s
anyToken = more f
   where f s = case splitPrimePrefix s
               of Just (first, rest) -> Result rest first
                  Nothing -> anyToken

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s) => s -> Parser a s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: FactorialMonoid s => (s -> Bool) -> Parser a s s
satisfy pred = p
   where p = more f
         f s = case splitPrimePrefix s
               of Just (first, rest) -> if pred first then Result rest first else Failure
                  Nothing -> p

-- | A parser that consumes and returns the given prefix of the input.
string :: (LeftCancellativeMonoid s, MonoidNull s) => s -> Parser a s s
string x | mnull x = mempty
string x = more (\y-> case (mstripPrefix x y, mstripPrefix y x)
                      of (Just y', _) -> Result y' x
                         (Nothing, Nothing) -> Failure
                         (Nothing, Just x') -> string x' >> return x)

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'many0 . satisfy'.
takeWhile :: (FactorialMonoid s, MonoidNull s) => (s -> Bool) -> Parser a s s
takeWhile = fst . takeWhiles

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'many1 . satisfy'.
takeWhile1 :: (FactorialMonoid s, MonoidNull s) => (s -> Bool) -> Parser a s s
takeWhile1 = snd . takeWhiles

takeWhiles :: (FactorialMonoid s, MonoidNull s) => (s -> Bool) -> (Parser a s s, Parser a s s)
takeWhiles p = (takeWhile, takeWhile1)
   where takeWhile = takeWhile1 <<|> return mempty
         takeWhile1 = more f
         f s | mnull s = takeWhile1
         f s = let (prefix, suffix) = mspan p s 
               in if mnull prefix then Failure
                  else if mnull suffix then resultPart (mappend prefix) takeWhile
                       else Result suffix prefix

-- | Accepts the given number of occurrences of the argument parser.
count :: (Monoid s, Monoid r) => Int -> Parser a s r -> Parser a s r
count n p | n > 0 = p >< count (pred n) p
          | otherwise = mempty

-- | Like 'optional', but restricted to 'Monoid' results.
option :: (Alternative (Parser a s), Monoid s, Monoid r) => Parser a s r -> Parser a s r
option p = p <|> mempty

-- | Discards the results of the argument parser.
skip :: (Monoid s, Monoid r) => Parser a s r' -> Parser a s r
skip p = p *> mempty

-- | Zero or more argument occurrences like 'many', but matches the longest possible input sequence.
many0 :: (Alternative (Parser a s), Monoid s, Monoid r) => Parser a s r -> Parser a s r
many0 = fst . manies

-- | One or more argument occurrences like 'some', but matches the longest possible input sequence.
many1 :: (Alternative (Parser a s), Monoid s, Monoid r) => Parser a s r -> Parser a s r
many1 = snd . manies

manies :: (Alternative (Parser a s), Monoid s, Monoid r) => Parser a s r -> (Parser a s r, Parser a s r)
manies p = (many0, many1)
   where many0 = ResultPart id (many1 <|> mempty)
         many1 = mappend p many0

-- | Repeats matching the first argument until the second one succeeds.
manyTill :: (Alternative (Parser a s), Monoid s, Monoid r) => Parser a s r -> Parser a s r' -> Parser a s r
manyTill next end = t
   where t = skip end <|> mappend next t

-- | A parser that accepts all input.
acceptAll :: Monoid s => Parser a s s
acceptAll = Delay mempty (\s-> resultPart (mappend s) acceptAll)

-- | Parallel parser conjunction: the combined parser keeps accepting input as long as both arguments do.
and :: (Monoid s, Monoid r1, Monoid r2) => Parser a s r1 -> Parser a s r2 -> Parser a s (r1, r2)
Failure `and` _ = Failure
_ `and` Failure = Failure
p `and` Result _ r = fmap (\x-> (x, r)) (feedEof p)
Result _ r `and` p = fmap (\x-> (r, x)) (feedEof p)
ResultPart f p1 `and` p2 = fmap (\(r1, r2)-> (f r1, r2)) (p1 `and` p2)
p1 `and` ResultPart f p2 = fmap (\(r1, r2)-> (r1, f r2)) (p1 `and` p2)
Choice p1a p1b `and` p2 = (p1a `and` p2) <||> (p1b `and` p2)
p1 `and` Choice p2a p2b = (p1 `and` p2a) <||> (p1 `and` p2b)
p1 `and` p2 = Delay (feedEof p1 `and` feedEof p2) (\s-> feed s p1 `and` feed s p2)

-- | Parser a sequence that preserves incremental results, otherwise equivalent to 'liftA2' (,)
andThen :: (Monoid s, Monoid r1, Monoid r2) => Parser a s r1 -> Parser a s r2 -> Parser a s (r1, r2)
Result t r `andThen` p = resultPart (mappend (r, mempty)) (feed t (fmap ((,) mempty) p))
ResultPart f p1 `andThen` p2 = resultPart (\(r1, r2)-> (f r1, r2)) (p1 `andThen` p2)
p1 `andThen` p2 = apply (`andThen` p2) p1
