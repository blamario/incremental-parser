{-
    Copyright 2010-2015 Mario Blazevic

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

{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}

module Text.ParserCombinators.Incremental (
   -- * The Parser type
   Parser,
   -- * Using a Parser
   feed, feedEof, inspect, results, completeResults, resultPrefix,
   -- * Parser primitives
   failure, (<?>), more, eof, anyToken, token, satisfy, acceptAll, string, takeWhile, takeWhile1,
   -- ** Character primitives
   satisfyChar, takeCharsWhile, takeCharsWhile1,
   -- * Parser combinators
   count, skip, moptional, concatMany, concatSome, manyTill,
   mapType, mapIncremental, (+<*>), (<||>), (<<|>), (><), lookAhead, notFollowedBy, and, andThen,
   -- * Utilities
   isInfallible, showWith, defaultMany, defaultSome
   )
where

import Prelude hiding (and, null, span, takeWhile)
import Control.Applicative (Applicative (pure, (<*>), (*>), (<*)), Alternative ((<|>)))
import Control.Applicative.Monoid(MonoidApplicative(..), MonoidAlternative(..))
import Control.Monad (ap)
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid, mempty, mappend, (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid (stripPrefix))
import Data.Monoid.Factorial (FactorialMonoid (splitPrimePrefix), span)
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Textual as Textual

-- | The central parser type. Its first parameter is the subtype of the parser, the second is the input monoid type, the
-- third the output type.
data Parser t s r = Failure String
                  | Result s r
                  | ResultPart (r -> r) (Parser t s r) (s -> Parser t s r)
                  | Delay (Parser t s r) (s -> Parser t s r)
                  | Choice (Parser t s r) (Parser t s r)

-- | Feeds a chunk of the input to the parser.
feed :: Monoid s => s -> Parser t s r -> Parser t s r
feed s p@Failure{} = s `seq` p
feed s (Result s' r) = Result (mappend s' s) r
feed s (ResultPart r _ f) = resultPart r (f s)
feed s (Choice p1 p2) = feed s p1 <||> feed s p2
feed s (Delay _ f) = f s

-- | Signals the end of the input.
feedEof :: Monoid s => Parser t s r -> Parser t s r
feedEof p@Failure{} = p
feedEof p@Result{} = p
feedEof (ResultPart r e _) = prepend r (feedEof e)
feedEof (Choice p1 p2) = feedEof p1 <||> feedEof p2
feedEof (Delay e _) = feedEof e

-- | Extracts all available parsing results from a 'Parser'. The first component of the result pair is a list of
-- complete results together with the unconsumed remainder of the input. If the parsing can continue further, the second
-- component of the pair provides the partial result prefix together with the parser for the rest of the input.
results :: Monoid r => Parser t s r -> ([(r, s)], Maybe (r, Parser t s r))
results = fmap (fmap (\(mf, p)-> (fromMaybe id mf mempty, p))) . inspect

-- | Like 'results', but more general: doesn't assume that the result type is a 'Monoid'.
inspect :: Parser t s r -> ([(r, s)], Maybe (Maybe (r -> r), Parser t s r))
inspect Failure{} = ([], Nothing)
inspect (Result s r) = ([(r, s)], Nothing)
inspect (ResultPart r e f) = ([], Just (Just r, ResultPart id e f))
inspect (Choice p1 p2) | isInfallible p1 = (results1 ++ results2, combine rest1 rest2)
   where (results1, rest1) = inspect p1
         (results2, rest2) = inspect p2
         combine Nothing rest = rest
         combine rest Nothing = rest
         combine (Just (r1, p1')) (Just (r2, p2')) = 
            Just (Just id, Choice (prepend (fromMaybe id r1) p1') (prepend (fromMaybe id r2) p2'))
inspect p = ([], Just (Nothing, p))

-- | Like 'results', but returns only the complete results with the corresponding unconsumed inputs.
completeResults :: Parser t s r -> [(r, s)]
completeResults (Result s r) = [(r, s)]
completeResults (ResultPart r e f) = map (\(r', t)-> (r r', t)) (completeResults e)
completeResults (Choice p1 p2) | isInfallible p1 = completeResults p1 ++ completeResults p2
completeResults _ = []

-- | Like 'results', but returns only the partial result prefix.
resultPrefix :: Monoid r => Parser t s r -> (r, Parser t s r)
resultPrefix (Result s r) = (r, Result s mempty)
resultPrefix (ResultPart r e f) = (r mempty, ResultPart id e f)
resultPrefix p = (mempty, p)

failure :: Parser t s r
failure = Failure "failure"

infix  0 <?>

-- | Name a parser for error reporting in case it fails.
(<?>) :: Monoid s => Parser t s r -> String -> Parser t s r
Failure{} <?> msg = Failure msg
p@Result{} <?> _ = p
p@ResultPart{} <?> _ = p
p <?> msg = apply (<?> msg) p

-- | Usage of 'fmap' destroys the incrementality of parsing results, if you need it use 'mapIncremental' instead.
instance Monoid s => Functor (Parser t s) where
   fmap f (Result s r) = Result s (f r)
   fmap g (ResultPart r e f) = ResultPart id (fmap g $ prepend r $ feedEof e) (fmap g . prepend r . f)
   fmap f p = apply (fmap f) p

-- | The '<*>' combinator requires its both arguments to provide complete parsing results, takeWhile '*>' and '<*'
-- preserve the incremental results.
instance Monoid s => Applicative (Parser t s) where
   pure = Result mempty
   Result s r <*> p = r <$> feed s p
   p1 <*> p2 = apply (<*> p2) p1

   Result s _ *> p = feed s p
   ResultPart _ e f *> p | isInfallible p = ResultPart id (e *> p) ((*> p) . f)
                         | otherwise = Delay (e *> p) ((*> p) . f)
   p1 *> p2 = apply (*> p2) p1

   Result s r <* p = feed s p *> pure r
   ResultPart r e f <* p | isInfallible p = ResultPart r (e <* p) ((<* p) . f)
   p1 <* p2 = apply (<* p2) p1

-- | Usage of '>>=' destroys the incrementality of its left argument's parsing results, but '>>' is safe to use.
instance Monoid s => Monad (Parser t s) where
   return = pure
   Result s r >>= f = feed s (f r)
   p >>= f = apply (>>= f) p
   (>>) = (*>)

instance Monoid s => MonoidApplicative (Parser t s) where
   -- | The '+<*>' operator is specialized to return incremental parsing results.
   Result s r +<*> p = resultPart r (feed s p)
   p1 +<*> p2 = apply (+<*> p2) p1
   -- | Join operator on two parsers of the same type, preserving the incremental results.
   _ >< p@Failure{} = p
   p1 >< p2 | isInfallible p2 = appendIncremental p1 p2
            | otherwise       = append p1 p2

appendIncremental :: (Monoid s, Monoid r) => Parser t s r -> Parser t s r -> Parser t s r
appendIncremental (Result s r) p = resultPart (mappend r) (feed s p)
appendIncremental (ResultPart r e f) p2 = ResultPart r (appendIncremental e p2) (flip appendIncremental p2 . f)
appendIncremental p1 p2 = apply (`appendIncremental` p2) p1

append :: (Monoid s, Monoid r) => Parser t s r -> Parser t s r -> Parser t s r
append (Result s r) p2 = prepend (mappend r) (feed s p2)
append p1 p2 = apply (`append` p2) p1

-- | Two parsers can be sequentially joined.
instance (Monoid s, Monoid r) => Monoid (Parser t s r) where
   mempty = return mempty
   mappend = (><)

instance (Alternative (Parser t s), Monoid s) => MonoidAlternative (Parser t s) where
   moptional p = p <|> mempty
   concatMany = fst . manies
   concatSome = snd . manies

manies :: (Alternative (Parser t s), Monoid s, Monoid r) => Parser t s r -> (Parser t s r, Parser t s r)
manies p = (many, some)
   where many = resultPart id (some <|> mempty)
         some = appendIncremental p many

infixl 3 <||>
infixl 3 <<|>

(<||>) :: Parser t s r -> Parser t s r -> Parser t s r
Delay e1 f1 <||> Delay e2 f2 = Delay (e1 <||> e2) (\s-> f1 s <||> f2 s)
Failure{} <||> p = p
p <||> Failure{} = p
p1@Result{} <||> p2 = Choice p1 p2
p1@ResultPart{} <||> p2 = Choice p1 p2
Choice p1a p1b <||> p2 | isInfallible p1a = Choice p1a (p1b <||> p2)
p1 <||> p2@Result{} = Choice p2 p1
p1 <||> p2@ResultPart{} = Choice p2 p1
p1 <||> Choice p2a p2b | isInfallible p2a = Choice p2a (p1 <||> p2b)
p1 <||> p2 = Choice p1 p2

(<<|>) :: Monoid s => Parser t s r -> Parser t s r -> Parser t s r
Failure{} <<|> p = p
p <<|> _ | isInfallible p = p
p <<|> Failure{} = p
p1 <<|> p2 = if isInfallible p2 then ResultPart id e f else Delay e f
   where e = feedEof p1 <<|> feedEof p2
         f s = feed s p1 <<|> feed s p2

defaultMany :: (Monoid s, Alternative (Parser t s)) => Parser t s r -> Parser t s [r]
defaultMany = fst . defaultManySome

defaultSome :: (Monoid s, Alternative (Parser t s)) => Parser t s r -> Parser t s [r]
defaultSome = snd . defaultManySome

defaultManySome :: (Monoid s, Alternative (Parser t s)) => Parser t s r -> (Parser t s [r], Parser t s [r])
defaultManySome p = (many, some)
   where many = resultPart id (some <|> pure [])
         some = (:) <$> p +<*> many
{-# INLINE defaultManySome #-}

-- instance (Monoid s, Monoid r, Show s, Show r) => Show (Parser t s r) where
--    show = showWith (show . ($ mempty)) show

showWith :: (Monoid s, Monoid r, Show s) => ((s -> Parser t s r) -> String) -> (r -> String) -> Parser t s r -> String
showWith _ _ (Failure s) = "Failure " ++ show s
showWith _ sr (Result s r) = "(Result " ++ shows s (" " ++ sr r ++ ")")
showWith sm sr (ResultPart r e f) =
   "(ResultPart (mappend " ++ sr (r mempty) ++ ") " ++ showWith sm sr e ++ " " ++ sm f ++ ")"
showWith sm sr (Choice p1 p2) = "(Choice " ++ showWith sm sr p1 ++ " " ++ showWith sm sr p2 ++ ")"
showWith sm sr (Delay e f) = "(Delay " ++ showWith sm sr e ++ " " ++ sm f ++ ")"

-- | Like 'fmap', but capable of mapping partial results, being restricted to 'Monoid' types only.
mapIncremental :: (Monoid s, Monoid a, Monoid b) => (a -> b) -> Parser p s a -> Parser p s b
mapIncremental f (Result s r) = Result s (f r)
mapIncremental g (ResultPart r e f) = 
   ResultPart (mappend $ g $ r mempty) (mapIncremental g e) (mapIncremental g . f)
mapIncremental f p = apply (mapIncremental f) p

-- | Behaves like the argument parser, but without consuming any input.
lookAhead :: Monoid s => Parser t s r -> Parser t s r
lookAhead p = lookAheadInto mempty p
   where lookAheadInto :: Monoid s => s -> Parser t s r -> Parser t s r
         lookAheadInto _ p@Failure{}        = p
         lookAheadInto t (Result _ r)       = Result t r
         lookAheadInto t (ResultPart r e f) = ResultPart r (lookAheadInto t e) (\s-> lookAheadInto (mappend t s) (f s))
         lookAheadInto t (Choice p1 p2)     = lookAheadInto t p1 <||> lookAheadInto t p2
         lookAheadInto t (Delay e f)        = Delay (lookAheadInto t e) (\s-> lookAheadInto (mappend t s) (f s))

-- | Does not consume any input; succeeds (with 'mempty' result) iff the argument parser fails.
notFollowedBy :: (Monoid s, Monoid r) => Parser t s r' -> Parser t s r
notFollowedBy = lookAheadNotInto mempty
   where lookAheadNotInto :: (Monoid s, Monoid r) => s -> Parser t s r' -> Parser t s r
         lookAheadNotInto t Failure{}   = Result t mempty
         lookAheadNotInto t (Delay e f) = Delay (lookAheadNotInto t e) (\s-> lookAheadNotInto (mappend t s) (f s))
         lookAheadNotInto t p | isInfallible p = Failure "notFollowedBy"
                              | otherwise = Delay (lookAheadNotInto t $ feedEof p) 
                                                  (\s-> lookAheadNotInto (mappend t s) (feed s p))

-- | Provides a partial parsing result.
resultPart :: Monoid s => (r -> r) -> Parser t s r -> Parser t s r
resultPart _ Failure{} = error "Internal contradiction"
resultPart f (Result s r) = Result s (f r)
resultPart r1 (ResultPart r2 e f) = ResultPart (r1 . r2) e f
resultPart r p = ResultPart r (feedEof p) (flip feed p)

isInfallible :: Parser t s r -> Bool
isInfallible Result{} = True
isInfallible ResultPart{} = True
isInfallible (Choice p _) = isInfallible p
isInfallible _ = False

prepend :: (r -> r) -> Parser t s r -> Parser t s r
prepend _ p@Failure{} = p
prepend r1 (Result s r2) = Result s (r1 r2)
prepend r1 (ResultPart r2 e f) = ResultPart (r1 . r2) e f
prepend r (Choice p1 p2) = Choice (prepend r p1) (prepend r p2)
prepend r (Delay e f) = Delay (prepend r e) (prepend r . f)

apply :: Monoid s => (Parser t s r -> Parser t s r') -> Parser t s r -> Parser t s r'
apply _ (Failure s) = Failure s
apply f (Choice p1 p2) = f p1 <||> f p2
apply g (Delay e f) = Delay (g e) (g . f)
apply g (ResultPart r e f) = Delay (g $ prepend r e) (g . prepend r . f)
apply f p = Delay (f $ feedEof p) (\s-> f $ feed s p)

mapType :: (Parser t s r -> Parser b s r) -> Parser t s r -> Parser b s r
mapType _ (Failure s) = Failure s
mapType _ (Result s r) = Result s r
mapType g (ResultPart r e f) = ResultPart r (g e) (g . f)
mapType f (Choice p1 p2) = Choice (f p1) (f p2)
mapType g (Delay e f) = Delay (g e) (g . f)

more :: (s -> Parser t s r) -> Parser t s r
more = Delay (Failure "more")

-- | A parser that fails on any input and succeeds at its end.
eof :: (MonoidNull s, Monoid r) => Parser t s r
eof = Delay mempty (\s-> if null s then eof else Failure "eof")

-- | A parser that accepts any single input atom.
anyToken :: FactorialMonoid s => Parser t s s
anyToken = more f
   where f s = case splitPrimePrefix s
               of Just (first, rest) -> Result rest first
                  Nothing -> anyToken

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s) => s -> Parser t s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: FactorialMonoid s => (s -> Bool) -> Parser t s s
satisfy predicate = p
   where p = more f
         f s = case splitPrimePrefix s
               of Just (first, rest) -> if predicate first then Result rest first else Failure "satisfy"
                  Nothing -> p

-- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the given
-- predicate.
satisfyChar :: TextualMonoid s => (Char -> Bool) -> Parser t s s
satisfyChar predicate = p
   where p = more f
         f s = case splitPrimePrefix s
               of Just (first, rest) -> case Textual.characterPrefix first
                                        of Just c -> if predicate c then Result rest first else Failure "satisfyChar"
                                           Nothing -> if null rest then p else Failure "satisfyChar"
                  Nothing -> p

-- | A parser that consumes and returns the given prefix of the input.
string :: (LeftReductiveMonoid s, MonoidNull s) => s -> Parser t s s
string x | null x = mempty
string x = more (\y-> case (stripPrefix x y, stripPrefix y x)
                      of (Just y', _) -> Result y' x
                         (Nothing, Nothing) -> Failure "string"
                         (Nothing, Just x') -> string x' >> return x)

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'concatMany . satisfy'.
takeWhile :: (FactorialMonoid s, MonoidNull s) => (s -> Bool) -> Parser t s s
takeWhile pred = while
   where while = ResultPart id (return mempty) f
         f s = let (prefix, suffix) = span pred s
               in if null suffix then resultPart (mappend prefix) while
                  else Result suffix prefix

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'concatSome . satisfy'.
takeWhile1 :: (FactorialMonoid s, MonoidNull s) => (s -> Bool) -> Parser t s s
takeWhile1 pred = more f
   where f s | null s = takeWhile1 pred
             | otherwise = let (prefix, suffix) = span pred s
                           in if null prefix then Failure "takeWhile1"
                              else if null suffix then resultPart (mappend prefix) (takeWhile pred)
                                   else Result suffix prefix

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
takeCharsWhile :: (TextualMonoid s, MonoidNull s) => (Char -> Bool) -> Parser t s s
takeCharsWhile pred = while
   where while = ResultPart id (return mempty) f
         f s = let (prefix, suffix) = Textual.span (const False) pred s
               in if null suffix then resultPart (mappend prefix) while
                  else let (prefix', suffix') = Textual.span (const True) (const False) suffix
                       in if null prefix' then Result suffix prefix
                          else resultPart (mappend prefix . mappend prefix') (f suffix')

-- | Specialization of 'takeWhile1' on 'TextualMonoid' inputs, accepting the longest non-empty sequence of input atoms
-- that match the given predicate; an optimized version of 'concatSome . satisfyChar'.
takeCharsWhile1 :: (TextualMonoid s, MonoidNull s) => (Char -> Bool) -> Parser t s s
takeCharsWhile1 pred = more f
   where f s | null s = takeCharsWhile1 pred
             | otherwise = let (prefix, suffix) = Textual.span (const False) pred s
                               (prefix', suffix') = Textual.span (const True) (const False) suffix
                           in if null prefix
                              then if null prefix' then Failure "takeCharsWhile1"
                                   else prepend (mappend prefix') (f suffix')
                              else if null suffix then resultPart (mappend prefix) (takeCharsWhile pred)
                                   else if null prefix' then Result suffix prefix
                                        else resultPart (mappend prefix . mappend prefix')
                                                        (feed suffix' $ takeCharsWhile pred)

-- | Accepts the given number of occurrences of the argument parser.
count :: (Monoid s, Monoid r) => Int -> Parser t s r -> Parser t s r
count n p | n > 0 = p >< count (pred n) p
          | otherwise = mempty

-- | Discards the results of the argument parser.
skip :: (Monoid s, Monoid r) => Parser t s r' -> Parser t s r
skip p = p *> mempty

-- | Repeats matching the first argument until the second one succeeds.
manyTill :: (Monoid s, Monoid r) => Parser t s r -> Parser t s r' -> Parser t s r
manyTill next end = if isInfallible next then t1 else t2
   where t1 = skip end <<|> appendIncremental next t1
         t2 = skip end <<|> append next t2

-- | A parser that accepts all input.
acceptAll :: Monoid s => Parser t s s
acceptAll = ResultPart id mempty f
   where f s = ResultPart (mappend s) mempty f

-- | Parallel parser conjunction: the combined parser keeps accepting input as long as both arguments do.
and :: (Monoid s, Monoid r1, Monoid r2) => Parser t s r1 -> Parser t s r2 -> Parser t s (r1, r2)
Failure s `and` _ = Failure s
_ `and` Failure s = Failure s
p `and` Result _ r = fmap (\x-> (x, r)) (feedEof p)
Result _ r `and` p = fmap (\x-> (r, x)) (feedEof p)
ResultPart r e f `and` p | isInfallible p =
   ResultPart (\(r1, r2)-> (r r1, r2)) (e `and` feedEof p) (\s-> f s `and` feed s p)
p `and` ResultPart r e f | isInfallible p =
   ResultPart (\(r1, r2)-> (r1, r r2)) (feedEof p `and` e) (\s-> feed s p `and` f s)
Choice p1a p1b `and` p2 = (p1a `and` p2) <||> (p1b `and` p2)
p1 `and` Choice p2a p2b = (p1 `and` p2a) <||> (p1 `and` p2b)
p1 `and` p2 = Delay (feedEof p1 `and` feedEof p2) (\s-> feed s p1 `and` feed s p2)

-- | A sequence parser that preserves incremental results, otherwise equivalent to 'Alternative.liftA2' (,)
andThen :: (Monoid s, Monoid r1, Monoid r2) => Parser t s r1 -> Parser t s r2 -> Parser t s (r1, r2)
Result s r `andThen` p | isInfallible p = resultPart (mappend (r, mempty)) (feed s (mapIncremental ((,) mempty) p))
ResultPart r e f `andThen` p | isInfallible p = ResultPart (\(r1, r2)-> (r r1, r2)) (e `andThen` p) ((`andThen` p) . f)
p1 `andThen` p2 = apply (`andThen` p2) p1
