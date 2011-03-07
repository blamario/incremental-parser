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

{-# LANGUAGE ScopedTypeVariables, Rank2Types, ExistentialQuantification #-}

module Text.ParserCombinators.Incremental (
   -- * The Parser type
   Parser,
   -- * Using a Parser
   feed, feedEof, feedListPrefix, results, resultPrefix,
   -- * Parser primitives
   empty, eof, anyToken, token, satisfy, count, acceptAll, string, prefixOf, whilePrefixOf, while, while1,
   skip, optional, optionMaybe, many, many0, many1, manyTill,
   -- * Parser combinators
   pmap, (><), (<<|>), lookAhead, lookAheadNot, and, andThen,
   -- * Utilities
   showWith
   )
where

import Prelude hiding (and, foldl)
import Control.Applicative (Applicative (pure, (<*>)), Alternative (empty, (<|>), some, many))
import Control.Monad (Functor (fmap), Monad (return, (>>=), (>>)), MonadPlus (mzero, mplus), liftM2)
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid, mempty, mappend)
import Data.Monoid.Cancellative (LeftCancellativeMonoid(mstripPrefix))
import Data.Monoid.Null (MonoidNull(mnull))
import Data.Foldable (Foldable, foldl, toList)

-- | This is a cofunctor data type for selecting a prefix of an input stream. If the next input item is acceptable, the
-- ticker function returns the ticker for the rest of the stream. If not, it returns 'Nothing'.
data Parser s r = Failure
                | Result s r
                | ResultPart (r -> r) (Parser s r)
                | Choice (Parser s r) (Parser s r)
                | CommitedLeftChoice (Parser s r) (Parser s r)
                | More (s -> Parser s r)
                | forall r'. Apply (Parser s r' -> Parser s r) (Parser s r')
                | forall r'. ApplyInput (s -> Parser s r' -> Parser s r) (Parser s r')

feed :: MonoidNull s => s -> Parser s r -> Parser s r
feed _ Failure = Failure
feed s (Result t r) = Result (mappend t s) r
feed s (ResultPart r p) = resultPart r (feed s p)
feed s (Choice p1 p2) = feed s p1 <|> feed s p2
feed s (CommitedLeftChoice p1 p2) = feed s p1 <<|> feed s p2
feed s p@(More f) = if mnull s then p else f s
feed s (Apply f p) = f (feed s p)
feed s (ApplyInput f p) = f s (feed s p)

feedEof :: MonoidNull s => Parser s r -> Parser s r
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

feedListPrefix :: [s] -> [s] -> Parser [s] r -> (Parser [s] r, [s])
feedListPrefix whole chunk p = feedRest chunk p
   where feedRest [] (Result t r) = (Result mempty r, t)
         feedRest rest (Result t r) = (Result mempty r, mappend t rest)
         feedRest _ Failure = (Failure, whole)
         feedRest [] p = (p, [])
         feedRest l p = feedRest [] (feed l p)

results :: Parser s r -> [(r, s)]
results (Result t r) = [(r, t)]
results (ResultPart f p) = map (\(r, t)-> (f r, t)) (results p)
results (Choice p1@Result{} p2) = results p1 ++ results p2
results _ = []

hasResult :: Parser s r -> Bool
hasResult Result{} = True
hasResult (ResultPart _ p) = hasResult p
hasResult (Choice Result{} _) = True
hasResult (CommitedLeftChoice _ p) = hasResult p
hasResult _ = False

resultPrefix :: Monoid r => Parser s r -> (Maybe r, Parser s r)
resultPrefix (Result t r) = (Just r, Result t mempty)
resultPrefix (ResultPart f p) = (Just (f $ fromMaybe mempty r), p')
   where (r, p') = resultPrefix p
resultPrefix p = (Nothing, p)

lookAhead :: MonoidNull s => Parser s r -> Parser s r
lookAhead p = lookAheadInto mempty p

lookAheadNot :: (MonoidNull s, Monoid r) => Parser s r' -> Parser s r
lookAheadNot = lookAheadNotInto mempty

lookAheadInto :: MonoidNull s => s -> Parser s r -> Parser s r
lookAheadInto t Failure               = Failure
lookAheadInto t (Result _ r)          = Result t r
lookAheadInto t (ResultPart r p)      = resultPart r (lookAheadInto t p)
lookAheadInto t (More f)              = More (\s-> lookAheadInto (mappend t s) (f s))
lookAheadInto t (Choice p1 p2)        = lookAheadInto t p1 <|> lookAheadInto t p2
lookAheadInto t p                     = ApplyInput (\t' p'-> lookAheadInto (mappend t t') p') p

lookAheadNotInto :: (MonoidNull s, Monoid r) => s -> Parser s r' -> Parser s r
lookAheadNotInto t Failure               = Result t mempty
lookAheadNotInto t (Result _ r)          = Failure
lookAheadNotInto t (Choice (Result _ r) _) = Failure
lookAheadNotInto t (ResultPart r p)      = lookAheadNotInto t p
lookAheadNotInto t p                     = ApplyInput (\t' p'-> lookAheadNotInto (mappend t t') p') p

resultPart :: (r -> r) -> Parser s r -> Parser s r
resultPart _ Failure = Failure
resultPart f (Result t r) = Result t (f r)
resultPart f (Choice (Result t r) p) = Choice (Result t (f r)) (resultPart f p)
resultPart f (ResultPart g p) = ResultPart (f . g) p
resultPart f p = ResultPart f p

instance MonoidNull s => Functor (Parser s) where
   fmap f Failure = Failure
   fmap f (Result t r) = Result t (f r)
   fmap f (Choice p1 p2) = fmap f p1 <|> fmap f p2
   fmap f (CommitedLeftChoice p1 p2) = fmap f p1 <<|> fmap f p2
   fmap f (More g) = More (fmap f . g)
   fmap f p = Apply (fmap f) p

instance MonoidNull s => Applicative (Parser s) where
   pure = Result mempty
   Failure <*> _ = Failure
   Result t f <*> p = fmap f (feed t p)
   Choice p1a p1b <*> p2 = (p1a <*> p2) <|> (p1b <*> p2)
   More f <*> p = More (\x-> f x <*> p)
   p1 <*> p2 = Apply (<*> p2) p1

instance MonoidNull s => Alternative (Parser s) where
   -- | A parser that succeeds without consuming any input.
   empty = Failure
   
   Failure <|> p = p
   p <|> Failure = p
   More f <|> More g = More (\x-> f x <|> g x)
   p1@Result{} <|> p2 = Choice p1 p2
   Choice p1a@Result{} p1b <|> p2 = Choice p1a (p1b <|> p2)
   p1 <|> p2@Result{} = Choice p2 p1
   p1 <|> Choice p2a@Result{} p2b = Choice p2a (p1 <|> p2b)
   p1 <|> p2 = Choice p1 p2

instance MonoidNull s => Monad (Parser s) where
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

instance MonoidNull s => MonadPlus (Parser s) where
   mzero = Failure
   mplus = (<<|>)

instance (MonoidNull s, Monoid r) => Monoid (Parser s r) where
   mempty = return mempty
   mappend = (><)

-- instance (MonoidNull s, Monoid r, Show s, Show r) => Show (Parser s r) where
--    show = showWith (show . ($ mempty)) show

showWith :: (MonoidNull s, Monoid r, Show s) => ((s -> Parser s r) -> String) -> (r -> String) -> Parser s r -> String
showWith sm sr Failure = "Failure"
showWith sm sr (Result t r) = "(Result (" ++ shows t ("++) " ++ sr r ++ ")")
showWith sm sr (ResultPart f p) = "(ResultPart (mappend " ++ sr (f mempty) ++ ") " ++ showWith sm sr p ++ ")"
showWith sm sr (Choice p1 p2) = "(Choice " ++ showWith sm sr p1 ++ " " ++ showWith sm sr p2 ++ ")"
showWith sm sr (CommitedLeftChoice p1 p2) = "(CommitedLeftChoice " ++ showWith sm sr p1 ++ " " ++ showWith sm sr p2 ++ ")"
showWith sm sr (More f) = "(More $ " ++ sm f ++ ")"
showWith sm sr (Apply f p) = "Apply"
showWith sm sr (ApplyInput f p) = "ApplyInput"

pmap :: (MonoidNull s, Monoid a, Monoid b) => (a -> b) -> Parser s a -> Parser s b
pmap f Failure = Failure
pmap f (Result t r) = Result t (f r)
pmap f (ResultPart r p) = ResultPart (f (r mempty) `mappend`) (pmap f p)
pmap f (Choice p1 p2) = pmap f p1 <|> pmap f p2
pmap f (CommitedLeftChoice p1 p2) = pmap f p1 <<|> pmap f p2
pmap f (More g) = More (pmap f . g)
pmap f p = Apply (pmap f) p

infixl 3 <<|>
(<<|>) :: Parser s r -> Parser s r -> Parser s r
Failure <<|> p = p
p <<|> Failure = p
p <<|> _ | hasResult p = p
More f <<|> More g = More (\x-> f x <<|> g x)
p1 <<|> p2 = CommitedLeftChoice p1 p2

infixl 5 ><
(><) :: forall s r. (MonoidNull s, Monoid r) => Parser s r -> Parser s r -> Parser s r
Failure >< _ = Failure
Result t r >< p = resultPart (mappend r) (feed t p)
ResultPart r p1 >< p2 = resultPart r (p1 >< p2)
Choice p1a p1b >< p2 = (p1a >< p2) <|> (p1b >< p2)
More f >< p = More (\x-> f x >< p)
p1 >< p2 = Apply (>< p2) p1

-- | A parser that fails on any input.
eof :: (MonoidNull s, Monoid r) => Parser s r
eof = lookAheadNot (More return)

-- | A parser that accepts a single input item.
anyToken :: Parser [x] x
anyToken = More (\(x:rest)-> Result rest x)

-- | A parser that accepts a specific input item.
token :: Eq x => x -> Parser [x] x
token x = satisfy (== x)

-- | A parser that accepts an input item only if it satisfies the given predicate.
satisfy :: Eq x => (x -> Bool) -> Parser [x] x
satisfy pred = More (\(x:rest)-> if pred x then Result rest x else Failure)

-- | A parser that accepts a given number of input items.
count :: Int -> Parser [x] [x]
count n | n > 0 = More (\l-> case splitAt n l of (l', []) -> resultPart (mappend l') $ count (n - length l)
                                                 (l', rest) -> Result rest l')
        | otherwise = return []

string :: (LeftCancellativeMonoid s, MonoidNull s) => s -> Parser s s
string x | mnull x = mempty
string x = More (\y-> case (mstripPrefix x y, mstripPrefix y x)
                      of (Just y', _) -> Result y' x
                         (Nothing, Nothing) -> Failure
                         (Nothing, Just x') -> string x' >> return x)

-- | A parser that accepts the longest prefix of input that matches a prefix of the argument list.
prefixOf :: Eq x => [x] -> Parser [x] [x]
prefixOf list = whilePrefixOf (map (==) list)

-- | A parser that accepts a prefix of input as long as each item satisfies the predicate at the same position in the
-- argument list. The length of the predicate list thus determines the maximum number of acepted values.
whilePrefixOf :: [x -> Bool] -> Parser [x] [x]
whilePrefixOf (p : rest) = 
   CommitedLeftChoice
      (More $ \(x:xs)-> if p x then resultPart (x:) (feed xs (whilePrefixOf rest)) else Failure)
      (return [])
whilePrefixOf [] = return []

-- | A parser that accepts all input as long as it matches the given predicate.
while :: (x -> Bool) -> Parser [x] [x]
while p = t
   where t = CommitedLeftChoice (More (\l-> case span p l
                                            of ([], _) -> Failure
                                               (r, []) -> resultPart (mappend r) t
                                               (r, rest) -> Result rest r))
                                (return [])

-- | A parser that accepts all input as long as it matches the given predicate, and fails if there isn't any.
while1 :: (x -> Bool) -> Parser [x] [x]
while1 p = More (\(x:rest)-> if p x then resultPart (x:) (feed rest $ while p) else Failure)

optional :: (MonoidNull s, Monoid r) => Parser s r -> Parser s r
optional p = p <|> return mempty

optionMaybe :: MonoidNull s => Parser s r -> Parser s (Maybe r)
optionMaybe p = fmap Just p <<|> return Nothing

skip :: (MonoidNull s, Monoid r) => Parser s r' -> Parser s r
skip p = fmap (const mempty) p

many0 :: (MonoidNull s, Monoid r) => Parser s r -> Parser s r
many0 p = many1 p <<|> return mempty

many1 :: (MonoidNull s, Monoid r) => Parser s r -> Parser s r
many1 p = More (\x-> feed x p >< many0 p)

manyTill :: (MonoidNull s, Monoid r) => Parser s r -> Parser s r' -> Parser s r
manyTill next end = t
   where t = skip end <<|> (next >< t)

-- | A parser that accepts all input.
acceptAll :: MonoidNull s => Parser s s
acceptAll = CommitedLeftChoice (More $ \s-> resultPart (mappend s) acceptAll) (return mempty)

-- | Parallel parser conjunction: the result of the combinator keeps accepting input as long as both arguments do.
and :: (MonoidNull s, Monoid r1, Monoid r2) => Parser s r1 -> Parser s r2 -> Parser s (r1, r2)
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

andThen :: (MonoidNull s, Monoid r1, Monoid r2) => Parser s r1 -> Parser s r2 -> Parser s (r1, r2)
Failure `andThen` _ = Failure
Result t r `andThen` p = resultPart (mappend (r, mempty)) (feed t (fmap ((,) mempty) p))
ResultPart f p1 `andThen` p2 = resultPart (\(r1, r2)-> (f r1, r2)) (p1 `andThen` p2)
Choice p1a p1b `andThen` p2 = (p1a `andThen` p2) <|> (p1b `andThen` p2)
More f `andThen` p = More (\x-> f x `andThen` p)
p1 `andThen` p2 = Apply (`andThen` p2) p1
