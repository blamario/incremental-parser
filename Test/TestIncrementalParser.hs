{- 
    Copyright 2011-2018 Mario Blazevic

    This file is part of the Streaming Component Combinators (SCC) project.

    The SCC project is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
    License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later
    version.

    SCC is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
    of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along with SCC.  If not, see
    <http://www.gnu.org/licenses/>.
-}

-- | This module contains tests of "Text.ParserCombinators.Incremental" module.

{-# LANGUAGE FlexibleContexts, FlexibleInstances, ScopedTypeVariables, UndecidableInstances #-}

module Main where

import Control.Applicative (Applicative, Alternative, pure, (<*>), (*>), empty, (<|>))
import Control.Monad (MonadPlus, liftM, liftM2, mzero, mplus)
import Data.List (find, minimumBy, nub, sort)
import Data.Monoid (Monoid(..))
import Data.Semigroup (Semigroup(..))
import System.Environment (getArgs)

import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Property, property, (==>), (.&&.), forAll, oneof, resize, sized, whenFail)
import Test.QuickCheck.Checkers (Binop, EqProp(..), TestBatch, isAssoc, leftId, rightId, verboseBatch)
import Test.QuickCheck.Classes (functor, monad, monoid, applicative, monadFunctor, monadApplicative, monadOr, monadPlus)

import Text.ParserCombinators.Incremental (Parser, feedEof, feed, completeResults,
                                           (><), (<<|>), (<||>), failure,
                                           anyToken, eof, lookAhead, notFollowedBy, satisfy, skip, token, string,
                                           isInfallible, showWith)
import Text.ParserCombinators.Incremental.Symmetric (Symmetric)
import Text.ParserCombinators.Incremental.LeftBiasedLocal (LeftBiasedLocal)

main = do args <- getArgs 
          case args of [] -> mapM_ verboseBatch tests
                       _ -> mapM_ (\batch-> maybe (error ("No test batch named " ++ batch)) verboseBatch 
                                            (find ((batch ==) . fst) tests)) args

data Described a = Described String !a

data TestParser a r = TestParser (Described (Parser a [Bool] r))

describedParser (TestParser (Described _ p)) = p

instance Show (Described a) where
   show (Described desc _) = desc

instance Show (TestParser a r) where
   show (TestParser d) = show d

instance (Arbitrary r, Semigroup r, Monoid r, Show r) => Arbitrary (TestParser a r) where
   arbitrary = fmap TestParser arbitrary

instance Semigroup a => Semigroup (Described a) where
   Described d1 p1 <> Described d2 p2 = Described (d1 ++ " <> " ++ d2) (p1 <> p2)

instance (Semigroup a, Monoid a) => Monoid (Described a) where
   mempty = Described "mempty" mempty
   mappend = (<>)

instance Semigroup r => Semigroup (TestParser a r) where
   TestParser d1 <> TestParser d2 = TestParser (d1 <> d2)

instance (Semigroup r, Monoid r) => Monoid (TestParser a r) where
   mempty = TestParser mempty
   mappend = (<>)

instance EqProp a => EqProp (Described a) where
   Described _ x =-= Described _ y = x =-= y

instance (Ord r, Show r, Monoid r, EqProp r) => EqProp (TestParser a r) where
   TestParser d1 =-= TestParser d2 = d1 =-= d2

instance Functor (TestParser a) where
   fmap f (TestParser (Described d p)) = TestParser (Described ("fmap ? " ++ d) (fmap f p))

instance Applicative (TestParser a) where
   pure x = TestParser (Described "pure ?" (pure x))
   TestParser (Described d1 p1) <*> TestParser (Described d2 p2) =
      TestParser (Described (d1 ++ " <*> " ++ d2) (p1 <*> p2))
   TestParser (Described d1 p1) *> TestParser (Described d2 p2) =
      TestParser (Described (d1 ++ " *> " ++ d2) (p1 >> p2))

instance Monad (TestParser a) where
   return = pure
   TestParser (Described d1 p1) >>= f =
      TestParser (Described (d1 ++ " >>= ?") (p1 >>= describedParser . f))
   (>>) = (*>)

instance Alternative (Parser a [Bool]) => Alternative (TestParser a) where
   empty = TestParser (Described "failure" empty)
   TestParser (Described d1 p1) <|> TestParser (Described d2 p2) =
      TestParser (Described (d1 ++ " <|> " ++ d2) (p1 <|> p2))

instance MonadPlus (Parser a [Bool]) => MonadPlus (TestParser a) where
   mzero = TestParser (Described "mzero" mzero)
   TestParser (Described d1 p1) `mplus` TestParser (Described d2 p2) =
      TestParser (Described (d1 ++ " `mplus` " ++ d2) (mplus p1 p2))

parser2l :: TestParser LeftBiasedLocal (String, String)
parser2l = undefined

parser2s :: TestParser Symmetric (String, String)
parser2s = undefined

parser3l :: TestParser LeftBiasedLocal (String, String, String)
parser3l = undefined

parser3s :: TestParser Symmetric (String, String, String)
parser3s = undefined

tests :: [TestBatch]
tests = [monoid parser3s,
         functor parser3s,
         applicative parser3s,
         alternative parser2s,
         monad parser3s,
         monadFunctor parser2s,
         monadApplicative parser2s,
         monadOr parser2l,
         monadPlus parser2s,
         primitives,
         lookAheadBatch,
         testJoin]

-- | Properties to check that the 'Alternative' @m@ satisfies the alternative
-- properties
alternative :: forall m a b.
               ( Alternative m
               , Arbitrary (m a), Arbitrary (m b)
               , Show (m a), Show (m b)
               , EqProp (m a), EqProp (m b)
               ) =>
               m (a,b) -> TestBatch
alternative = const ( "alternative"
                    , [ ("left zero"     , property leftZeroP)
                      , ("right zero"    , property rightZeroP)
                      , ("left identity" , leftId (<|>) (empty :: m a))
                      , ("right identity", rightId (<|>) (empty :: m a))
                      , ("associativity" , isAssoc ((<|>) :: Binop (m a)))
                      , ("left distribution", property leftDistP)
                      ]
                    )
 where
   leftZeroP :: m a -> Property
   rightZeroP :: m a -> Property
   leftDistP :: m a -> m a -> m b -> Property

   leftZeroP k = (empty *> k) =-= empty
   rightZeroP k = (k *> empty) =-= (empty :: m b)
   leftDistP a b k = ((a <|> b) *> k) =-= ((a *> k) <|> (b *> k))

primitives :: TestBatch
primitives = ("primitives",
              [("anyToken EOF", feedEof (anyToken :: Parser a [Bool] [Bool]) =-= failure),
               ("anyToken list", property tokenListP),
               ("token", property tokenP),
               ("token = satisfy . (==)", property tokenSatisfyP),
               ("satisfy not", property satisfyNotP),
               ("satisfy or not Symmetric", property (satisfyOrNotP (undefined :: Symmetric))),
               ("satisfy or not LeftBiasedLocal", property (satisfyOrNotP (undefined :: LeftBiasedLocal))),
               ("string", property stringP),
               ("feed eof", property feedEofP),
               ("feedEof eof", property feedEofEofP)])
   where tokenListP :: Bool -> [Bool] -> Property
         tokenP :: Bool -> [Bool] -> Property
         tokenSatisfyP :: Bool -> Property
         satisfyNotP :: (Bool -> Bool) -> Property
         satisfyOrNotP :: Alternative (Parser a [Bool]) => a -> (Bool -> Bool) -> Property
         stringP :: [Bool] -> [Bool] -> Property
         feedEofP :: [Bool] -> Property
         feedEofEofP :: Bool
         
         tokenListP x xs = canonicalResults (feed (x:xs) anyToken) =-= [([x], xs)]
         tokenP x xs = canonicalResults (feed (x:xs) (token [x])) =-= [([x], xs)]
         tokenSatisfyP x = token [x] =-= satisfy (== [x])
         satisfyNotP pred = satisfy (pred . head) =-= (notFollowedBy (satisfy (not . pred . head)) >< anyToken)
         satisfyOrNotP (_ :: a) pred = (satisfy (pred . head) <|> satisfy (not . pred . head)) 
                                       =-= (anyToken :: Parser a [Bool] [Bool])
         stringP xs ys = xs /= [] ==> canonicalResults (feed (xs ++ ys) (string xs)) =-= [(xs, ys)]
         feedEofP x = x /= [] ==> feed x eof =-= (failure :: Parser a [Bool] String)
         feedEofEofP = canonicalResults (feedEof eof :: Parser a [Bool] String) == [([], [])]

lookAheadBatch :: TestBatch
lookAheadBatch = ("lookAhead",
                  [("lookAhead", property lookAheadP),
                   ("lookAhead p >> p", property lookAheadConsumeP),
                   ("notFollowedBy p >< p", property lookAheadNotOrP),
                   ("not not Symmetric", property (lookAheadNotNotP (undefined :: Symmetric))),
                   ("not not LeftBiasedLocal", property (lookAheadNotNotP (undefined :: LeftBiasedLocal))),
                   ("lookAhead anyToken", property lookAheadTokenP)])
   where lookAheadP :: [Bool] -> Described (Parser a [Bool] String) -> Bool
         lookAheadConsumeP :: Described (Parser a [Bool] String) -> Property
         lookAheadNotOrP :: Described (Parser a [Bool] String) -> Property
         lookAheadNotNotP :: Alternative (Parser a [Bool]) => a -> Described (Parser a [Bool] String) -> Property
         lookAheadTokenP :: Bool -> [Bool] -> Bool
         
         lookAheadP xs (Described _ p) = completeResults (feed xs $ lookAhead p)
                                         == map (\(r, _)-> (r, xs)) (completeResults (feed xs p))
         lookAheadConsumeP (Described _ p) = (lookAhead p >> p) =-= p
         lookAheadNotOrP (Described _ p) = (notFollowedBy p >< p) =-= failure
         lookAheadNotNotP (_ :: a) (Described _ p) = notFollowedBy (notFollowedBy p :: Parser a [Bool] ()) =-= (skip (lookAhead p) :: Parser a [Bool] ())
         lookAheadTokenP x xs = canonicalResults (feed (x:xs) (lookAhead anyToken)) == [([x], x:xs)]

instance (Eq x, Monoid x, Ord x, Show x) => EqProp (Parser a [Bool] x) where
   p1 =-= p2 = sameResults (feedEof p1) (feedEof p2)
               .&&. forAll (sized $ \n-> resize (min n 20) arbitrary) 
                           (\s-> whenFail (print (s, p1, p2, feed s p1, feed s p2)) 
                                          (if length s < 2 then property True else feed s p1 =-= feed s p2))

sameResults p1 p2 = whenFail (print (canonicalResults p1) >> putStrLn "  !=" >> print (canonicalResults p2)
                              >> putStrLn "  =>" >> print p1 >> putStrLn "  !=" >> print p2)
                    (canonicalResults p1 == canonicalResults p2)

testJoin :: TestBatch
testJoin = ("join",
            [("empty ><", property leftZeroP),
             (">< empty", property rightZeroP),
             ("(<|>) ><", property leftDistP),
             (">< (<||>)", property rightDistP),
             ("><", property joinP1),
             (">< infallible", property joinP2)])
   where leftZeroP :: Described (Parser a [Bool] String) -> Property
         rightZeroP :: Described (Parser a [Bool] String) -> Property
         leftDistP :: Described (Parser a [Bool] String) -> Described (Parser a [Bool] String)
                      -> Described (Parser a [Bool] String) -> Property
         rightDistP :: Described (Parser a [Bool] String) -> Described (Parser a [Bool] String)
                       -> Described (Parser a [Bool] String) -> Property
         joinP1 :: [Bool] -> Described (Parser a [Bool] String) -> Described (Parser a [Bool] String) -> Property
         joinP2 :: [Bool] -> Described (Parser a [Bool] String) -> Described (Parser a [Bool] String) -> Property

         leftZeroP (Described _ k) = (failure >< k) =-= failure
         rightZeroP (Described _ k) = (k >< failure) =-= failure
         leftDistP (Described _ a) (Described _ b) (Described _ k) = ((a <||> b) >< k) =-= ((a >< k) <||> (b >< k))
         rightDistP (Described _ k) (Described _ a) (Described _ b) = (k >< (a <||> b)) =-= ((k >< a) <||> (k >< b))
         joinP1 input (Described _ a) (Described _ b)
            = whenFail (print r1 >> putStrLn "  !=" >> print r2 >> putStrLn "  !=" >> print r1a) (r1 == r2)
            where r1 = canonicalResults (feedEof $ feed input (a >< b))
                  r2 = sort (nub [(r2a ++ r2b, rest') 
                                 | (r2a, rest) <- r1a,
                                   (r2b, rest') <- completeResults (feedEof $ feed rest b)])
                  r1a = canonicalResults (feedEof $ feed input a)
         joinP2 input (Described _ a) (Described _ b)
            = isInfallible b ==>
              whenFail (print r1 >> putStrLn "  !=" >> print r2 >> putStrLn "  !=" >> print r1a) (r1 == r2)
            where r1 = canonicalResults (feed input (a >< b))
                  r2 = sort (nub [(r2a ++ r2b, rest') 
                                 | (r2a, rest) <- r1a,
                                   (r2b, rest') <- completeResults (feed rest b)])
                  r1a = canonicalResults (feed input a)

canonicalResults p = sort $ nub $ completeResults p

instance forall a r. (Arbitrary r, Semigroup r, Monoid r, Show r) => Arbitrary (Described (Parser a [Bool] r)) where
   arbitrary = sized $ 
               \n-> if n == 0
                    then return (Described "empty" failure)
                    else resize (min 50 n) $
                         oneof [return (Described "empty" failure),
                                return (Described "mempty" mempty),
                                sized $ \n-> liftM (\r-> Described ("(return " ++ shows r ")") (return r))
                                                   (resize (pred n) arbitrary),
                                splitSize " >< " (><) (liftM (Described "return ?" . return) arbitrary) arbitrary,
                                splitSize " <||> " (<||>) arbitrary arbitrary,
                                splitSize " <<|> " (<<|>) arbitrary arbitrary,
                                reduceSize "anyToken >> " (anyToken >>) arbitrary,
                                reduceSize "satisfy head >> " (satisfy head >>) arbitrary,
                                reduceSize "satisfy (not . head) >> " (satisfy (not . head) >>) arbitrary,
                                reduceSize "lookAhead " lookAhead arbitrary,
                                reduceSize "notFollowedBy " notFollowedBy (arbitrary
                                                                           :: Gen (Described (Parser a [Bool] r)))]

instance (Monoid r, Show r) => Show (Parser a [Bool] r) where
   show p = showWith (showBoolFun show) show p

instance Semigroup Bool where
   (<>) = (||)

instance Monoid Bool where
   mempty = False
   mappend = (<>)

showBoolFun :: (r -> String) -> ([Bool] -> r) -> String
showBoolFun show f = "\\[b]-> if b then " ++ show (f [True]) ++ " else " ++ show (f [False])

splitSize :: String -> (a -> b -> c) -> Gen (Described a) -> Gen (Described b) -> Gen (Described c)
splitSize binOp f a b =
   sized $ \n-> liftM2 (\(Described s1 x) (Described s2 y)-> Described ('(' : s1 ++ binOp ++ s2 ++  ")") (f x y))
                   (resize (div n 2) a)
                   (resize (div n 2) b)

reduceSize :: String -> (a -> b) -> Gen (Described a) -> Gen (Described b)
reduceSize prefix f a = sized $ \n-> liftM (\(Described s x)-> Described ('(' : prefix ++ s ++ ")") (f x)) (resize (if n > 0 then pred n else n) a)
