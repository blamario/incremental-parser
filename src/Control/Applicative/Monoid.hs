{-
    Copyright 2011-2020 Mario Blazevic
-}

-- | This module defines the 'MonoidApplicative' and 'MonoidAlternative' type classes. Their methods are specialized
-- forms of the standard 'Applicative' and 'Alternative' class methods. Instances of these classes should override the
-- default method implementations with more efficient ones.

module Control.Applicative.Monoid (
   MonoidApplicative(..), MonoidAlternative(..)
   )
where

import Control.Applicative (Applicative (pure, (<*>)), Alternative ((<|>)), (<$>))
import Data.Monoid (Monoid, mempty)
import Data.Semigroup (Semigroup, (<>))


class Applicative f => MonoidApplicative f where
   -- | A variant of the Applicative's '<*>' operator specialized for endomorphic functions.
   infixl 4 +<*>
   (+<*>) :: f (a -> a) -> f a -> f a
   (+<*>) = (<*>)

   -- | Lifted and potentially optimized monoid `Data.Monoid.mappend` operation from the parameter type.
   infixl 5 ><
   (><) :: Semigroup a => f a -> f a -> f a
   a >< b = (<>) <$> a +<*> b

class (Alternative f, MonoidApplicative f) => MonoidAlternative f where
   -- | Like 'optional', but restricted to 'Monoid' results.
   moptional :: (Semigroup a, Monoid a) => f a -> f a
   moptional x = x <|> pure mempty

   -- | Zero or more argument occurrences like 'Control.Applicative.many', but concatenated.
   concatMany :: (Semigroup a, Monoid a) => f a -> f a
   concatMany x = many'
      where many' = some' <|> pure mempty
            some' = x >< many'

   -- | One or more argument occurrences like 'Control.Applicative.some', but concatenated.
   concatSome :: (Semigroup a, Monoid a) => f a -> f a
   concatSome x = some'
      where many' = some' <|> pure mempty
            some' = x >< many'
