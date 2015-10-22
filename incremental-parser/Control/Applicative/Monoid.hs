{- 
    Copyright 2011 Mario Blazevic

    This file is part of the Streaming Component Combinators (SCC) project.

    The SCC project is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
    License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later
    version.

    SCC is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
    of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along with SCC.  If not, see
    <http://www.gnu.org/licenses/>.
-}

-- | This module defines the AlternativeMonoid class

module Control.Applicative.Monoid (
   MonoidApplicative(..), MonoidAlternative(..)
   )
where

import Control.Applicative (Applicative (pure), Alternative ((<|>), some, many), liftA2)
import Data.Monoid (Monoid, mempty, mappend, mconcat)


class Applicative f => MonoidApplicative f where
   -- | Lifted and potentially optimized monoid `mappend` operation from the parameter type.
   infixl 5 ><
   (><) :: Monoid a => f a -> f a -> f a
   (><) = liftA2 mappend

class (Alternative f, MonoidApplicative f) => MonoidAlternative f where
   -- | Like 'optional', but restricted to 'Monoid' results.
   moptional :: Monoid a => f a -> f a
   moptional x = x <|> pure mempty

   -- | Zero or more argument occurrences like 'many', but concatenated.
   concatMany :: Monoid a => f a -> f a
   concatMany = fmap mconcat . many

   -- | One or more argument occurrences like 'some', but concatenated.
   concatSome :: Monoid a => f a -> f a
   concatSome = fmap mconcat . some
