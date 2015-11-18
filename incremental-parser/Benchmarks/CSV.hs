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

{-# LANGUAGE Haskell2010, BangPatterns, ExistentialQuantification, FlexibleContexts, OverloadedStrings,
  ScopedTypeVariables #-}

module Main (main, parseWhole, parseChunked) where

import Prelude hiding (null, splitAt)
import Control.Applicative (Alternative, (<$>), (<*>), (<*), (*>), (<|>), many, pure)
import Control.Monad (void)
import Data.Foldable (foldl')
import Data.Monoid (Monoid, (<>), mappend, mconcat, mempty)
import Data.Monoid.Textual (TextualMonoid)
import Data.Monoid.Factorial (FactorialMonoid (splitAt))
import Data.Monoid.Null (MonoidNull (null))
import Text.ParserCombinators.Incremental.LeftBiasedLocal

import Control.DeepSeq (NFData(..))
import Criterion.Main (bench, bgroup, defaultMain, nf)
   
import qualified Data.ByteString as B
import qualified Data.Text.IO as T

import Data.Monoid.Instances.ByteString.UTF8 (ByteStringUTF8(ByteStringUTF8))
import Data.Monoid.Instances.Concat (Concat(extract))

instance NFData ByteStringUTF8 where
  rnf (ByteStringUTF8 b) = rnf b

instance NFData a => NFData (Concat a) where
  rnf s = rnf (extract s)

endOfInput :: MonoidNull s => Parser s ()
endOfInput = eof

char :: TextualMonoid t => Char -> Parser t t
char = satisfyChar . (==)

sepBy1 :: Alternative f => f a -> f s -> f [a]
sepBy1 p q = (:) <$> p <*> many (q *> p)
             
lineEnd :: TextualMonoid t => Parser t ()
lineEnd = void (char '\n') <|> void (string "\r\n")
          <|> void (char '\r')
          <?> "end of line"

unquotedField :: TextualMonoid t => Parser t t
unquotedField = takeCharsWhile (`notElem` (",\n\r\"" :: [Char]))
                <?> "unquoted field"

insideQuotes :: TextualMonoid t => Parser t t
insideQuotes = mappend <$> takeCharsWhile (/= '"')
               <*> (mconcat
                    <$> many (mappend <$> dquotes <*> insideQuotes))
               <?> "inside of double quotes"

   where dquotes = string "\"\"" >> return "\""
                   <?> "paired double quotes"

quotedField :: TextualMonoid t => Parser t t
quotedField = char '"' *> insideQuotes <* char '"'
              <?> "quoted field"

field :: TextualMonoid t => Parser t t
field = quotedField <|> unquotedField
        <?> "field"

record :: TextualMonoid t => Parser t [t]
record = field `sepBy1` char ','


-- file1 is not incremental because it's fallible
file1 :: TextualMonoid t => Parser t [[t]]
file1 = (:) <$> record
        +<*> manyTill (lineEnd *> ((:[]) <$> record))
                      (moptional lineEnd *> endOfInput)
        <?> "file"

file2 :: forall t. TextualMonoid t => Parser t [[t]]
file2 = (:) <$> record
        +<*> many ((notFollowedBy (moptional lineEnd *> endOfInput) :: Parser t ())
                  *> lineEnd *> record)
        <?> "file"

parseWhole :: TextualMonoid t => Parser t [[t]] -> t -> [([[t]], t)]
parseWhole p s = completeResults (feedEof $ feed s p)

parseChunked :: TextualMonoid t => Parser t [[t]] -> [t] -> [([[t]], t)]
parseChunked p chunks = completeResults (feedEof $ foldl' (flip feed) p $ chunks)

parseIncremental :: (Monoid r, TextualMonoid t) => Parser t [[t]] -> ([[t]] -> r) -> [t] -> r
parseIncremental p0 process chunks = let (inc, p') = foldl' feedInc (mempty, p0) chunks
                                     in case completeResults (feedEof p')
                                        of [] -> inc
                                           (r,_):_ -> inc <> process r
   where feedInc (!inc, !p) chunk = let !(prefix, p') = resultPrefix (feed chunk p)
                                    in (inc <> process prefix, p')

chunksOf :: FactorialMonoid t => Int -> t -> [t]
chunksOf len t
   | null t = []
   | (h, t') <- splitAt len t = h : chunksOf len t'

chunkSize :: Int
chunkSize = 1024

data Input = forall t. (NFData t, TextualMonoid t) => Input String t

main :: IO ()
main = do
   airportsS <- readFile "Benchmarks/airports.dat"
   airportsT <- T.readFile "Benchmarks/airports.dat"
   airportsB <- B.readFile "Benchmarks/airports.dat"
   let inputs = [Input "UTF8" (ByteStringUTF8 airportsB),
                 Input "Text" airportsT,
                 Input "Concat String" (pure airportsS :: Concat String)]
   defaultMain [
      let chunks = chunksOf chunkSize i
      in nf id chunks `seq` bgroup inputName [
         bgroup parserName [
            bench "whole" $ nf (parseWhole p) i,
            bench "chunked" $ nf (parseChunked p) chunks,
            bench "incremental" $ nf (parseIncremental p id) chunks,
            bench "incremental'" $ nf (parseIncremental p (pure :: a -> Concat a)) chunks]
            | (parserName, p) <- [("manyTill", file1), ("many", file2)]]
         | Input inputName i <- inputs]
