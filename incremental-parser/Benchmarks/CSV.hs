{-# Language FlexibleContexts, OverloadedStrings, ExistentialQuantification #-}
module Main (main, parseWhole, parseChunked) where

import Prelude hiding (splitAt)
import Control.Applicative (Alternative, (<|>), many)
import Control.Monad (void)
import Data.Foldable (foldl')
import Data.Monoid ((<>))
import Data.Monoid.Textual (TextualMonoid)
import Data.Monoid.Factorial (splitAt)
import Data.Monoid.Null (MonoidNull)
import Text.ParserCombinators.Incremental.LeftBiasedLocal

import Control.DeepSeq (NFData(..))
import Criterion.Main (bench, bgroup, defaultMain, nf)
   
import qualified Data.ByteString as B
import qualified Data.Text as T
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

file1 :: TextualMonoid t => Parser t [[t]]
file1 = (:) <$> record
        <*> manyTill (lineEnd *> ((:[]) <$> record))
                     (moptional lineEnd *> endOfInput)
        <?> "file"

file2 :: TextualMonoid t => Parser t [[t]]
file2 = (:) <$> record
        <*> many (notFollowedBy (moptional lineEnd *> endOfInput)
                  >< lineEnd *> record)
        <?> "file"

parseWhole :: TextualMonoid t => Parser t [[t]] -> t -> [([[t]], t)]
parseWhole file s = completeResults (feedEof $ feed s file)

parseChunked :: TextualMonoid t => Parser t [[t]] -> Int -> t -> [([[t]], t)]
parseChunked file chunkLength s = completeResults (feedEof $ foldl' (flip feed) file $ splitAt chunkLength s)

parseIncremental :: (Monoid r, TextualMonoid t) => Parser t [[t]] -> ([[t]] -> r) -> Int -> t -> r
parseIncremental file process chunkLength s = let (inc, p) = foldl' feedInc (mempty, file) (splitAt chunkLength s)
                                              in case completeResults (feedEof p)
                                                 of [] -> inc
                                                    (r,_):_ -> inc <> process r
   where feedInc (inc, p) chunk = let (prefix, p') = resultPrefix (feed chunk p)
                                  in (inc <> process prefix, p')

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
      bgroup inputName [
         bgroup parserName [
            bench "whole" $ nf (parseWhole p) i,
            bench "chunked" $ nf (parseChunked p chunkSize) i,
            bench "incremental" $ nf (parseIncremental p id chunkSize) i]
            | (parserName, p) <- [("manyTill", file1), ("many", file2)]]
         | Input inputName i <- inputs]
