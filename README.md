The incremental-parser library is yet another parser combinator Haskell library, providing the usual set of
`Applicative`, `Alternative`, and `Monad` combinators. Apart from this, it has three twists that make it unique.

First, the parser is incremental. That means it can be fed its input in chunks, and in proper circumstances it can also
provide the parsed output in chunks. For this to be possible the result type must be a `Monoid`. The complete parsing
result is then a concatenation of the partial results.

In order to make the incremental parsing easier, the combinator set is optimized for monoidal results. Apart from the
usual combinators `many` and `some`, for example, there are `concatMany` and `concatSome` operators.

    many :: Parser s r -> Parser s [r]
    concatMany :: (Monoid s, Monoid r) => Parser s r -> Parser s r

The second weirdness, this one shared with [Picoparsec](http://hackage.haskell.org/package/picoparsec), is that the the
parser is generic in its input stream type, but this type is parameterized in a holistic way. There is no separate token
type. Primitive parsers that need to peek into the input require its type to be an instance of a monoid subclass, from
the [monoid-subclasses](http://hackage.haskell.org/package/monoid-subclasses) package.

In Parsec:

    string :: Stream s m Char => String -> ParsecT s u m String
    char :: Stream s m Char => Char -> ParsecT s u m Char
    anyToken :: (Stream s m t, Show t) => ParsecT s u m t

In Attoparsec:

    string :: ByteString -> Parser ByteString
    word8 :: Word8 -> Parser Word8
    anyWord8 :: Parser Word8

In incremental-parser and Picoparsec:

    string :: (LeftCancellativeMonoid s, MonoidNull s) => s -> Parser s s
    token :: (Eq s, FactorialMonoid s) => s -> Parser s s
    anyToken :: FactorialMonoid s => Parser s s

Finally, the library being implemented on the basis of Brzozowski derivatives, it can provide both the symmetric and the
left-biased choice, `<||>` and `<<|>`. This is the same design choice made by
[`Text.ParserCombinators.ReadP`](http://hackage.haskell.org/package/base/docs/Text-ParserCombinators-ReadP.html#g:2) and
uu-parsinglib. Parsec and its progeny on the other hand provide only the faster left-biased choice, at some cost to the
expressiveness of the combinator language. The standard `<|>` Alternative operator acts as one or the other of the
above, depending on whether the first type parameter of `Parser` is `Parallel` or `LeftBiasedLocal`.
