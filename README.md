The incremental-parser library is yet another parser combinator library, providing the usual set of `Applicative`,
`Alternative`, and `Monad` combinators. Apart from this, it has four twists that make it unique.

#### Parsing incrementally

First, the parser is incremental. Not only can it be fed its input in chunks, but in proper circumstances it can also
provide its output in parsed chunks. For this to be possible the result type must be a `Monoid`. The complete parsing
result is then a concatenation of the partial results.

In order to make the incremental parsing easier, the combinator set is optimized for monoidal results. Apart from the
usual combinators `many` and `some`, for example, there are `concatMany` and `concatSome` operators.

```haskell
    many :: Parser s r -> Parser s [r]
    concatMany :: (Monoid s, Monoid r) => Parser s r -> Parser s r
```

#### Arbitrary monoidal inputs

The second weirdness, this one shared with [Picoparsec](http://hackage.haskell.org/package/picoparsec), is that the the
parser is generic in its input stream type, but this type is parameterized in a holistic way. There is no separate token
type. Primitive parsers that need to peek into the input require its type to be an instance of a monoid subclass, from
the [monoid-subclasses](http://hackage.haskell.org/package/monoid-subclasses) package.

In Parsec:

```haskell
    string :: Stream s m Char => String -> ParsecT s u m String
    char :: Stream s m Char => Char -> ParsecT s u m Char
    anyToken :: (Stream s m t, Show t) => ParsecT s u m t
```

In Attoparsec:

```haskell
    string :: ByteString -> Parser ByteString
    word8 :: Word8 -> Parser Word8
    anyWord8 :: Parser Word8
```

In incremental-parser and Picoparsec:

```haskell
    string :: (LeftCancellativeMonoid s, MonoidNull s) => s -> Parser s s
    token :: (Eq s, FactorialMonoid s) => s -> Parser s s
    anyToken :: FactorialMonoid s => Parser s s
```

#### Two `Alternative` alternatives

The library being implemented on the basis of Brzozowski derivatives, it can provide both the symmetric and the
left-biased choice, `<||>` and `<<|>`. This is the same design choice made by
[`Text.ParserCombinators.ReadP`](http://hackage.haskell.org/package/base/docs/Text-ParserCombinators-ReadP.html#g:2) and
[uu-parsinglib](http://hackage.haskell.org/package/uu-parsinglib). Parsec and its progeny on the other hand provide only
the faster left-biased choice, at some cost to the expressiveness of the combinator language. The standard `<|>`
operator from the `Alternative` class acts as one or the other of the above, depending on whether the first type
parameter of `Parser` is `Symmetric` or `LeftBiasedLocal`.

#### `MonadFix` and `record`

Finally, the parser is an instance of the `MonadFix` class. Beware of its power. In particular, never ever try to
`mfix` a strict function. This will hang. The argument of `mfix` takes the value constructed by the argument parser at
the very same input position it's looking at. The best and probably the only safe and useful argument to `mfix` is the
`record` function. See the [construct](https://hackage.haskell.org/package/construct) library for examples.
