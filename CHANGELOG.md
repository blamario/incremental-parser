# Revision history for incremental-parser

## 0.5.1 -- 2023-12-19

* Replaced the ListT transformer with LogicT
* Bumped dependency bounds
* Fixed some compiler warnings

## 0.5.0.5 -- 2023-04-09

* Allow `monoid-subclasses-1.2` and `rank2classes-1.5`, thanks to felixonmars

## 0.5.0.4 -- 2022-10-03

* Incremented dependency versions.

## 0.5.0.3 -- 2022-03-09

* Allow `checkers-0.6`

## 0.5.0.2 -- 2021-03-07

* Incremented `monoid-subclasses` and `input-parsers` upper bounds

## 0.5.0.1 -- 2020-12-25

* Incremented the `tasty` dependency version bounds

## 0.5 -- 2020-07-18

* Fixed the `take` method implementation
* Added the `DeterministicParsing` instance
* Cleaned up the comments and warnings
* Added the `InputCharParsing` instance
* Added the `InputParsing` instance

## 0.4.0.2 -- 2020-05-10

* Bumped up the upper dependency bound for `tasty`

## 0.4.0.1 -- 2020-03-08

* Relax bound of `rank2classes` to < 1.5, thanks to felixonmars

## 0.4 -- 2020-01-21

* Improved error reporting
* Changed the result type of inspect to report the error message
* Added the missing `Choice` in `ResultStructure` case, eliminated all warnings except `ListT`
* Generalized the `CharParsing` instance
* Added `mapInput` and `mapInput'`
* Preserve the input left after `ResultStructure`
* Generalized `ResultStructure` off `Identity`
* Eta-reduced the `Parser` type synonyms
* Added `ResultStructure` and the record combinator
* Moved the source code into the `src/` directory
* Added instances for `MonoidFix` and `*Parsing` classes

## 0.3.3 -- 2019-10-10

* Updated for `monoid-subclasses-1.0`

## 0.3.2.2 -- 2019-03-30

* Bumped the `checkers` dependency version bound
* Fixed a bug in the ordering of incremental results

## 0.3.2.1 -- 2019-12-03

* Incremented the upper bound for `tasty`

## 0.3.2 -- 2018-10-14

* Added `MonadFail` instance

## 0.3.1.1 -- 2018-05-12

* Incremented the tasty upper bound
* Fixed compilation with GHC 8.2

## 0.3.1 -- 2018-04-26

* Building with GHC-8.4 and `Semigroup`
* Limited the `base` upper bound

## 0.2.5.3 -- 2018-01-09

* Incremented the upper bound for `tasty`
