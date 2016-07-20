# Change Log

## [Unreleased][unreleased]

### Changed

## 1.2.4 - 2016-07-20

### Thanks
- @Phlosioneer for documentation fixes
- @sourrust for fixing offsets in `take_bits!`
- @ChrisMacNaughton for the XFS crate
- @pwoolcoc for `rest_s`
- @fitzgen for more `IResult` methods
- @gtors for the negative lookahead feature
- @frk1 and @jeandudey for little endian float parsing
- @jethrogb for fixing input usage in `many1`
- @acatton for beating me at nom golf :D

### Added
- the `rest_s` method on `IResult` returns the remaining `&str` input
- `unwrap_err` and `unwrap_inc` methods on `IResult`
- `not!` will peek at the input and return `Done` if the underlying parser returned `Error` or `Incomplete`, without consuming the input
- `le_f32` and `le_f64` parse little endian floating point numbers (IEEE 754)
-

### Fixed
- documentation fixes
- `take_bits!` is now more precise
- `many1` inccorectly used the `len` function instead of `input_len`
- the INI parser is simpler
- `recognize!` had an early `return` taht is removed now

## 1.2.3 - 2016-05-10

### Thanks
- @lu-zero for the contribution guidelines
- @GuillaumeGomez for fixes on `length_bytes` and some documentation
- @Hywan for ducomentation and test fixes
- @Xirdus for correct trait import issues
- @mspiegel for the new AST example
- @cholcombe973 for adding the `cond_with_error!` combinator
- @tstorch for refactoring `many0!`
- @panicbit for the folding combinators
- @evestera for `separated_list!` fixes
- @DanielKeep for correcting some enum imports

### Added
- Regular expression combinators starting with `re_bytes_` work on byte slices
- example parsing arithmetic expressions to an AST
- `cond_with_error!` works like `cond!` but will return `None` if the condition is false, and `Some(value)` if the underlying parser succeeded
- `fold_many0!`, `fold_many1!` and `fold_many_m_n!` will take a parser, an initial value and a combining function, and fold over the successful applications of the parser

### Fixed
- `length_bytes!` converts the result of its child parser to usize
- `take_till!` now imports `InputLength` instead of assuming it's in scope
- `separated_list!` and `separated_nonempty_list!` will not consume the separator if there's no following successfully parsed value
- no more warnings on build

### Changed
- simpler implementation of `many0!`

## 1.2.2 - 2016-03-09

### Thanks
- @conradev for fixing take_until_s!`
- @GuillaumeGomez for some documentation fixes
- @frewsxcv for some documentation fixes
- @tstorch for some test refactorings

### Added
- `nom::Err` now implements `std::error::Error`

### Fixed
- `hex_u32` does not parses more than 8 chars now
- `take_while!` and `take_while1!` will not perturb the behaviour of `recognize!` anymore

## 1.2.1 - 2016-02-23

### Thanks
- @sourrust for adding methods to `IResult`
- @tstorch for the test refactoring, and for adding methods to `IResult` and `Needed`
- @joelself for fixing the method system

### Added

- mapping methods over `IResult` and `Needed`

### Changed

- `apply_rf` is renamed to `apply_m`. This will not warrant a major version, since it is part missing from the methods feture added in the 1.2.0 release
- the `regexp_macros` feature that used `regex!` to precompile regular expressions has been replaced by the normal regex engine combined with `lazy_static`

### Fixed

- when a parser or combinator was returning an empty buffer as remaining part, it was generating one from a static empty string. This was messing with buffer offset calculation. Now, that empty slice is taken like this: `&input[input.len()..]`.
- The `regexp_macros` and `no_std` feature build again and are now tested with Travis CI

## 1.2.0 - 2016-02-08

### Thanks
- @zentner-kyle for type inference fixes
- @joelself for his work on `&str` parsing and method parsers
- @GuillaumeGomez for implementing methods on `IResult`
- @dirk for the `alt_complete!` combinator
- @tstorch for a lot of refactoring work and unit tests additions
- @jansegre for the hex digit parsers
- @belgum for some documentation fixes
- @lwandrebeck for some documentation fixes and code fixes in `hex_digit`

### Added
- `take_until_and_consume_s!` for consumption of string data until a tag
- more function patterns in `named!`. The error type can now be specified
- `alt_complete!` works like the `alt!` combinator, but tries the next branch if the current one returned `Incomplete`, instead of returning directly
- more unit tests for a lot of combinators
- hexadecimal digit parsers
- the `tuple!` combinator takes a list of parsers as argument, and applies them serially on the input. If all of them are successful, it willr eturn a tuple accumulating all the values. This combinator will (hopefully) replace most uses of `chain!`
- parsers can now be implemented as a method for a struct thanks to the `method!`, `call_m!` and `apply_rf!` combinators

### Fixed
- there were type inference issues in a few combinators. They will now be easier to compile
- `peek!` compilation with bare functions
- `&str` parsers were splitting data at the byte level, not at the char level, which can result in inconsistencies in parsing UTF-8 characters. They now use character indexes
- some method implementations were missing on `ÌResult<I,O,E>` (with specified error type instead of implicit)

## 1.1.0 - 2016-01-01

This release adds a lot of features related to `&str` parsing. The previous versions
were focused on `&[u8]` and bit streams parsing, but there's a need for more text
parsing with nom. The parsing functions like `alpha`, `digit` and others will now
accept either a `&[u8]` or a `&str`, so there is no breaking change on that part.

There are also a few performance improvements and documentation fixes.

### Thanks
- @Binero for pushing the work on `&str` parsing
- @meh for fixing `Option` and `Vec` imports
- @hoodie for a documentation fix
- @joelself for some documentation fixes
- @vberger for his traits magic making `nom functions more generic

### Added

- string related parsers: `tag_s!`, `take_s!`, `is_a_s!`, `is_not_s!`, `take_while_s!`, `take_while1_s!`, `take_till_s!
- `value!` is a combinator that always returns the same value. If a child parser is passed as second argument, that value is returned when the child parser succeeds

### Changed

- `tag!` will now compare even on partial input. If it expects "abcd" but receives "ef", it will now return an `Error` instead of `Incomplete`
- `many0!` and others will preallocate a larger vector to avoid some copies and reallocations
- `alpha`, `digit`, `alphanumeric`, `space` and `multispace` now accept as input a `&[u8]` or a `&str`. Additionally, they return an error if they receive an empty input
- `take_while!`, `take_while1!`, `take_while_s!`, `take_while1_s!` wilreturn an error on empty input

### Fixed

- if the child parser of `many0!` or `many1!` returns `Incomplete`, it will return `Incomplete` too, possibly updating the needed size
- `Option,` `Some`, `None` and `Vec` are now used with full path imports

## 1.0.1 - 2015-11-22

This releases makes the 1.0 version compatible with Rust 1.2 and 1.3

### Thanks
- @steveklabnik for fixing lifetime issues in Producers and Consumers

## 1.0.0 - 2015-11-16

Stable release for nom. A lot of new features, a few breaking changes

### Thanks
- @ahenry for macro fixes
- @bluss for fixing documentation
- @sourrust for cleaning code and debugging the new streaming utilities
- @meh for inline optimizations
- @ccmtaylor for fixing function imports
- @soro for improvements to the streaming utilities
- @breard-r for catching my typos
- @nelsonjchen for catching my typos too
- @divarvel for hex string parsers
- @mrordinaire for the `length_bytes!` combinator

### Breaking changes
- `IResult::Error` can now use custom error types, and is generic over the input type
- Producers and consumers have been replaced. The new implementation uses less memory and integrates more with parsers
- `nom::ErrorCode` is now `nom::ErrorKind`
- `filter!` has been renamed to `take_while!`
- `chain!` will count how much data is consumed and use that number to calculate how much data is needed if a parser returned `Incomplete`
- `alt!` returns `Incomplete` if a child parser returned `Incomplete`, instead of skipping to the next parser
- `IResult` does not require a lifetime tag anymore, yay!

### Added

- `complete!` will return an error if the child parser returned `Incomplete`
- `add_error!` will wrap an error, but allow backtracking
- `hex_u32` parser

### Fixed
- the behaviour around `Incomplete` is better for most parsers now

## 0.5.0 - 2015-10-16

This release fixes a few issues and stabilizes the code.

### Thanks
- @nox for documentation fixes
- @daboross for linting fixes
- @ahenry for fixing `tap!` and extending `dbg!` and `dbg_dmp!`
- @bluss for tracking down and fixing issues with unsafe code
- @meh for inlining parser functions
- @ccmtaylor for fixing import of `str::from_utf8`

### Fixed
- `tap!`, `dbg!` and `dbg_dmp!` now accept function parameters

### Changed
- the type used in `count_fixed!` must be `Copy`
- `chain!` calculates how much data is needed if one of the parsers returns `Incomplete
- optional parsers in `chain!` can return `Incomplete`

## 0.4.0 - 2015-09-08

Considering the number of changes since the last release, this version can contain breaking changes, so the version number becomes 0.4.0. A lot of new features and performance improvements!

### Thanks
- @frewsxcv for documentation fixes
- @ngrewe for his work on producers and consumers
- @meh for fixes on `chain!` and for the `rest` parser
- @daboross for refactoring `many0!` and `many1!`
- @aleksander for the `switch!` combinator idea
- @TechnoMancer for his help with bit level parsing
- @sxeraverx for pointing out a bug in `is_a!`

### Fixed
- `count_fixed!` must take an explicit type as argument to generate the fixed-size array
- optional parsing behaviour in `chain!`
- `count!` can take 0 elements
- `is_a!` and `is_not!` can now consume the whole input

### Added
- it is now possible to seek to the end of a `MemProducer`
- `opt!` returns `Done(input, None)` if `the child parser returned `Incomplete`
- `rest` will return the remaining input
- consumers can now seek to and from the end of input
- `switch!` applies a first parser then matches on its result to choose the next parser
- bit-level parsers
- character-level parsers
- regular expression parsers
- implementation of `take_till!`, `take_while!` and `take_while1!`

### Changed
- `alt!` can return `Incomplete`
- the error analysis functions will now take references to functions instead of moving them
- performance improvements on producers
- performance improvement for `filter!`
- performance improvement for `count!`: a `Vec` of the right size is directly allocated

## 0.3.11 - 2015-08-04

### Thanks
- @bluss for remarking that the crate included random junk lying non commited in my local repository

### Fixed
- cleanup of my local repository will ship less files in the crates, resulting in a smaller download

## 0.3.10 - 2015-08-03

### Added

- `bits!` for bit level parsing. It indicates that all child parsers will take a `(&[u8], usize)`as input, with the second parameter indicating the bit offset in the first byte. This allows viewing a byte slice as a bit stream. Most combinators can be used directly under `bits!`
- `take_bits!` takes an integer type and a number of bits, consumes that number of bits and updates the offset, possibly by crossing byte boundaries
- bit level parsers are all written in `src/bits.rs`

### Changed

- Parsers that specifically handle bytes have been moved to src/bytes.rs`. This applies to `tag!`, `is_not!`, `is_a!`, `filter!`, `take!`, `take_str!`, `take_until_and_consume!`, `take_until!`, `take_until_either_and_consume!`, `take_until_either!`

## 0.3.9 - 2015-07-20

### Thanks
- @badboy for fixing `filter!`
- @idmit for some documentation fixes

### Added
- `opt_res!` applies a parser and transform its result in a Result. This parser never fails
- `cond_reduce!` takes an expression as parameter, applies the parser if the expression is true, and returns an error if the expression is false
- `tap!` pass the result of a parser to a block to manipulate it, but do not affect the parser's result
- `AccReader` is a Read+BufRead that supports data accumulation and partial consumption. The `consume` method must be called afterwardsto indicate how much was consumed
- Arithmetic expression evaluation and parsing example
- `u16!`, `u32!`, `u64!`, `i16!`, `i32!`, `i64!` take an expression as parameter, if the expression is true, apply the big endian integer parser, if false, the little endian version
- type information for combinators. This will make the documentation a bit easier to navigate

### Fixed
- `map_opt!` and `map_res!` had issues with argument order due to bad macros
- `delimited!` did not compile for certain combinations of arguments
- `filter!` did not return a byte slice but a fixed array

## 0.3.8 - 2015-07-03

### Added
- code coverage is now calculated automatically on Travis CI
- `Stepper`: wrap a `Producer`, and call the method `step` with a parser. This method will buffer data if there is not enough, apply the parser if there is, and keep the rest of the input in memory for the next call
- `ReadProducer`: takes something implementing `Read`, and makes a `Producer` out of it

### Fixed
- the combinators `separated_pair!` and `delimited!` did not work because an implementation macro was not exported
- if a `MemProducer` reached its end, it should always return `Eof`
- `map!` had issues with argument matching

## 0.3.7 - 2015-06-24

### Added
- `expr_res!` and `expr_opt!` evaluate an expression returning a Result or Opt and convert it to IResult
- `AsBytes` is implemented for fixed size arrays. This allows `tag!([41u8, 42u8])`

### Fixed
- `count_fixed!` argument parsing works again

## 0.3.6 - 2015-06-15

### Added
- documentation for a few functions
- the consumer trait now requires the `failed(&self, error_code)` method in case of parsing error
- `named!` now handles thge alternative `named!(pub fun_name<OutputType>, ...)`

### Fixed
- `filter!` now returns the whole input if the filter function never returned false
- `take!` casts its argument as usize, so it can accepts any integer type now

## 0.3.5 - 2015-06-10

### Thanks
- @cmr for some documentation fixes

### Added
- `count_fixed!` returns a fixed array

### Fixed
- `count!` is back to the previous behaviour, returning a `Vec` for sizes known at runtime

### Changed
- functions and traits exported from `nom::util` are now directly in `nom::`

## 0.3.4 - 2015-06-09

### Thanks
- @andrew-d for fixes on `cond!`
- @keruspe for features in `chain!`

### Added
- `chain!` can now have mutable fields

### Fixed
- `cond!` had an infinite macro recursion

### Changed
- `chain!` generates less code now. No apprent compilation time improvement

## 0.3.3 - 2015-06-09

### Thanks
- @andrew-d for the little endian signed integer parsers
- @keruspe for fixes on `count!`

### Added
- `le_i8`, `le_i16`, `le_i32`, `le_i64`: little endian signed integer parsers

### Changed
- the `alt!` parser compiles much faster, even with more than 8 branches
- `count!` can now return a fixed size array instead of a growable vector

## 0.3.2 - 2015-05-31

### Thanks
- @keruspe for the `take_str` parser and the function application combinator

### Added
- `take_str!`: takes the specified number of bytes and return a UTF-8 string
- `apply!`: do partial application on the parameters of a function

### Changed
- `Needed::Size` now contains a `usize` instead of a `u32`

## 0.3.1 - 2015-05-21

### Thanks
- @divarvel for the big endian signed integer parsers

### Added
- `be_i8`, `be_i16`, `be_i32`, `be_i64`: big endian signed integer parsers
- the `core` feature can be passed to cargo to build with `no_std`
- colored hexdump can be generated from error chains

## 0.3.0 - 2015-05-07

### Thanks
- @filipegoncalves for some documentation and the new eof parser
- @CrimsonVoid for putting fully qualified types in the macros
- @lu_zero for some documentation fixes

### Added
- new error types that can contain an error code, an input slice, and a list of following errors
- `error!` will cut backtracking and return directly from the parser, with a specified error code
- `eof` parser, successful if there is no more input
- specific error codes for the parsers provided by nom

### Changed
- fully qualified types in macros. A lot of imports are not needed anymore

### Removed
- `FlatMap`, `FlatpMapOpt` and `Functor` traits (replaced by `map!`, `map_opt!` and `map_res!`)

## 0.2.2 - 2015-04-12

### Thanks
- @filipegoncalves and @thehydroimpulse for debugging an infinite loop in many0 and many1
- @thehydroimpulse for suggesting public named parsers
- @skade for removing the dependency on the collections gate

### Added
- `named!` can now declare public functions like this: `named!(pub tst, tag!("abcd"));`
- `pair!(X,Y)` returns a tuple `(x, y)`
- `separated_pair!(X, sep, Y)` returns a tuple `(x, y)`
- `preceded!(opening, X)` returns `x`
- `terminated!(X, closing)` returns `x`
- `delimited(opening, X, closing)` returns `x`
- `separated_list(sep, X)` returns a `Vec<X>`
- `separated_nonempty_list(sep, X)` returns a `Vec<X>` of at list one element

### Changed
- `many0!` and `many1!` forbid parsers that do not consume input
- `is_a!`, `is_not!`, `alpha`, `digit`, `space`, `multispace` will now return an error if they do not consume at least one byte

## 0.2.1 - 2015-04-04

### Thanks
- @mtsr for catching the remaining debug println!
- @jag426 who killed a lot of warnings
- @skade for removing the dependency on the core feature gate


### Added
- little endian unsigned int parsers le_u8, le_u16, le_u32, le_u64
- `count!` to apply a parser a specified number of times
- `cond!` applies a parser if the condition is met
- more parser development tools in `util::*`

### Fixed
- in one case, `opt!` would not compile

### Removed
- most of the feature gates are now removed. The only one still needed is `collections`

## 0.2.0 - 2015-03-24
*works with `rustc 1.0.0-dev (81e2396c7 2015-03-19) (built 2015-03-19)`*

### Thanks
- Ryman for the AsBytes implementation
- jag426 and jaredly for documentation fixes
- eternaleye on #rust IRC for his help on the new macro syntax

### Changed
- the AsBytes trait improves readability, no more b"...", but "..." instead
- Incomplete will now hold either Needed;;Unknown, or Needed::Size(u32). Matching on Incomplete without caring for the value is done with `Incomplete(_)`, but if more granularity is mandatory, `Needed` can be matched too
- `alt!` can pass the result of the parser to a closure
- the `take_*` macros changed behaviour, the default case is now not to consume the separator. The macros have been renamed as follows: `take_until!` -> `take_until_and_consume!`, `take_until_and_leave!` -> `take_until!`, `take_until_either_and_leave!` -> `take_until_either!`, `take_until_either!` -> `take_until_either_and_consume!`

### Added
- `peek!` macro: matches the future input but does not consume it
- `length_value!` macro: the first argument is a parser returning a `n` that can cast to usize, then applies the second parser `n` times. The macro has a variant with a third argument indicating the expected input size for the second parser
- benchmarks are available at https://github.com/Geal/nom_benchmarks
- more documentation
- **Unnamed parser syntax**: warning, this is a breaking change. With this new syntax, the macro combinators do not generate functions anymore, they create blocks. That way, they can be nested, for better readability. The `named!` macro is provided to create functions from parsers. Please be aware that nesting parsers comes with a small cost of compilation time, negligible in most cases, but can quickly get to the minutes scale if not careful. If this happens, separate your parsers in multiple subfunctions.
- `named!`, `closure!` and `call!` macros used to support the unnamed syntax
- `map!`, `map_opt!` and `map_res!` to combine a parser with a normal function, transforming the input directly, or returning an `Option` or `Result`

### Fixed
- `is_a!` is now working properly

### Removed
- the `o!` macro does less than `chain!`, so it has been removed
- the `fold0!` and `fold1!` macros were too complex and awkward to use, the `many*` combinators will be useful for most uses for now

## 0.1.6 - 2015-02-24
### Changed
- consumers must have an end method that will be called after parsing

### Added
- big endian unsigned int and float parsers: be_u8, be_u16, be_u32, be_u64, be_f32, be_f64
- producers can seek
- function and macros documentation
- README documentation
### Fixed
- lifetime declarations
- tag! can return Incomplete

## 0.1.5 - 2015-02-17
### Changed
- traits were renamed: FlatMapper -> FlatMap, Mapper -> FlatMapOpt, Mapper2 -> Functor

### Fixed
- woeks with rustc f1bb6c2f4

## 0.1.4 - 2015-02-17
### Changed
- the chaining macro can take optional arguments with '?'

## 0.1.3 - 2015-02-16
### Changed
- the chaining macro now takes the closure at the end of the argument list

## 0.1.2 - 2015-02-16
### Added
- flat_map implementation for <&[u8], &[u8]>
- chaining macro
- partial MP4 parser example


## 0.1.1 - 2015-02-06
### Fixed
- closure syntax change

## Compare code

* [unreleased]: https://github.com/Geal/nom/compare/1.2.4...HEAD
* [1.2.3]: https://github.com/Geal/nom/compare/1.2.3...1.2.4
* [1.2.3]: https://github.com/Geal/nom/compare/1.2.2...1.2.3
* [1.2.2]: https://github.com/Geal/nom/compare/1.2.1...1.2.2
* [1.2.1]: https://github.com/Geal/nom/compare/1.2.0...1.2.1
* [1.2.0]: https://github.com/Geal/nom/compare/1.1.0...1.2.0
* [1.1.0]: https://github.com/Geal/nom/compare/1.0.1...1.1.0
* [1.0.1]: https://github.com/Geal/nom/compare/1.0.0...1.0.1
* [1.0.0]: https://github.com/Geal/nom/compare/0.5.0...1.0.0
* [0.5.0]: https://github.com/geal/nom/compare/0.4.0...0.5.0
* [0.4.0]: https://github.com/geal/nom/compare/0.3.11...0.4.0
* [0.3.11]: https://github.com/geal/nom/compare/0.3.10...0.3.11
* [0.3.10]: https://github.com/geal/nom/compare/0.3.9...0.3.10
* [0.3.9]: https://github.com/geal/nom/compare/0.3.8...0.3.9
* [0.3.8]: https://github.com/Geal/nom/compare/0.3.7...0.3.8
* [0.3.7]: https://github.com/Geal/nom/compare/0.3.6...0.3.7
* [0.3.6]: https://github.com/Geal/nom/compare/0.3.5...0.3.6
* [0.3.5]: https://github.com/Geal/nom/compare/0.3.4...0.3.5
* [0.3.4]: https://github.com/Geal/nom/compare/0.3.3...0.3.4
* [0.3.3]: https://github.com/Geal/nom/compare/0.3.2...0.3.3
* [0.3.2]: https://github.com/Geal/nom/compare/0.3.1...0.3.2
* [0.3.1]: https://github.com/Geal/nom/compare/0.3.0...0.3.1
* [0.3.0]: https://github.com/Geal/nom/compare/0.2.2...0.3.0
* [0.2.2]: https://github.com/Geal/nom/compare/0.2.1...0.2.2
* [0.2.1]: https://github.com/Geal/nom/compare/0.2.0...0.2.1
* [0.2.0]: https://github.com/Geal/nom/compare/0.1.6...0.2.0
* [0.1.6]: https://github.com/Geal/nom/compare/0.1.5...0.1.6
* [0.1.5]: https://github.com/Geal/nom/compare/0.1.4...0.1.5
* [0.1.4]: https://github.com/Geal/nom/compare/0.1.3...0.1.4
* [0.1.3]: https://github.com/Geal/nom/compare/0.1.2...0.1.3
* [0.1.2]: https://github.com/Geal/nom/compare/0.1.1...0.1.2
* [0.1.1]: https://github.com/Geal/nom/compare/0.1.0...0.1.1
