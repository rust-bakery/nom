# Change Log

## [Unreleased][unreleased]

### Changed

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

[unreleased]: https://github.com/Geal/nom/compare/0.3.0...HEAD
[0.3.0]: https://github.com/Geal/nom/compare/0.2.2...0.3.0
[0.2.2]: https://github.com/Geal/nom/compare/0.2.1...0.2.2
[0.2.1]: https://github.com/Geal/nom/compare/0.2.0...0.2.1
[0.2.0]: https://github.com/Geal/nom/compare/0.1.6...0.2.0
[0.1.6]: https://github.com/Geal/nom/compare/0.1.5...0.1.6
[0.1.5]: https://github.com/Geal/nom/compare/0.1.4...0.1.5
[0.1.4]: https://github.com/Geal/nom/compare/0.1.3...0.1.4
[0.1.3]: https://github.com/Geal/nom/compare/0.1.2...0.1.3
[0.1.2]: https://github.com/Geal/nom/compare/0.1.1...0.1.2
[0.1.1]: https://github.com/Geal/nom/compare/0.1.0...0.1.1
