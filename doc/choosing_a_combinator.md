# List of parsers and combinators

**Note**: this list is meant to provide a nicer way to find a nom parser than reading through the documentation on docs.rs. Function combinators are organized in module so they are a bit easier to find.

Links present in this document will nearly always point to `complete` version of the parser. Most of the parsers also have a `streaming` version.

## Basic elements

Those are used to recognize the lowest level elements of your grammar, like, "here is a dot", or "here is an big endian integer".

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [char](crate::character::complete::char) | `char('a')` |  `"abc"` | `Ok(("bc", 'a'))` |Matches one character (works with non ASCII chars too) | 
| [is_a](crate::bytes::complete::is_a) | `is_a("ab")` |  `"abbac"` | `Ok(("c", "abba"))` |Matches a sequence of any of the characters passed as arguments|
| [is_not](crate::bytes::complete::is_not) | `is_not("cd")` |  `"ababc"` | `Ok(("c", "abab"))` |Matches a sequence of none of the characters passed as arguments|
| [one_of](crate::character::complete::one_of) | `one_of("abc")` |  `"abc"` | `Ok(("bc", 'a'))` |Matches one of the provided characters (works with non ASCII characters too)|
| [none_of](crate::character::complete::none_of) | `none_of("abc")` |  `"xyab"` | `Ok(("yab", 'x'))` |Matches anything but the provided characters|
| [tag](crate::bytes::complete::tag) | `tag("hello")` |  `"hello world"` | `Ok((" world", "hello"))` |Recognizes a specific suite of characters or bytes|
| [tag_no_case](crate::bytes::complete::tag_no_case) | `tag_no_case("hello")` |  `"HeLLo World"` | `Ok((" World", "HeLLo"))` |Case insensitive comparison. Note that case insensitive comparison is not well defined for unicode, and that you might have bad surprises|
| [take](crate::bytes::complete::take) | `take(4)` |  `"hello"` | `Ok(("o", "hell"))` |Takes a specific number of bytes or characters|
| [take_while](crate::bytes::complete::take_while) | `take_while(is_alphabetic)` |  `"abc123"` | `Ok(("123", "abc"))` |Returns the longest list of bytes for which the provided function returns true. `take_while1` does the same, but must return at least one character, while `take_while_m_n` must return between m and n|
| [take_till](crate::bytes::complete::take_till) | `take_till(is_alphabetic)` |  `"123abc"` | `Ok(("abc", "123"))` |Returns the longest list of bytes or characters until the provided function returns true. `take_till1` does the same, but must return at least one character. This is the reverse behaviour from `take_while`: `take_till(f)` is equivalent to `take_while(\|c\| !f(c))`|
| [take_until](crate::bytes::complete::take_until) | `take_until("world")` |  `"Hello world"` | `Ok(("world", "Hello "))` |Returns the longest list of bytes or characters until the provided tag is found. `take_until1` does the same, but must return at least one character|

## Choice combinators

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [alt](crate::branch::alt) | `alt((tag("ab"), tag("cd")))` |  `"cdef"` | `Ok(("ef", "cd"))` |Try a list of parsers and return the result of the first successful one|
| [permutation](crate::branch::permutation) | `permutation((tag("ab"), tag("cd"), tag("12")))` | `"cd12abc"` | `Ok(("c", ("ab", "cd", "12"))` |Succeeds when all its child parser have succeeded, whatever the order|

## Sequence combinators

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [delimited](crate::sequence::delimited) | `delimited(char('('), take(2), char(')'))` | `"(ab)cd"` | `Ok(("cd", "ab"))` |Matches an object from the first parser and discards it, then gets an object from the second parser, and finally matches an object from the third parser and discards it.|
| [preceded](crate::sequence::preceded) | `preceded(tag("ab"), tag("XY"))` | `"abXYZ"` | `Ok(("Z", "XY"))` |Matches an object from the first parser and discards it, then gets an object from the second parser.|
| [terminated](crate::sequence::terminated) | `terminated(tag("ab"), tag("XY"))` | `"abXYZ"` | `Ok(("Z", "ab"))` |Gets an object from the first parser, then matches an object from the second parser and discards it.|
| [pair](crate::sequence::pair) | `pair(tag("ab"), tag("XY"))` | `"abXYZ"` | `Ok(("Z", ("ab", "XY")))` |Gets an object from the first parser, then gets another object from the second parser.|
| [separated_pair](crate::sequence::separated_pair) | `separated_pair(tag("hello"), char(','), tag("world"))` | `"hello,world!"` | `Ok(("!", ("hello", "world")))` |Gets an object from the first parser, then matches an object from the sep_parser and discards it, then gets another object from the second parser.|
| [tuple](crate::sequence::tuple) | `tuple((tag("ab"), tag("XY"), take(1)))` | `"abXYZ!"` | `Ok(("!", ("ab", "XY", "Z")))` | Chains parsers and assemble the sub results in a tuple. You can use as many child parsers as you can put elements in a tuple|

## Applying a parser multiple times

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [count](crate::multi::count) | `count(take(2), 3)` | `"abcdefgh"` | `Ok(("gh", vec!["ab", "cd", "ef"]))` |Applies the child parser a specified number of times|
| [many0](crate::multi::many0) | `many0(tag("ab"))` |  `"abababc"` | `Ok(("c", vec!["ab", "ab", "ab"]))` |Applies the parser 0 or more times and returns the list of results in a Vec. `many1` does the same operation but must return at least one element|
| [many0_count](crate::multi::many0_count) | `many0_count(tag("ab"))` | `"abababc"` | `Ok(("c", 3))` |Applies the parser 0 or more times and returns how often it was applicable. `many1_count` does the same operation but the parser must apply at least once|
| [many_m_n](crate::multi::many_m_n) | `many_m_n(1, 3, tag("ab"))` | `"ababc"` | `Ok(("c", vec!["ab", "ab"]))` |Applies the parser between m and n times (n included) and returns the list of results in a Vec|
| [many_till](crate::multi::many_till) | `many_till(tag( "ab" ), tag( "ef" ))` | `"ababefg"` | `Ok(("g", (vec!["ab", "ab"], "ef")))` |Applies the first parser until the second applies. Returns a tuple containing the list of results from the first in a Vec and the result of the second|
| [separated_list0](crate::multi::separated_list0) | `separated_list0(tag(","), tag("ab"))` | `"ab,ab,ab."` | `Ok((".", vec!["ab", "ab", "ab"]))` |`separated_list1` works like `separated_list0` but must returns at least one element|
| [fold_many0](crate::multi::fold_many0) | `fold_many0(be_u8, ::|\| 0, \|acc, item\| acc + item)` | `[1, 2, 3]` | `Ok(([], 6))` |Applies the parser 0 or more times and folds the list of return values. The `fold_many1` version must apply the child parser at least one time|
| [fold_many_m_n](crate::multi::fold_many_m_n) | `fold_many_m_n(1, 2, be_u8, ::|\| 0, \|acc, item\| acc + item)` | `[1, 2, 3]` | `Ok(([3], 3))` |Applies the parser between m and n times (n included) and folds the list of return value|
| [length_count](crate::multi::length_count) | `length_count(number, tag("ab"))` | `"2ababab"` | `Ok(("ab", vec!["ab", "ab"]))` |Gets a number from the first parser, then applies the second parser that many times|

## Integers

Parsing integers from binary formats can be done in two ways: With parser functions, or combinators with configurable endianness.

The following parsers could be found on [docs.rs number section](https://docs.rs/nom/latest/nom/number/complete/index.html).

- **configurable endianness:** [`i16`](crate::number::complete::i16), [`i32`](crate::number::complete::i32), [`i64`](crate::number::complete::i64), [`u16`](crate::number::complete::u16), [`u32`](crate::number::complete::u32), [`u64`](crate::number::complete::u64) are combinators that take as argument a [`nom::number::Endianness`](crate::number::Endianness), like this: `i16(endianness)`. If the parameter is `nom::number::Endianness::Big`, parse a big endian `i16` integer, otherwise a little endian `i16` integer.
- **fixed endianness**: The functions are prefixed by `be_` for big endian numbers, and by `le_` for little endian numbers, and the suffix is the type they parse to. As an example, `be_u32` parses a big endian unsigned integer stored in 32 bits.
  - [`be_f32`](crate::number::complete::be_f32), [`be_f64`](crate::number::complete::be_f64): Big endian floating point numbers
  - [`le_f32`](crate::number::complete::le_f32), [`le_f64`](crate::number::complete::le_f64): Little endian floating point numbers
  - [`be_i8`](crate::number::complete::be_i8), [`be_i16`](crate::number::complete::be_i16), [`be_i24`](crate::number::complete::be_i24), [`be_i32`](crate::number::complete::be_i32), [`be_i64`](crate::number::complete::be_i64), [`be_i128`](crate::number::complete::be_i128): Big endian signed integers
  - [`be_u8`](crate::number::complete::be_u8), [`be_u16`](crate::number::complete::be_u16), [`be_u24`](crate::number::complete::be_u24), [`be_u32`](crate::number::complete::be_u32), [`be_u64`](crate::number::complete::be_u64), [`be_u128`](crate::number::complete::be_u128): Big endian unsigned integers
  - [`le_i8`](crate::number::complete::le_i8), [`le_i16`](crate::number::complete::le_i16), [`le_i24`](crate::number::complete::le_i24), [`le_i32`](crate::number::complete::le_i32), [`le_i64`](crate::number::complete::le_i64), [`le_i128`](crate::number::complete::le_i128): Little endian signed integers
  - [`le_u8`](crate::number::complete::le_u8), [`le_u16`](crate::number::complete::le_u16), [`le_u24`](crate::number::complete::le_u24), [`le_u32`](crate::number::complete::le_u32), [`le_u64`](crate::number::complete::le_u64), [`le_u128`](crate::number::complete::le_u128): Little endian unsigned integers

## Streaming related

- [`eof`](crate::combinator::eof): Returns its input if it is at the end of input data
- [`complete`](crate::combinator::complete): Replaces an `Incomplete` returned by the child parser with an `Error`

## Modifiers


- [`Parser::and`](https://docs.rs/nom/latest/nom/trait.Parser.html#method.and): method to create a parser by applying the supplied parser to the rest of the input after applying `self`, returning their results as a tuple (like `sequence::tuple` but only takes one parser)
- [`Parser::and_then`](https://docs.rs/nom/latest/nom/trait.Parser.html#method.and_then): method to create a parser from applying another parser to the output of `self`
- [`map_parser`](crate::combinator::map_parser): function variant of `Parser::and_then`
- [`Parser::map`](https://docs.rs/nom/latest/nom/trait.Parser.html#method.map): method to map a function on the output of `self`
- [`map`](crate::combinator::map): function variant of `Parser::map`
- [`Parser::flat_map`](https://docs.rs/nom/latest/nom/trait.Parser.html#method.flat_map): method to create a parser which will map a parser returning function (such as `take` or something which returns a parser) on the output of `self`, then apply that parser over the rest of the input. That is, this method accepts a parser-returning function which consumes the output of `self`, the resulting parser gets applied to the rest of the input
- [`flat_map`](crate::combinator::flat_map): function variant of `Parser::flat_map`
- [`cond`](crate::combinator::cond): Conditional combinator. Wraps another parser and calls it if the condition is met
- [`map_opt`](crate::combinator::map_opt): Maps a function returning an `Option` on the output of a parser
- [`map_res`](crate::combinator::map_res): Maps a function returning a `Result` on the output of a parser
- [`into`](crate::combinator::into): Converts the child parser's result to another type
- [`not`](crate::combinator::not): Returns a result only if the embedded parser returns `Error` or `Incomplete`. Does not consume the input
- [`opt`](crate::combinator::opt): Make the underlying parser optional
- [`cut`](crate::combinator::cut): Transform recoverable error into unrecoverable failure (commitment to current branch)
- [`peek`](crate::combinator::peek): Returns a result without consuming the input
- [`recognize`](crate::combinator::recognize): If the child parser was successful, return the consumed input as the produced value
- [`consumed`](crate::combinator::consumed): If the child parser was successful, return a tuple of the consumed input and the produced output.
- [`verify`](crate::combinator::verify): Returns the result of the child parser if it satisfies a verification function
- [`value`](crate::combinator::value): Returns a provided value if the child parser was successful
- [`all_consuming`](crate::combinator::all_consuming): Returns the result of the child parser only if it consumed all the input

## Error management and debugging

- [`dbg_dmp`](crate::dbg_dmp): Prints a message and the input if the parser fails

## Text parsing

- [`escaped`](crate::bytes::complete::escaped): Matches a byte string with escaped characters
- [`escaped_transform`](crate::bytes::complete::escaped_transform): Matches a byte string with escaped characters, and returns a new string with the escaped characters replaced
- [`precedence`](crate::precedence::precedence): Parses an expression with regards to operator precedence

## Binary format parsing

- [`length_data`](crate::multi::length_data): Gets a number from the first parser, then takes a subslice of the input of that size, and returns that subslice
- [`length_value`](crate::multi::length_value): Gets a number from the first parser, takes a subslice of the input of that size, then applies the second parser on that subslice. If the second parser returns `Incomplete`, `length_value` will return an error

## Bit stream parsing

- [`bits`](crate::bits::bits): Transforms the current input type (byte slice `&[u8]`) to a bit stream on which bit specific parsers and more general combinators can be applied
- [`bytes`](crate::bits::bytes): Transforms its bits stream input back into a byte slice for the underlying parser

## Remaining combinators

- [`success`](crate::combinator::success): Returns a value without consuming any input, always succeeds
- [`fail`](crate::combinator::fail): Inversion of `success`. Always fails.

## Character test functions

Use these functions with a combinator like `take_while`:

- [`is_alphabetic`](crate::character::is_alphabetic): Tests if byte is ASCII alphabetic: `[A-Za-z]`
- [`is_alphanumeric`](crate::character::is_alphanumeric): Tests if byte is ASCII alphanumeric: `[A-Za-z0-9]`
- [`is_digit`](crate::character::is_digit): Tests if byte is ASCII digit: `[0-9]`
- [`is_hex_digit`](crate::character::is_hex_digit): Tests if byte is ASCII hex digit: `[0-9A-Fa-f]`
- [`is_oct_digit`](crate::character::is_oct_digit): Tests if byte is ASCII octal digit: `[0-7]`
- [`is_bin_digit`](crate::character::is_bin_digit): Tests if byte is ASCII binary digit: `[0-1]`
- [`is_space`](crate::character::is_space): Tests if byte is ASCII space or tab: `[ \t]`
- [`is_newline`](crate::character::is_newline): Tests if byte is ASCII newline: `[\n]`

Alternatively there are ready to use functions:

- [`alpha0`](crate::character::complete::alpha0): Recognizes zero or more lowercase and uppercase alphabetic characters: `[a-zA-Z]`. [`alpha1`](crate::character::complete::alpha1) does the same but returns at least one character
- [`alphanumeric0`](crate::character::complete::alphanumeric0): Recognizes zero or more numerical and alphabetic characters: `[0-9a-zA-Z]`. [`alphanumeric1`](crate::character::complete::alphanumeric1) does the same but returns at least one character
- [`anychar`](crate::character::complete::anychar): Matches one byte as a character
- [`crlf`](crate::character::complete::crlf): Recognizes the string `\r\n`
- [`digit0`](crate::character::complete::digit0): Recognizes zero or more numerical characters: `[0-9]`. [`digit1`](crate::character::complete::digit1) does the same but returns at least one character
- [`double`](crate::number::complete::double): Recognizes floating point number in a byte string and returns a `f64`
- [`float`](crate::number::complete::float): Recognizes floating point number in a byte string and returns a `f32`
- [`hex_digit0`](crate::character::complete::hex_digit0): Recognizes zero or more hexadecimal numerical characters: `[0-9A-Fa-f]`. [`hex_digit1`](crate::character::complete::hex_digit1) does the same but returns at least one character
- [`hex_u32`](crate::number::complete::hex_u32): Recognizes a hex-encoded integer
- [`line_ending`](crate::character::complete::line_ending): Recognizes an end of line (both `\n` and `\r\n`)
- [`multispace0`](crate::character::complete::multispace0): Recognizes zero or more spaces, tabs, carriage returns and line feeds. [`multispace1`](crate::character::complete::multispace1) does the same but returns at least one character
- [`newline`](crate::character::complete::newline): Matches a newline character `\n`
- [`not_line_ending`](crate::character::complete::not_line_ending): Recognizes a string of any char except `\r` or `\n`
- [`oct_digit0`](crate::character::complete::oct_digit0): Recognizes zero or more octal characters: `[0-7]`. [`oct_digit1`](crate::character::complete::oct_digit1) does the same but returns at least one character
- [`bin_digit0`](crate::character::complete::bin_digit0): Recognizes zero or more binary characters: `[0-1]`. [`bin_digit1`](crate::character::complete::bin_digit1) does the same but returns at least one character
- [`rest`](crate::combinator::rest): Return the remaining input
- [`rest_len`](crate::combinator::rest_len): Return the length of the remaining input
- [`space0`](crate::character::complete::space0): Recognizes zero or more spaces and tabs. [`space1`](crate::character::complete::space1) does the same but returns at least one character
- [`tab`](crate::character::complete::tab): Matches a tab character `\t`
