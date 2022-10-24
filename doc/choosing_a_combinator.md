# List of parsers and combinators

**Note**: this list is meant to provide a nicer way to find a nom parser than reading through the documentation on docs.rs. Function combinators are organized in module so they are a bit easier to find.

Links present in this document will nearly always point to `complete` version of the parser. Most of the parsers also have a `streaming` version.

## Basic elements

Those are used to recognize the lowest level elements of your grammar, like, "here is a dot", or "here is an big endian integer".

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [char](https://docs.rs/nom/latest/nom/character/complete/fn.char.html) | `char('a')` |  `"abc"` | `Ok(("bc", 'a'))` |Matches one character (works with non ASCII chars too) | 
| [is_a](https://docs.rs/nom/latest/nom/bytes/complete/fn.is_a.html) | ` is_a("ab")` |  `"ababc"` | `Ok(("c", "abab"))` |Matches a sequence of any of the characters passed as arguments|
| [is_not](https://docs.rs/nom/latest/nom/bytes/complete/fn.is_not.html) | `is_not("cd")` |  `"ababc"` | `Ok(("c", "abab"))` |Matches a sequence of none of the characters passed as arguments|
| [one_of](https://docs.rs/nom/latest/nom/character/complete/fn.one_of.html) | `one_of("abc")` |  `"abc"` | `Ok(("bc", 'a'))` |Matches one of the provided characters (works with non ASCII characters too)|
| [none_of](https://docs.rs/nom/latest/nom/character/complete/fn.none_of.html) | `none_of("abc")` |  `"xyab"` | `Ok(("yab", 'x'))` |Matches anything but the provided characters|
| [tag](https://docs.rs/nom/latest/nom/bytes/complete/fn.tag.html) | `tag("hello")` |  `"hello world"` | `Ok((" world", "hello"))` |Recognizes a specific suite of characters or bytes|
| [tag_no_case](https://docs.rs/nom/latest/nom/bytes/complete/fn.tag_no_case.html) | `tag_no_case("hello")` |  `"HeLLo World"` | `Ok((" World", "HeLLo"))` |Case insensitive comparison. Note that case insensitive comparison is not well defined for unicode, and that you might have bad surprises|
| [take](https://docs.rs/nom/latest/nom/bytes/complete/fn.take.html) | `take(4)` |  `"hello"` | `Ok(("o", "hell"))` |Takes a specific number of bytes or characters|
| [take_while](https://docs.rs/nom/latest/nom/bytes/complete/fn.take_while.html) | `take_while(is_alphabetic)` |  `"abc123"` | `Ok(("123", "abc"))` |Returns the longest list of bytes for which the provided function returns true. `take_while1` does the same, but must return at least one character|
| [take_till](https://docs.rs/nom/latest/nom/bytes/complete/fn.take_till.html) | `take_till(is_alphabetic)` |  `"123abc"` | `Ok(("abc", "123"))` |Returns the longest list of bytes or characters until the provided function returns true. `take_till1` does the same, but must return at least one character. This is the reverse behaviour from `take_while`: `take_till(f)` is equivalent to `take_while(\|c\| !f(c))`|
| [take_until](https://docs.rs/nom/latest/nom/bytes/complete/fn.take_until.html) | `take_until("world")` |  `"Hello world"` | `Ok(("world", "Hello "))` |Returns the longest list of bytes or characters until the provided tag is found. `take_until1` does the same, but must return at least one character|

## Choice combinators

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [alt](https://docs.rs/nom/latest/nom/branch/fn.alt.html) | `alt((tag("ab"), tag("cd")))` |  `"cdef"` | `Ok(("ef", "cd"))` |Try a list of parsers and return the result of the first successful one|
| [permutation](https://docs.rs/nom/latest/nom/branch/fn.permutation.html) | `permutation((tag("ab"), tag("cd"), tag("12")))` | `"cd12abc"` | `Ok(("c", ("ab", "cd", "12"))` |Succeeds when all its child parser have succeeded, whatever the order|

## Sequence combinators

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [delimited](https://docs.rs/nom/latest/nom/sequence/fn.delimited.html) | `delimited(char('('), take(2), char(')'))` | `"(ab)cd"` | `Ok(("cd", "ab"))` ||
| [preceded](https://docs.rs/nom/latest/nom/sequence/fn.preceded.html) | `preceded(tag("ab"), tag("XY"))` | `"abXYZ"` | `Ok(("Z", "XY"))` ||
| [terminated](https://docs.rs/nom/latest/nom/sequence/fn.terminated.html) | `terminated(tag("ab"), tag("XY"))` | `"abXYZ"` | `Ok(("Z", "ab"))` ||
| [pair](https://docs.rs/nom/latest/nom/sequence/fn.pair.html) | `pair(tag("ab"), tag("XY"))` | `"abXYZ"` | `Ok(("Z", ("ab", "XY")))` ||
| [separated_pair](https://docs.rs/nom/latest/nom/sequence/fn.separated_pair.html) | `separated_pair(tag("hello"), char(','), tag("world"))` | `"hello,world!"` | `Ok(("!", ("hello", "world")))` ||
| [tuple](https://docs.rs/nom/latest/nom/sequence/fn.tuple.html) | `tuple((tag("ab"), tag("XY"), take(1)))` | `"abXYZ!"` | `Ok(("!", ("ab", "XY", "Z")))` |Chains parsers and assemble the sub results in a tuple. You can use as many child parsers as you can put elements in a tuple|

## Applying a parser multiple times

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [count](https://docs.rs/nom/latest/nom/multi/fn.count.html) | `count(take(2), 3)` | `"abcdefgh"` | `Ok(("gh", vec!["ab", "cd", "ef"]))` |Applies the child parser a specified number of times|
| [many0](https://docs.rs/nom/latest/nom/multi/fn.many0.html) | `many0(tag("ab"))` |  `"abababc"` | `Ok(("c", vec!["ab", "ab", "ab"]))` |Applies the parser 0 or more times and returns the list of results in a Vec. `many1` does the same operation but must return at least one element|
| [many_m_n](https://docs.rs/nom/latest/nom/multi/fn.many_m_n.html) | `many_m_n(1, 3, tag("ab"))` | `"ababc"` | `Ok(("c", vec!["ab", "ab"]))` |Applies the parser between m and n times (n included) and returns the list of results in a Vec|
| [many_till](https://docs.rs/nom/latest/nom/multi/fn.many_till.html) | `many_till(tag( "ab" ), tag( "ef" ))` | `"ababefg"` | `Ok(("g", (vec!["ab", "ab"], "ef")))` |Applies the first parser until the second applies. Returns a tuple containing the list of results from the first in a Vec and the result of the second|
| [separated_list0](https://docs.rs/nom/latest/nom/multi/fn.separated_list0.html) | `separated_list0(tag(","), tag("ab"))` | `"ab,ab,ab."` | `Ok((".", vec!["ab", "ab", "ab"]))` |`separated_list1` works like `separated_list0` but must returns at least one element|
| [fold_many0](https://docs.rs/nom/latest/nom/multi/fn.fold_many0.html) | `fold_many0(be_u8, \|\| 0, \|acc, item\| acc + item)` | `[1, 2, 3]` | `Ok(([], 6))` |Applies the parser 0 or more times and folds the list of return values. The `fold_many1` version must apply the child parser at least one time|
| [fold_many_m_n](https://docs.rs/nom/latest/nom/multi/fn.fold_many_m_n.html) | `fold_many_m_n(1, 2, be_u8, \|\| 0, \|acc, item\| acc + item)` | `[1, 2, 3]` | `Ok(([3], 3))` |Applies the parser between m and n times (n included) and folds the list of return value|
| [length_count](https://docs.rs/nom/latest/nom/multi/fn.length_count.html) | `length_count(number, tag("ab"))` | `"2ababab"` | `Ok(("ab", vec!["ab", "ab"]))` |Gets a number from the first parser, then applies the second parser that many times|

## Integers

Parsing integers from binary formats can be done in two ways: With parser functions, or combinators with configurable endianness.

The following parsers could be found on [docs.rs number section](https://docs.rs/nom/latest/nom/number/complete/index.html).

- **configurable endianness:** [`i16`](https://docs.rs/nom/latest/nom/number/complete/fn.i16.html), [`i32`](https://docs.rs/nom/latest/nom/number/complete/fn.i32.html), [`i64`](https://docs.rs/nom/latest/nom/number/complete/fn.i64.html), [`u16`](https://docs.rs/nom/latest/nom/number/complete/fn.u16.html), [`u32`](https://docs.rs/nom/latest/nom/number/complete/fn.u32.html), [`u64`](https://docs.rs/nom/latest/nom/number/complete/fn.u64.html) are combinators that take as argument a [`nom::number::Endianness`](https://docs.rs/nom/latest/nom/number/enum.Endianness.html), like this: `i16(endianness)`. If the parameter is `nom::number::Endianness::Big`, parse a big endian `i16` integer, otherwise a little endian `i16` integer.
- **fixed endianness**: The functions are prefixed by `be_` for big endian numbers, and by `le_` for little endian numbers, and the suffix is the type they parse to. As an example, `be_u32` parses a big endian unsigned integer stored in 32 bits.
  - [`be_f32`](https://docs.rs/nom/latest/nom/number/complete/fn.be_f32.html), [`be_f64`](https://docs.rs/nom/latest/nom/number/complete/fn.be_f64.html): Big endian floating point numbers
  - [`le_f32`](https://docs.rs/nom/latest/nom/number/complete/fn.le_f32.html), [`le_f64`](https://docs.rs/nom/latest/nom/number/complete/fn.le_f64.html): Little endian floating point numbers
  - [`be_i8`](https://docs.rs/nom/latest/nom/number/complete/fn.be_i8.html), [`be_i16`](https://docs.rs/nom/latest/nom/number/complete/fn.be_i16.html), [`be_i24`](https://docs.rs/nom/latest/nom/number/complete/fn.be_i24.html), [`be_i32`](https://docs.rs/nom/latest/nom/number/complete/fn.be_i32.html), [`be_i64`](https://docs.rs/nom/latest/nom/number/complete/fn.be_i64.html), [`be_i128`](https://docs.rs/nom/latest/nom/number/complete/fn.be_i128.html): Big endian signed integers
  - [`be_u8`](https://docs.rs/nom/latest/nom/number/complete/fn.be_u8.html), [`be_u16`](https://docs.rs/nom/latest/nom/number/complete/fn.be_u16.html), [`be_u24`](https://docs.rs/nom/latest/nom/number/complete/fn.be_u24.html), [`be_u32`](https://docs.rs/nom/latest/nom/number/complete/fn.be_u32.html), [`be_u64`](https://docs.rs/nom/latest/nom/number/complete/fn.be_u64.html), [`be_u128`](https://docs.rs/nom/latest/nom/number/complete/fn.be_u128.html): Big endian unsigned integers
  - [`le_i8`](https://docs.rs/nom/latest/nom/number/complete/fn.le_i8.html), [`le_i16`](https://docs.rs/nom/latest/nom/number/complete/fn.le_i16.html), [`le_i24`](https://docs.rs/nom/latest/nom/number/complete/fn.le_i24.html), [`le_i32`](https://docs.rs/nom/latest/nom/number/complete/fn.le_i32.html), [`le_i64`](https://docs.rs/nom/latest/nom/number/complete/fn.le_i64.html), [`le_i128`](https://docs.rs/nom/latest/nom/number/complete/fn.le_i128.html): Little endian signed integers
  - [`le_u8`](https://docs.rs/nom/latest/nom/number/complete/fn.le_u8.html), [`le_u16`](https://docs.rs/nom/latest/nom/number/complete/fn.le_u16.html), [`le_u24`](https://docs.rs/nom/latest/nom/number/complete/fn.le_u24.html), [`le_u32`](https://docs.rs/nom/latest/nom/number/complete/fn.le_u32.html), [`le_u64`](https://docs.rs/nom/latest/nom/number/complete/fn.le_u64.html), [`le_u128`](https://docs.rs/nom/latest/nom/number/complete/fn.le_u128.html): Little endian unsigned integers

## Streaming related

- [`eof`](https://docs.rs/nom/latest/nom/combinator/fn.eof.html): Returns its input if it is at the end of input data
- [`complete`](https://docs.rs/nom/latest/nom/combinator/fn.complete.html): Replaces an `Incomplete` returned by the child parser with an `Error`

## Modifiers

- [`cond`](https://docs.rs/nom/latest/nom/combinator/fn.cond.html): Conditional combinator. Wraps another parser and calls it if the condition is met
- [`Parser::flat_map`](https://docs.rs/nom/latest/nom/trait.Parser.html#method.flat_map): method to map a new parser from the output of the first parser, then apply that parser over the rest of the input
- [`flat_map`](https://docs.rs/nom/latest/nom/combinator/fn.flat_map.html): function variant of `Parser::flat_map`
- [`Parser::map`](https://docs.rs/nom/latest/nom/trait.Parser.html#method.map): method to map a function on the result of a parser
- [`map`](https://docs.rs/nom/latest/nom/combinator/fn.map.html): function variant of `Parser::map`
- [`map_opt`](https://docs.rs/nom/latest/nom/combinator/fn.map_opt.html): Maps a function returning an `Option` on the output of a parser
- [`map_res`](https://docs.rs/nom/latest/nom/combinator/fn.map_res.html): Maps a function returning a `Result` on the output of a parser
- [`not`](https://docs.rs/nom/latest/nom/combinator/fn.not.html): Returns a result only if the embedded parser returns `Error` or `Incomplete`. Does not consume the input
- [`opt`](https://docs.rs/nom/latest/nom/combinator/fn.opt.html): Make the underlying parser optional
- [`peek`](https://docs.rs/nom/latest/nom/combinator/fn.peek.html): Returns a result without consuming the input
- [`recognize`](https://docs.rs/nom/latest/nom/combinator/fn.recognize.html): If the child parser was successful, return the consumed input as the produced value
- [`consumed`](https://docs.rs/nom/latest/nom/combinator/fn.consumed.html): If the child parser was successful, return a tuple of the consumed input and the produced output.
- [`verify`](https://docs.rs/nom/latest/nom/combinator/fn.verify.html): Returns the result of the child parser if it satisfies a verification function

## Error management and debugging

- [`dbg_dmp`](https://docs.rs/nom/latest/nom/fn.dbg_dmp.html): Prints a message and the input if the parser fails

## Text parsing

- [`escaped`](https://docs.rs/nom/latest/nom/bytes/complete/fn.escaped.html): Matches a byte string with escaped characters
- [`escaped_transform`](https://docs.rs/nom/latest/nom/bytes/complete/fn.escaped_transform.html): Matches a byte string with escaped characters, and returns a new string with the escaped characters replaced

## Binary format parsing

- [`length_data`](https://docs.rs/nom/latest/nom/multi/fn.length_data.html): Gets a number from the first parser, then takes a subslice of the input of that size, and returns that subslice
- [`length_value`](https://docs.rs/nom/latest/nom/multi/fn.length_value.html): Gets a number from the first parser, takes a subslice of the input of that size, then applies the second parser on that subslice. If the second parser returns `Incomplete`, `length_value` will return an error

## Bit stream parsing

- [`bits`](https://docs.rs/nom/latest/nom/bits/fn.bits.html): Transforms the current input type (byte slice `&[u8]`) to a bit stream on which bit specific parsers and more general combinators can be applied
- [`bytes`](https://docs.rs/nom/latest/nom/bits/fn.bytes.html): Transforms its bits stream input back into a byte slice for the underlying parser

## Remaining combinators

- [`success`](https://docs.rs/nom/latest/nom/combinator/fn.success.html): Returns a value without consuming any input, always succeeds
- [`fail`](https://docs.rs/nom/latest/nom/combinator/fn.fail.html): Inversion of `success`. Always fails.

## Character test functions

Use these functions with a combinator like `take_while`:

- [`is_alphabetic`](https://docs.rs/nom/latest/nom/character/fn.is_alphabetic.html): Tests if byte is ASCII alphabetic: `[A-Za-z]`
- [`is_alphanumeric`](https://docs.rs/nom/latest/nom/character/fn.is_alphanumeric.html): Tests if byte is ASCII alphanumeric: `[A-Za-z0-9]`
- [`is_digit`](https://docs.rs/nom/latest/nom/character/fn.is_digit.html): Tests if byte is ASCII digit: `[0-9]`
- [`is_hex_digit`](https://docs.rs/nom/latest/nom/character/fn.is_hex_digit.html): Tests if byte is ASCII hex digit: `[0-9A-Fa-f]`
- [`is_oct_digit`](https://docs.rs/nom/latest/nom/character/fn.is_oct_digit.html): Tests if byte is ASCII octal digit: `[0-7]`
- [`is_space`](https://docs.rs/nom/latest/nom/character/fn.is_space.html): Tests if byte is ASCII space or tab: `[ \t]`
- [`is_newline`](https://docs.rs/nom/latest/nom/character/fn.is_newline.html): Tests if byte is ASCII newline: `[\n]`

Alternatively there are ready to use functions:

- [`alpha0`](https://docs.rs/nom/latest/nom/character/complete/fn.alpha0.html): Recognizes zero or more lowercase and uppercase alphabetic characters: `[a-zA-Z]`. [`alpha1`](https://docs.rs/nom/latest/nom/character/complete/fn.alpha1.html) does the same but returns at least one character
- [`alphanumeric0`](https://docs.rs/nom/latest/nom/character/complete/fn.alphanumeric0.html): Recognizes zero or more numerical and alphabetic characters: `[0-9a-zA-Z]`. [`alphanumeric1`](https://docs.rs/nom/latest/nom/character/complete/fn.alphanumeric1.html) does the same but returns at least one character
- [`anychar`](https://docs.rs/nom/latest/nom/character/complete/fn.anychar.html): Matches one byte as a character
- [`crlf`](https://docs.rs/nom/latest/nom/character/complete/fn.crlf.html): Recognizes the string `\r\n`
- [`digit0`](https://docs.rs/nom/latest/nom/character/complete/fn.digit0.html): Recognizes zero or more numerical characters: `[0-9]`. [`digit1`](https://docs.rs/nom/latest/nom/character/complete/fn.digit1.html) does the same but returns at least one character
- [`double`](https://docs.rs/nom/latest/nom/number/complete/fn.double.html): Recognizes floating point number in a byte string and returns a `f64`
- [`float`](https://docs.rs/nom/latest/nom/number/complete/fn.float.html): Recognizes floating point number in a byte string and returns a `f32`
- [`hex_digit0`](https://docs.rs/nom/latest/nom/character/complete/fn.hex_digit0.html): Recognizes zero or more hexadecimal numerical characters: `[0-9A-Fa-f]`. [`hex_digit1`](https://docs.rs/nom/latest/nom/character/complete/fn.hex_digit1.html) does the same but returns at least one character
- [`hex_u32`](https://docs.rs/nom/latest/nom/number/complete/fn.hex_u32.html): Recognizes a hex-encoded integer
- [`line_ending`](https://docs.rs/nom/latest/nom/character/complete/fn.line_ending.html): Recognizes an end of line (both `\n` and `\r\n`)
- [`multispace0`](https://docs.rs/nom/latest/nom/character/complete/fn.multispace0.html): Recognizes zero or more spaces, tabs, carriage returns and line feeds. [`multispace1`](https://docs.rs/nom/latest/nom/character/complete/fn.multispace1.html) does the same but returns at least one character
- [`newline`](https://docs.rs/nom/latest/nom/character/complete/fn.newline.html): Matches a newline character `\n`
- [`not_line_ending`](https://docs.rs/nom/latest/nom/character/complete/fn.not_line_ending.html): Recognizes a string of any char except `\r` or `\n`
- [`oct_digit0`](https://docs.rs/nom/latest/nom/character/complete/fn.oct_digit0.html): Recognizes zero or more octal characters: `[0-7]`. [`oct_digit1`](https://docs.rs/nom/latest/nom/character/complete/fn.oct_digit1.html) does the same but returns at least one character
- [`rest`](https://docs.rs/nom/latest/nom/combinator/fn.rest.html): Return the remaining input
- [`space0`](https://docs.rs/nom/latest/nom/character/complete/fn.space0.html): Recognizes zero or more spaces and tabs. [`space1`](https://docs.rs/nom/latest/nom/character/complete/fn.space1.html) does the same but returns at least one character
- [`tab`](https://docs.rs/nom/latest/nom/character/complete/fn.tab.html): Matches a tab character `\t`
