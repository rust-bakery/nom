# List of macros parsers and combinators

**Note**: this list is meant to provide a nicer way to find a nom macros than reading through the
documentation on docs.rs, since rustdoc puts all the macros at the top level. Function combinators
are organized in module so they are a bit easier to find.

## Basic elements

Those are used to recognize the lowest level elements of your grammar, like, "here is a dot", or "here is an big endian integer".

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [char](https://docs.rs/nom/latest/nom/macro.char.html) | `char!('a')` |  `"abc"` | `Ok(("bc", 'a'))` |Matches one character (works with non ASCII chars too) | 
| [is_a](https://docs.rs/nom/latest/nom/macro.is_a.html) | ` is_a!("ab")` |  `"ababc"` | `Ok(("c", "abab"))` |Matches a sequence of any of the characters passed as arguments|
| [is_not](https://docs.rs/nom/latest/nom/macro.is_not.html) | `is_not!("cd")` |  `"ababc"` | `Ok(("c", "abab"))` |Matches a sequence of none of the characters passed as arguments|
| [one_of](https://docs.rs/nom/latest/nom/macro.one_of.html) | `one_of!("abc")` |  `"abc"` | `Ok(("bc", 'a'))` |Matches one of the provided characters (works with non ASCII characters too)|
| [none_of](https://docs.rs/nom/latest/nom/macro.none_of.html) | `none_of!("abc")` |  `"xyab"` | `Ok(("yab", 'x'))` |Matches anything but the provided characters|
| [tag](https://docs.rs/nom/latest/nom/macro.tag.html) | `tag!("hello")` |  `"hello world"` | `Ok((" world", "hello"))` |Recognizes a specific suite of characters or bytes|
| [tag_no_case](https://docs.rs/nom/latest/nom/macro.tag_no_case.html) | `tag_no_case!("hello")` |  `"HeLLo World"` | `Ok((" World", "HeLLo"))` |Case insensitive comparison. Note that case insensitive comparison is not well defined for unicode, and that you might have bad surprises|
| [take](https://docs.rs/nom/latest/nom/macro.take.html) | `take!(4)` |  `"hello"` | `Ok(("o", "hell"))` |Takes a specific number of bytes or characters|
| [take_while](https://docs.rs/nom/latest/nom/macro.take_while.html) | `take_while!(is_alphabetic)` |  `"abc123"` | `Ok(("123", "abc"))` |Returns the longest list of bytes for which the provided function returns true. `take_while1` does the same, but must return at least one character|
| [take_till](https://docs.rs/nom/latest/nom/macro.take_till.html) | `take_till!(is_alphabetic)` |  `"123abc"` | `Ok(("abc", "123"))` |Returns the longest list of bytes or characters until the provided function returns true. `take_till1` does the same, but must return at least one character. This is the reverse behaviour from `take_while`: `take_till!(f)` is equivalent to `take_while!(\|c\| !f(c))`|
| [take_until](https://docs.rs/nom/latest/nom/macro.take_until.html) | `take_until!("world")` |  `"Hello world"` | `Ok(("world", "Hello "))` |Returns the longest list of bytes or characters until the provided tag is found. `take_until1` does the same, but must return at least one character|

## Choice combinators

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [alt](https://docs.rs/nom/latest/nom/macro.alt.html) | `alt!(tag!("ab") \| tag!("cd"))` |  `"cdef"` | `Ok(("ef", "cd"))` |Try a list of parsers and return the result of the first successful one|
| [switch](https://docs.rs/nom/latest/nom/macro.switch.html) | `switch!(take!(2), "ab" => tag!("XYZ") \| "cd" => tag!("123"))` | `"cd1234"` | `Ok(("4", "123"))` |Choose the next parser depending on the result of the first one, if successful, and returns the result of the second parser|
| [permutation](https://docs.rs/nom/latest/nom/macro.permutation.html) | `permutation!(tag!("ab"), tag!("cd"), tag!("12"))` | `"cd12abc"` | `Ok(("c", ("ab", "cd", "12"))` |Succeeds when all its child parser have succeeded, whatever the order|

## Sequence combinators

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [delimited](https://docs.rs/nom/latest/nom/macro.delimited.html) | `delimited!(char!('('), take!(2), char!(')'))` | `"(ab)cd"` | `Ok(("cd", "ab"))` ||
| [preceded](https://docs.rs/nom/latest/nom/macro.preceded.html) | `preceded!(tag!("ab"), tag!("XY"))` | `"abXYZ"` | `Ok(("Z", "XY"))` ||
| [terminated](https://docs.rs/nom/latest/nom/macro.terminated.html) | `terminated!(tag!("ab"), tag!("XY"))` | `"abXYZ"` | `Ok(("Z", "ab"))` ||
| [pair](https://docs.rs/nom/latest/nom/macro.pair.html) | `pair!(tag!("ab"), tag!("XY"))` | `"abXYZ"` | `Ok(("Z", ("ab", "XY")))` ||
| [separated_pair](https://docs.rs/nom/latest/nom/macro.separated_pair.html) | `separated_pair!(tag!("hello"), char!(','), tag!("world"))` | `"hello,world!"` | `Ok(("!", ("hello", "world")))` ||
| [tuple](https://docs.rs/nom/latest/nom/macro.tuple.html) | `tuple!(tag!("ab"), tag!("XY"), take!(1))` | `"abXYZ!"` | `Ok(("!", ("ab", "XY", "Z")))` |Chains parsers and assemble the sub results in a tuple. You can use as many child parsers as you can put elements in a tuple|
| [do_parse](https://docs.rs/nom/latest/nom/macro.do_parse.html) | `do_parse!(tag: take!(2) >> length: be_u8 >> data: take!(length) >> (Buffer { tag: tag, data: data}) )` | `&[0, 0, 3, 1, 2, 3][..]` | `Buffer { tag: &[0, 0][..], data: &[1, 2, 3][..] }` |`do_parse` applies sub parsers in a sequence. It can store intermediary results and make them available for later parsers|

## Applying a parser multiple times

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [count](https://docs.rs/nom/latest/nom/macro.count.html) | `count!(take!(2), 3)` | `"abcdefgh"` | `Ok(("gh", vec!("ab", "cd", "ef")))` |Applies the child parser a specified number of times|
| [many0](https://docs.rs/nom/latest/nom/macro.many0.html) | `many0!(tag!("ab"))` |  `"abababc"` | `Ok(("c", vec!("ab", "ab", "ab")))` |Applies the parser 0 or more times and returns the list of results in a Vec. `many1` does the same operation but must return at least one element|
| [many_m_n](https://docs.rs/nom/latest/nom/macro.many_m_n.html) | `many_m_n!(1, 3, tag!("ab"))` | `"ababc"` | `Ok(("c", vec!("ab", "ab")))` |Applies the parser between m and n times (n included) and returns the list of results in a Vec|
| [many_till](https://docs.rs/nom/latest/nom/macro.many_till.html) | `many_till!(tag!( "ab" ), tag!( "ef" ))` | `"ababefg"` | `Ok(("g", (vec!("ab", "ab"), "ef")))` |Applies the first parser until the second applies. Returns a tuple containing the list of results from the first in a Vec and the result of the second|
| [separated_list](https://docs.rs/nom/latest/nom/macro.separated_list.html) | `separated_list!(tag!(","), tag!("ab"))` | `"ab,ab,ab."` | `Ok((".", vec!("ab", "ab", "ab")))` |`separated_nonempty_list` works like `separated_list` but must returns at least one element|
| [fold_many0](https://docs.rs/nom/latest/nom/macro.fold_many0.html) | `fold_many0!(be_u8, 0, \|acc, item\| acc + item)` | `[1, 2, 3]` | `Ok(([], 6))` |Applies the parser 0 or more times and folds the list of return values. The `fold_many1` version must apply the child parser at least one time|
| [fold_many_m_n](https://docs.rs/nom/latest/nom/macro.fold_many_m_n.html) | `fold_many_m_n!(1, 2, be_u8, 0, \|acc, item\| acc + item)` | `[1, 2, 3]` | `Ok(([3], 3))` |Applies the parser between m and n times (n included) and folds the list of return value|
| [length_count](https://docs.rs/nom/latest/nom/macro.length_count.html) | `length_count!(number, tag!("ab"))` | `"2ababab"` | `Ok(("ab", vec!("ab", "ab")))` |Gets a number from the first parser, then applies the second parser that many times|

## Integers

Parsing integers from binary formats can be done in two ways: With parser functions, or combinators with configurable endianness:

- **configurable endianness:** `i16!`, `i32!`, `i64!`, `u16!`, `u32!`, `u64!` are combinators that take as argument a `nom::Endianness`, like this: `i16!(endianness)`. If the parameter is `nom::Endianness::Big`, parse a big endian `i16` integer, otherwise a little endian `i16` integer.
- **fixed endianness**: The functions are prefixed by `be_` for big endian numbers, and by `le_` for little endian numbers, and the suffix is the type they parse to. As an example, `be_u32` parses a big endian unsigned integer stored in 32 bits.
- `be_f32`, `be_f64`, `le_f32`, `le_f64`: Recognize floating point numbers
- `be_i8`, `be_i16`, `be_i24`, `be_i32`, `be_i64`: Big endian signed integers
- `be_u8`, `be_u16`, `be_u24`, `be_u32`, `be_u64`: Big endian unsigned integers
- `le_i8`, `le_i16`, `le_i24`, `le_i32`, `le_i64`: Little endian signed integers
- `le_u8`, `le_u16`, `le_u24`, `le_u32`, `le_u64`: Little endian unsigned integers

## Streaming related

- `eof!`: Returns its input if it is at the end of input data
- `complete!`: Replaces an `Incomplete` returned by the child parser with an `Error`

## Modifiers

- `cond!`: Conditional combinator. Wraps another parser and calls it if the condition is met
- `flat_map!`: 
- `map!`: Maps a function on the result of a parser
- `map_opt!`: Maps a function returning an `Option` on the output of a parser
- `map_res!`: Maps a function returning a `Result` on the output of a parser
- `not!`: Returns a result only if the embedded parser returns `Error` or `Incomplete`. Does not consume the input
- `opt!`: Make the underlying parser optional
- `opt_res!`: Make the underlying parser optional
- `parse_to!`: Uses the parse method from `std::str::FromStr` to convert the current input to the specified type
- `peek!`: Returns a result without consuming the input
- `recognize!`: If the child parser was successful, return the consumed input as the produced value
- `return_error!`: Prevents backtracking if the child parser fails
- `tap!`: Allows access to the parser's result without affecting it
- `verify!`: Returns the result of the child parser if it satisfies a verification function

## Error management and debugging

- `add_return_error!`: Add an error if the child parser fails
- `dbg!`: Prints a message if the parser fails
- `dbg_dmp!`: Prints a message and the input if the parser fails
- `error_node_position!`: Creates a parse error from a `nom::ErrorKind`, the position in the input and the next error in the parsing tree. If the `verbose-errors` feature is not activated, it defaults to only the error code
- `error_position!`: Creates a parse error from a `nom::ErrorKind` and the position in the input. If the `verbose-errors` feature is not activated, it defaults to only the error code
- `fix_error!`: Translate parser result from `IResult` to `IResult` with a custom type

## Text parsing

- `escaped!`: Matches a byte string with escaped characters
- `escaped_transform!`: Matches a byte string with escaped characters, and returns a new string with the escaped characters replaced

## Binary format parsing

- `length_data!`: Gets a number from the first parser, then takes a subslice of the input of that size, and returns that subslice
- `length_bytes!`: Alias for length_data
- `length_value!`: Gets a number from the first parser, takes a subslice of the input of that size, then applies the second parser on that subslice. If the second parser returns `Incomplete`, `length_value!` will return an error

## Bit stream parsing

- `bits!`: Transforms the current input type (byte slice `&[u8]`) to a bit stream on which bit specific parsers and more general combinators can be applied
- `bytes!`: Transforms its bits stream input back into a byte slice for the underlying parser
- `tag_bits!`: Matches an integer pattern to a bitstream. The number of bits of the input to compare must be specified
- `take_bits!`: Generates a parser consuming the specified number of bits

## Whitespace delimited formats parsing

- `eat_separator!`: Helper macro to build a separator parser
- `sep!`: Parser rewriting macro for whitespace separated formats
- `wrap_sep!`: 
- `ws!`: Consumes whitespace characters, i.e. the `\s` regex pattern

## Remaining combinators

- `apply!`: Emulate function currying: `apply!(my_function, arg1, arg2, ...)` becomes `my_function(input, arg1, arg2, ...)`
- `call!`: Used to wrap common expressions and function as macros
- `method!`: Makes a method from a parser combination
- `named!`: Makes a function from a parser combination
- `named_args!`: Makes a function from a parser combination with arguments
- `named_attr!`: Makes a function from a parser combination, with attributes
- `try_parse!`: A bit like `std::try!`, this macro will return the remaining input and parsed value if the child parser returned `Ok`, and will do an early return for `Error` and `Incomplete`. This can provide more flexibility than `do_parse!` if needed
- `success`: Returns a value without consuming any input, always succeeds

## Character test functions

Use these functions with a combinator like `take_while!`:

- `is_alphabetic`: Tests if byte is ASCII alphabetic: `[A-Za-z]`
- `is_alphanumeric`: Tests if byte is ASCII alphanumeric: `[A-Za-z0-9]`
- `is_digit`: Tests if byte is ASCII digit: `[0-9]`
- `is_hex_digit`: Tests if byte is ASCII hex digit: `[0-9A-Fa-f]`
- `is_oct_digit`: Tests if byte is ASCII octal digit: `[0-7]`
- `is_space`: Tests if byte is ASCII space or tab: `[ \t]`
- `alpha`: Recognizes one or more lowercase and uppercase alphabetic characters: `[a-zA-Z]`
- `alphanumeric`: Recognizes one or more numerical and alphabetic characters: `[0-9a-zA-Z]`
- `anychar`: 
- `begin`: 
- `crlf`: 
- `digit`: Recognizes one or more numerical characters: `[0-9]`
- `double`: Recognizes floating point number in a byte string and returns a `f64`
- `eol`: 
- `float`: Recognizes floating point number in a byte string and returns a `f32`
- `hex_digit`: Recognizes one or more hexadecimal numerical characters: `[0-9A-Fa-f]`
- `hex_u32`: Recognizes a hex-encoded integer
- `line_ending`: Recognizes an end of line (both `\n` and `\r\n`)
- `multispace`: Recognizes one or more spaces, tabs, carriage returns and line feeds
- `newline`: Matches a newline character `\n`
- `non_empty`: Recognizes non empty buffers
- `not_line_ending`: 
- `oct_digit`: Recognizes one or more octal characters: `[0-7]`
- `rest`: Return the remaining input
- `shift`: 
- `sized_buffer`: 
- `space`: Recognizes one or more spaces and tabs
- `tab`: Matches a tab character `\t`
