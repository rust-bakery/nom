
# List of parsers and combinators

## Basic elements
Those are used to recognize the lowest level elements of your grammar, like, "here is a dot", or "here is an big endian integer".

| combinator|usage | input | output | comment |
|---|---|---|---|---|
| [char](https://docs.rs/nom/4.0.0-alpha2/nom/macro.char.html) | `char!('a')` |  `"abc"` | `Ok(("bc", 'a'))`| matches one character (works with non ASCII chars too) | 
|[is_a](https://docs.rs/nom/4.0.0-alpha2/nom/macro.is_a.html) | ` is_a!("ab")` |  `"ababc"` | `Ok(("c", "abab"))`|matches a sequence of any of the characters passed as arguments|
| [is_not](https://docs.rs/nom/4.0.0-alpha2/nom/macro.is_not.html) |`is_not!("cd")` |  `"ababc"` | `Ok(("c", "abab"))`|matches a sequence of none of the characters passed as arguments|
| [one_of](https://docs.rs/nom/4.0.0-alpha2/nom/macro.one_of.html) |`one_of!("abc")` |  `"abc"` | `Ok(("bc", 'a'))`|matches one of the provided characters (works with non ASCII characters too)|
| [none_of](https://docs.rs/nom/4.0.0-alpha2/nom/macro.none_of.html) |`none_of!("abc")` |  `"xyab"` | `Ok( ("yab", 'x') )`|matches anything but the provided characters|
| [tag](https://docs.rs/nom/4.0.0-alpha2/nom/macro.tag.html) |`tag!("hello")` |  `"hello world"` | `Ok( (" world", "hello") )`|recognizes a specific suite of characters or bytes|
| [tag_no_case](https://docs.rs/nom/4.0.0-alpha2/nom/macro.tag_no_case.html) |`tag_no_case!("hello")` |  `"HeLLo World"` | `Ok( (" World", "HeLLo") )`|case insensitive comparison. Note that case insensitive comparison is not well defined for unicode, and that you might have bad surprises|
| [take](https://docs.rs/nom/4.0.0-alpha2/nom/macro.take.html) |`take!(4)` |  `"hello"` | `Ok( ("o", "hell") )`|takes a specific number of bytes or characters|
| [take_while](https://docs.rs/nom/4.0.0-alpha2/nom/macro.take_while.html) |`take_while!(is_alphabetic)` |  `"abc123"` | `Ok( ("123", "abc") )`| returns the longest list of bytes for which the provided function returns true. `take_while1` does the same, but must return at least one character|
| [take_till](https://docs.rs/nom/4.0.0-alpha2/nom/macro.take_till.html) |`take_till!(is_alphabetic)` |  `"123abc"` | `Ok( ("abc", "123) )`|returns the longest list of bytes or characters until the provided function returns true. `take_till1` does the same, but must return at least one character. This is the reverse behaviour from `take_while`: `take_till!(f)` is equivalent to `take_while!(|c| !f(c))`|
|[take_until](https://docs.rs/nom/4.0.0-alpha2/nom/macro.take_until.html) | `take_until!("world")` |  `"Hello world"` | `Ok( ("world", "Hello ") )`|returns the longest list of bytes or characters until the provided tag is found. `take_until1` does the same, but must return at least one character|
|[take_until_and_consume](https://docs.rs/nom/4.0.0-alpha2/nom/macro.take_until_and_consume.html) | `take_until_and_consume!("world")` |  `"Hello world!"` | `Ok( ("!", "Hello ") )`| same as `take_until` but consumes the tag. `take_until_and_consume1` does the same, but must return at least one character|
| [take_until_either](https://docs.rs/nom/4.0.0-alpha2/nom/macro.take_until_either.html) |`take_until_either!` |  `` | ``|DEPRECATED? returns the longest list of bytes until any of the provided characters are found|
| [take_until_either_and_consume](https://docs.rs/nom/4.0.0-alpha2/nom/macro.take_until_either_and_consume.html) |`take_until_either_and_consume` |  `` | ``|DEPRECATED? same as take_until_either!, but consumes the terminating character|
|[value](https://docs.rs/nom/4.0.0-alpha2/nom/macro.value.html) | `value!(42, tag!("abcd"))` |`"abcdef"` | `Ok( ("ef", 42) )`|replaces the result of the child parser with the provided value. Can also be used without a child parser. `value!(42)` would return the `42` value without consuming the input|


## Choice combinators

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [alt](https://docs.rs/nom/4.0.0-alpha2/nom/macro.alt.html) |`alt!(tag!("ab") \| tag!("cd"))` |  `"cdef"` | `Ok( ("ef", "cd") )`|try a list of parsers and return the result of the first successful one|
| [switch](https://docs.rs/nom/4.0.0-alpha2/nom/macro.switch.html) |`switch!(take!(2), "ab" => tag!("XYZ") \| "cd" => tag!("123"))` |  `"cd1234"` | `Ok(("4", "123"))`|choose the next parser depending on the result of the first one, if successful, and returns the result of the second parser|
|[permutation](https://docs.rs/nom/4.0.0-alpha2/nom/macro.permutation.html) | `permutation!(tag!("ab"), tag!("cd"), tag!("12"))` |  `"cd12abc"` | `Ok( ("c", ("ab", "cd", "12") )`|succeeds when all its child parser have succeeded, whatever the order|

## Sequence combinators
| combinator|usage | input | output | comment |
|---|---|---|---|---|
| [delimited](https://docs.rs/nom/4.0.0-alpha2/nom/macro.delimited.html) |`delimited!(char!('('), take(2), char!(')'))` |  `"(ab)cd"` | `Ok( ("cd", "ab") )`||
| [preceded](https://docs.rs/nom/4.0.0-alpha2/nom/macro.preceded.html) |`preceded!(tag!("ab"), tag!("XY"))` |  `"abXYZ"` | `Ok( ("Z", "XY") )`||
| [terminated](https://docs.rs/nom/4.0.0-alpha2/nom/macro.terminated.html) |`terminated!(tag!("ab"), tag!("XY"))` |  `"abXYZ"` | `Ok( ("Z", "ab") )`||
| [pair](https://docs.rs/nom/4.0.0-alpha2/nom/macro.pair.html) |`pair!(tag!("ab"), tag!("XY"))` |  `"abXYZ"` | `Ok( ("Z", ("ab", "XY")) )`||
| [separated_pair](https://docs.rs/nom/4.0.0-alpha2/nom/macro.separated_pair.html) |`separated_pair!(tag!("hello"), char!(','), tag!("world"))` |  `"hello,world!"` | `Ok( ("!", ("hello", "world")) )`||
| [tuple](https://docs.rs/nom/4.0.0-alpha2/nom/macro.tuple.html) |`tuple!(tag!("ab"), tag!("XY"), take!(1))` |  `"abXYZ!"` | `Ok( ("!", ("ab", "XY", "Z")) )`|chains parsers and assemble the sub results in a tuple. You can use as many child parsers as you can put elements in a tuple|
| [do_parse](https://docs.rs/nom/4.0.0-alpha2/nom/macro.do_parse.html) |`do_parse!(tag: take!(2) >> length: be_u8 >> data: take!(length) >> (Buffer { tag: tag, data: data}) )` |  `&[0, 0, 3, 1, 2, 3][..]` | `Buffer { tag: &[0, 0][..], data: &[1, 2, 3][..] }`|`do_parse` applies sub parsers in a sequence. it can store intermediary results and make them available for later parsers|

## Applying a parser multiple times

| combinatoe|usage | input | output | comment |
|---|---|---|---|---|
| [count](https://docs.rs/nom/4.0.0-alpha2/nom/macro.count.html) |`count!(take!(2), 3)` |  `"abcdefgh"` | `Ok( ("gh", vec!("ab", "cd", "ef")) )`|applies the child parser a specified number of times|
| [count_fixed](https://docs.rs/nom/4.0.0-alpha2/nom/macro.count_fixed.html) |`count_fixed!(&[u8], take!(2), 3)` |  `"abcdefgh"` | `Ok( ("gh", ["ab", "cd", "ef"]))`|applies the child parser a fixed number of times and returns a fixed size array. The type must be specified and it must be `Copy`|
| [many0](https://docs.rs/nom/4.0.0-alpha2/nom/macro.many0.html) |`many0!(tag!("ab"))` |  `"abababc"` | `Ok( ("c", vec!("ab", "ab", "ab")) )`|Applies the parser 0 or more times and returns the list of results in a Vec. `many1` does the same operation but must return at least one element|
| [many_m_n](https://docs.rs/nom/4.0.0-alpha2/nom/macro.many_m_n.html) |`many_m_n!(1, 3, tag!("ab"))` |  `"ababc"` | `Ok( ("c", vec!("ab", "ab")) )`|applies the parser between m and n times (n included) and returns the list of results in a Vec|
| [many_till](https://docs.rs/nom/4.0.0-alpha2/nom/macro.many_till.html) |`many_till!( tag!( "ab" ), tag!( "ef" ) )` |  `"ababefg"` | `Ok( ("g", (vec!("ab", "ab"), "ef")) )`|Applies the first parser until the second applies. Returns a tuple containing the list of results from the first in a Vec and the result of the second.|
| [separated_list](https://docs.rs/nom/4.0.0-alpha2/nom/macro.separated_list.html) |`separated_list!(tag!(","), tag!("ab"))` |  `"ab,ab,ab."` | `Ok( (".", vec!("ab", "ab", "ab")) )`|`separated_nonempty_list` works like `separated_list` but must returns at least one element|
| [fold_many0](https://docs.rs/nom/4.0.0-alpha2/nom/macro.fold_many0.html) |`fold_many0!(be_u8, 0, \|acc, item\| acc + item)` |  `[1, 2, 3]` | `Ok( ([], 6) )`|applies the parser 0 or more times and folds the list of return values. The `fold_many1` version must apply the child parser at least one time|
| [fold_many_m_n](https://docs.rs/nom/4.0.0-alpha2/nom/macro.fold_many_m_n.html) |`fold_many_m_n!(1, 2, be_u8, 0, \|acc, item\| acc + item)` |  `[1, 2, 3]` | `Ok( ([3], 3))`|applies the parser between m and n times (n included) and folds the list of return value|
| [length_count](https://docs.rs/nom/4.0.0-alpha2/nom/macro.length_count.html) |`length_count!(number, tag!("ab"))` |  `"2ababab"` | `Ok( ("ab", vec!("ab", "ab")) )`|gets a number from the first parser, then applies the second parser that many times|

## Integers

Parsing integers from binary formats can be done in two ways: with parser functions, or combinators with configurable endianness:

- **configurable endianness:** i16!, i32!, i64!, u16!, u32!, u64! are combinators that take as argument a nom::Endianness, like this: i16!(endianness). If the parameter is nom::Endianness::Big, parse a big endian i16 integer, otherwise a little endian i16 integer
- **fixed endianness**: the functions are prefixed by "be_" for big endian numbers, and by "le_" for little endian numbers, and the suffix is the type they parse to. As an example, "be_u32" parses a big endian unsigned integer stored in 32 bits.
- **be_f32, be_f64, le_f32, le_f64**: recognize floating point numbers
- **be_i8, be_i16, be_i32, be_i24, be_i32, be_i64**: big endian signed integers
- **be_u8, be_u16, be_u32, be_u24, be_u32, be_u64**: big endian unsigned integers
- **le_i8, le_i16, le_i32, le_i24, le_i32, le_i64**: little endian signed integers
- **le_u8, le_u16, le_u32, le_u24, le_u32, le_u64**: little endian unsigned integers

## Streaming related

eof!: eof!() returns its input if it is at the end of input data
complete!: replaces a Incomplete returned by the child parser with an Error
alt_complete!: is equivalent to the alt! combinator, except that it will not returns Incomplete when one of the constituting parsers returns Incomplete. Instead, it will try the next alternative in the chain.
separated_list_complete!: This is equivalent to the separated_list! combinator, except that it will return Error when either the separator or element subparser returns Incomplete.
separated_nonempty_list_complete!: This is equivalent to the separated_nonempty_list! combinator, except that it will return Error when either the separator or element subparser returns Incomplete.

## Modifiers
| usage | input | output | comment |
|---|---|---|---|
| `` |  `` | ``||
| `` |  `` | ``||
| `` |  `` | ``||
| `` |  `` | ``||
| `` |  `` | ``||

- cond!: conditional combinator
- cond_reduce!: Conditional combinator with error
- cond_with_error!: Conditional combinator
- expr_opt!: evaluates an expression that returns a Option and returns a Ok((I,T)) if Some
- expr_res!: evaluates an expression that returns a Result and returns a Ok((I,T)) if Ok
- flat_map!:
- map!: maps a function on the result of a parser
- map_opt!: maps a function returning an Option on the output of a parser
- map_res!: maps a function returning a Result on the output of a parser
- not!: returns a result only if the embedded parser returns Error or Incomplete does not consume the input
- opt!: make the underlying parser optional
- opt_res!: make the underlying parser optional
- parse_to!: uses the parse method from std::str::FromStr to convert the current input to the specified type
- peek!: returns a result without consuming the input
- recognize!: if the child parser was successful, return the consumed input as produced value
- return_error!: prevents backtracking if the child parser fails
- tap!: allows access to the parser's result without affecting it
- verify!: returns the result of the child parser if it satisfies a verification function

## Error management and debugging

- add_return_error!: Add an error if the child parser fails
- dbg!: Prints a message if the parser fails
- dbg_dmp!: Prints a message and the input if the parser fails
- error_node_position!: creates a parse error from a nom::ErrorKind, the position in the input and the next error in the parsing tree. if "verbose-errors" is not activated, it default to only the error code
- error_position!: creates a parse error from a nom::ErrorKind and the position in the input if "verbose-errors" is not activated, it default to only the error code
- fix_error!: translate parser result from IResult to IResult with a custom type


## Text parsing

- escaped!: matches a byte string with escaped characters.
- escaped_transform!: matches a byte string with escaped characters, and returns a new string with the escaped characters replaced

## Binary format parsing
- length_data!: gets a number from the first parser, than takes a subslice of the input of that size, and returns that subslice
- length_bytes!: alias for length_data
- length_value!: gets a number from the first parser, takes a subslice of the input of that size, then applies the second parser on that subslice. If the second parser returns Incomplete, length_value will return an error

## Bit stream parsing

- bits!: transforms the current input type (byte slice &[u8]) to a bit stream on which bit specific parsers and more general combinators can be applied
- bytes!: transforms its bits stream input back into a byte slice for the underlying parsers.
- tag_bits!: matches an integer pattern to a bitstream. The number of bits of the input to compare must be specified
- take_bits!: generates a parser consuming the specified number of bits
Whitespace delimited formats parsing
- eat_separator!: helper macros to build a separator parser
- sep!: sep is the parser rewriting macro for whitespace separated formats
- wrap_sep!:
- ws!:

## Remaining combinators

- apply!: emulate function currying: apply!(my_function, arg1, arg2, ...) becomes my_function(input, arg1, arg2, ...)
- apply_m!: emulate function currying for method calls on structs apply_m!(self.my_function, arg1, arg2, ...) becomes self.my_function(input, arg1, arg2, ...)
- call!: Used to wrap common expressions and function as macros
- call_m!: Used to called methods then move self back into self
- closure!: Wraps a parser in a closure
- method!: Makes a method from a parser combination
- named!: Makes a function from a parser combination
- named_args!: Makes a function from a parser combination with arguments.
- named_attr!: Makes a function from a parser combination, with attributes
- try_parse!: A bit like std::try!, this macro will return the remaining input and parsed value if the child parser returned Ok, and will do an early return for Error and Incomplete this can provide more flexibility than do_parse! if needed

## Character test functions

use those functions with a combinator like take_while!:

- is_alphabetic: Tests if byte is ASCII alphabetic: A-Z, a-z
- is_alphanumeric: Tests if byte is ASCII alphanumeric: A-Z, a-z, 0-9
- is_digit: Tests if byte is ASCII digit: 0-9
- is_hex_digit: Tests if byte is ASCII hex digit: 0-9, A-F, a-f
- is_oct_digit: Tests if byte is ASCII octal digit: 0-7
- is_space: Tests if byte is ASCII space or tab
- Remaining functions (sort those out in the other categories)
- alpha: Recognizes one or more lowercase and uppercase alphabetic characters: a-zA-Z
- alphanumeric: Recognizes one or more numerical and alphabetic characters: 0-9a-zA-Z
- anychar:
- begin:
- crlf:
- digit: Recognizes one or more numerical characters: 0-9
- double: Recognizes floating point number in a byte string and returns a f64
- double_s: Recognizes floating point number in a string and returns a f64
- eol:
- float: Recognizes floating point number in a byte string and returns a f32
- float_s: Recognizes floating point number in a string and returns a f32
- hex_digit: Recognizes one or more hexadecimal numerical characters: 0-9, A-F, a-f
- hex_u32: Recognizes a hex-encoded integer
- line_ending: Recognizes an end of line (both '\n' and "\r\n")
- multispace: Recognizes one or more spaces, tabs, carriage returns and line feeds
- newline: Matches a newline character '\n'
- non_empty: Recognizes non empty buffers
- not_line_ending:
- oct_digit: Recognizes one or more octal characters: 0-7
- rest: Return the remaining input.
- rest_s: Return the remaining input, for strings.
- shift:
- sized_buffer:
- space: Recognizes one or more spaces and tabs
- tab: Matches a tab character '\t'
- tag_cl:
