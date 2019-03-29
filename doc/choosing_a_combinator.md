
# List of parsers and combinators

This is an overview of the parsers and functions included in Nom. For the full list refer to the [documentation](https://docs.rs/nom/4.2.3/nom/#macros). The words combinator and macro will be used interchangeably, as combinators are always implemented as macros.

## Basic elements

Basic elements are used to recognize the lowest level elements of your grammar, like "here is a dot", or "here is a big-endian integer".

| Combinator | Usage | Input | Output | Comment |
|---|---|---|---|---|
| [char](https://docs.rs/nom/4.0.0/nom/macro.char.html) | `char!('a')` |  `"abc"` | <code>Ok(("bc",&nbsp;'a'))</code>| Matches one character (works with non-ASCII chars too). | 
| [is_a](https://docs.rs/nom/4.0.0/nom/macro.is_a.html) | ` is_a!("ab")` |  `"ababc"` | <code>Ok(("c",&nbsp;"abab"))</code>| Matches a sequence of any of the characters in the given string. |
| [is_not](https://docs.rs/nom/4.0.0/nom/macro.is_not.html) | `is_not!("cd")` |  `"ababc"` | <code>Ok(("c",&nbsp;"abab"))</code>| Matches a sequence characters not contained in the given string. |
| [one_of](https://docs.rs/nom/4.0.0/nom/macro.one_of.html) | `one_of!("abc")` |  `"abc"` | <code>Ok(("bc",&nbsp;'a'))</code>| Matches one of the provided characters (works with non-ASCII characters too). |
| [none_of](https://docs.rs/nom/4.0.0/nom/macro.none_of.html) | `none_of!("abc")` |  `"xyab"` | <code>Ok(("yab",&nbsp;'x'))</code>| Matches anything but the provided characters. |
| [tag](https://docs.rs/nom/4.0.0/nom/macro.tag.html) | `tag!("hello")` |  `"hello world"` | <code>Ok(("&nbsp;world",&nbsp;"hello"))</code>| Matches a specific suite of characters or bytes. |
| [tag_no_case](https://docs.rs/nom/4.0.0/nom/macro.tag_no_case.html) | `tag_no_case!( "hello")` |  `"HeLLo World"` | <code>Ok(("&nbsp;World",&nbsp;"HeLLo"))</code> | Case insensitive comparison. Note that case insensitive comparison is not well defined for unicode, and that you might have bad surprises. |
| [take](https://docs.rs/nom/4.0.0/nom/macro.take.html) | `take!(4)` |  `"hello"` | <code>Ok(("o",&nbsp;"hell"))</code>| Takes a specific number of bytes or characters|
| [take_while](https://docs.rs/nom/4.0.0/nom/macro.take_while.html) | `take_while!( is_alphabetic)` |  `"abc123"` | <code>Ok(("123",&nbsp;"abc"))</code> | Returns the longest list of bytes for which the provided function returns true. |
| [take_till](https://docs.rs/nom/4.0.0/nom/macro.take_till.html) | `take_till!( is_alphabetic)` |  `"123abc"` | <code>Ok(("abc",&nbsp;"123))</code> | Returns the longest list of bytes or characters until the provided function returns true. Equivalent to `take_while!(\|c\| !f(c))`. |
| [take_until](https://docs.rs/nom/4.0.0/nom/macro.take_until.html) | `take_until!( "world")` |  `"Hello world"` | <code>Ok(("world",&nbsp;"Hello&nbsp;"))</code> | Returns the longest list of bytes or characters until the provided tag is found. |
| [take_until_ and_consume](https://docs.rs/nom/4.0.0/nom/macro.take_until_and_consume.html) | `take_until_ and_consume!( "world")` |  `"Hello world!"` | <code>Ok(("!",&nbsp;"Hello&nbsp;"))</code>| Same as `take_until` but consumes the tag. |
| [take_until_either](https://docs.rs/nom/4.0.0/nom/macro.take_until_either.html) | `take_until_either!( "abc")` | `"long wait"` | <code>Ok(("ait",&nbsp;"long&nbsp;w"))</code> | Returns the longest list of bytes until any of the provided characters are found|
| [take_until_either_ and_consume](https://docs.rs/nom/4.0.0/nom/macro.take_until_either_and_consume.html) | `take_until_either!( "abc")` | `"long wait"` | <code>Ok(("it",&nbsp;"long&nbsp;w"))</code> | Same as `take_until_either`, but consumes the terminating character. |
| [value](https://docs.rs/nom/4.0.0/nom/macro.value.html) | <code>value!(42, tag!("abcd"))</code> | `"abcdef"` | <code>Ok(("ef",&nbsp;42))</code>| Replaces the result of the child parser with the provided value. Can also be used without a child parser. `value!(42)` would return the `42` value without consuming the input. |

Parsers that consume arbitrarily many bytes (`take_while`, `take_till`, `take_until`, etc.) usually have a version that requires a non-empty match, i.e. they have to return at least one character/byte to match. These versions are suffixed with a "1" (read as "at least _one_"), e.g. `take_while1` is the same as `take_while`, except that it must return at least one character.

_Example_ (non-empty matchers)

| Combinator | Input | Output |
|---|---|---|
| `take_while!(is_alphabetic)` | `"abc123"` | <code>Ok(("123",&nbsp;"abc"))</code> |
|   | `"123"` | <code>Ok(("123",&nbsp;""))</code> |
| `take_while1!(is_alphabetic)` | `"abc123"` | <code>Ok(("123",&nbsp;"abc"))</code> |
|   | `"123"` | <code>Err(Error(error_position!("123",&nbsp;TakeWhile1)))</code> |

## Choice combinators

| Combinator | Usage | Input | Output | Comment |
|---|---|---|---|---|
| [alt](https://docs.rs/nom/4.0.0/nom/macro.alt.html) | <code>alt!(tag!("ab")&nbsp;\|&nbsp;tag!("cd"))</code> | `"cdef"` | <code>Ok(("ef",&nbsp;"cd"))</code>| Try a list of parsers and return the result of the first successful one. |
| [switch](https://docs.rs/nom/4.0.0/nom/macro.switch.html) | <code>switch!(take!(2), &nbsp;&nbsp;"ab"&nbsp;=>&nbsp;tag!("XYZ")&nbsp;\| &nbsp;&nbsp;"cd"&nbsp;=>&nbsp;tag!("123"))</code> | `"cd1234"` | <code>Ok(("4",&nbsp;"123"))</code>| Choose the next parser depending on the result of the first one, if successful, and returns the result of the second parser. |
| [permutation](https://docs.rs/nom/4.0.0/nom/macro.permutation.html) | <code>permutation!( &nbsp;&nbsp;tag!("ab"),&nbsp;tag!("cd"),&nbsp;tag!("12"))</code> | `"cd12abc"` | <code>Ok( ("c", ("ab",&nbsp;"cd",&nbsp;"12") )</code>| Succeeds when all its child parser have succeeded, whatever the order. |

## Sequence combinators

| Combinator | Usage | Input | Output | Comment |
|---|---|---|---|---|
| [delimited](https://docs.rs/nom/4.0.0/nom/macro.delimited.html) | <code>delimited!( char!('('),&nbsp;take(2), char!(')') )</code> | `"(ab)cd"` | <code>Ok(("cd",&nbsp;"ab") )</code>| Returns an enclosed result and consumes the enclosing characters. |
| [preceded](https://docs.rs/nom/4.0.0/nom/macro.preceded.html) | `preceded!(tag!("ab"), tag!("XY"))` | `"abXYZ"` | <code>Ok(("Z",&nbsp;"XY"))</code> | Returns the second result only if it is preceded by the first. |
| [terminated](https://docs.rs/nom/4.0.0/nom/macro.terminated.html) | `terminated!(tag!("ab"), tag!("XY"))` | `"abXYZ"` | <code>Ok(("Z",&nbsp;"ab"))</code> | Returns the first result only if it is terminated by the second. |
| [pair](https://docs.rs/nom/4.0.0/nom/macro.pair.html) | `pair!(tag!("ab"), tag!("XY"))` |  `"abXYZ"` | <code>Ok(("Z", ("ab",&nbsp;"XY")))</code> | Chains two child parsers. The result is a tuple containing each subresult. |
| [separated_pair](https://docs.rs/nom/4.0.0/nom/macro.separated_pair.html) | <code>separated_pair!( tag!("hello"),&nbsp;char!(','), tag!("world") )</code> |  `"hello,world!"` | <code>Ok( ("!", ("hello",&nbsp;"world")) )` | Returns the first and last child parsers when separated by the second one. The separator is consumed. |
| [tuple](https://docs.rs/nom/4.0.0/nom/macro.tuple.html) | <code>tuple!( tag!("ab"),&nbsp;tag!("XY"), take!(1) )</code> | `"abXYZ!"` | <code>Ok( ("!", ("ab",&nbsp;"XY",&nbsp;"Z")) )</code> | Chains parsers and assemble the sub results in a tuple. This works a `pair`, but you can use as many child parsers as you can put elements in a tuple. |
| [do_parse](https://docs.rs/nom/4.0.0/nom/macro.do_parse.html) | <code>do_parse!( tag:&nbsp;take!(2)&nbsp;>> length:&nbsp;be_u8&nbsp;>> data:&nbsp;take!(length)&nbsp;>> (Buffer&nbsp;{&nbsp;tag: tag, data: data}) )</code> |  `&[0, 0, 3, 1, 2, 3][..]` | `Buffer { tag: &[0, 0][..], data: &[1, 2, 3][..] }`| Applies sub parsers in a sequence. it can store intermediary results and make them available for later parsers. |

## Applying a parser multiple times

| Combinator | Usage | Input | Output | Comment |
|---|---|---|---|---|
| [count](https://docs.rs/nom/4.0.0/nom/macro.count.html) | <code>count!( take!(2),&nbsp;3 )</code> |  `"abcdefgh"` | <code>Ok( ("gh", vec!("ab",&nbsp;"cd", "ef")) )</code>| Applies the child parser a specified number of times. |
| [count_fixed](https://docs.rs/nom/4.0.0/nom/macro.count_fixed.html) | `count_fixed!( &[u8], take!(2), 3 )` |  `"abcdefgh"` | <code>Ok( ("gh", \["ab",&nbsp;"cd", "ef"\]) )</code>| Applies the child parser a fixed number of times and returns a fixed size array. The type must be specified and it must be `Copy`. |
| [many0](https://docs.rs/nom/4.0.0/nom/macro.many0.html) | `many0!( tag!("ab") )` |  `"abababc"` | <code>Ok( ("c", vec!("ab",&nbsp;"ab", "ab")) )</code>| Applies the parser zero or more times and returns the list of results in a vector. `many1` does the same operation but must return at least one element. |
| [many_m_n](https://docs.rs/nom/4.0.0/nom/macro.many_m_n.html) | <code>many_m_n!( 1,&nbsp;3, tag!("ab") )</code> |  `"ababc"` | <code>Ok( ("c", vec!("ab",&nbsp;"ab")) )</code>| Applies the parser between _m_ and _n_ times (_n_ included) and returns the list of results in a vector. |
| [many_till](https://docs.rs/nom/4.0.0/nom/macro.many_till.html) | <code>many_till!( tag!("ab"),&nbsp;tag!("ef") )</code> |  `"ababefg"` | <code>Ok( ("g", (vec!("ab",&nbsp;"ab"), "ef")) )</code>| Applies the first parser until the second applies. Returns a tuple containing the list of results from the first in a vector and the result of the second. |
| [separated_list](https://docs.rs/nom/4.0.0/nom/macro.separated_list.html) | <code>separated_list!( tag!(","),&nbsp;tag!("ab") )</code> |  `"ab,ab,ab."` | <code>Ok( (".", vec!("ab",&nbsp;"ab",&nbsp;"ab")) )</code>| Works like `separated_list` but must return at least one element. |
| [fold_many0](https://docs.rs/nom/4.0.0/nom/macro.fold_many0.html) | <code>fold_many0!( be_u8,&nbsp;0, \|acc,&nbsp;item\|&nbsp;acc&nbsp;+&nbsp;item )</code> |  `[1, 2, 3]` | <code>Ok( ([],&nbsp;6) )</code>| Applies the parser zero or more times and folds the list of return values. The `fold_many1` version must apply the child parser at least one time. |
| [fold_many_m_n](https://docs.rs/nom/4.0.0/nom/macro.fold_many_m_n.html) | <code>fold_many_m_n!( 1,&nbsp;2, be_u8, 0, \|acc,&nbsp;item\| acc + item )</code> |  `[1, 2, 3]` | <code>Ok( ([3],&nbsp;3) )</code>| Applies the parser between _m_ and _n_ times (_n_ included) and folds the list of return value. |
| [length_count](https://docs.rs/nom/4.0.0/nom/macro.length_count.html) | `length_count!( number, tag!("ab") )` |  `"2ababab"` | <code>Ok( ("ab", vec!("ab",&nbsp;"ab")) )</code>| Gets a number from the first parser, then applies the second parser that many times. |

## Integers

Parsing integers from binary formats can be done in two ways: with parser functions, or combinators with configurable endianness.

### _Variable endianness (macros)_

`i16!`, `i32!`, `i64!`, `u16!`, `u32!`, `u64!` are combinators that take as argument a `nom::Endianness` (e.g. `i16!(endianness)`). If the parameter is `nom::Endianness::Big`, a big-endian integer is parsed. Otherwise a little-endian integer is parsed.

### _Fixed endianness (functions)_

The functions are prefixed by "be_" for big-endian numbers, and by "le_" for little-endian numbers, and the suffix is the type they parse to. As an example, `be_u32` parses a big-endian unsigned integer stored in 32 bits.

- signed integers
  - big-endian: `be_i8`, `be_i16`, `be_i32`, `be_i24`, `be_i32`, `be_i64`
  - little-endian: `le_i8`, `le_i16`, `le_i32`, `le_i24`, `le_i32`, `le_i64`
- unsigned integers
  - big-endian: `be_u8`, `be_u16`, `be_u32`, `be_u24`, `be_u32`, `be_u64`
  - little-endian: `le_u8`, `le_u16`, `le_u32`, `le_u24`, `le_u32`, `le_u64`
- floating point numbers
  - big-endian: `be_f32`, `be_f64`
  - little-endian: `le_f32`, `le_f64`

## Streaming related

- [`eof!`](https://docs.rs/nom/4.0.0/nom/macro.eof.html): returns its input if it is at the end of input data.
- [`complete!`](https://docs.rs/nom/4.0.0/nom/macro.complete.html): replaces a `Incomplete` returned by the child parser with an `Error`.
- [`alt_complete!`](https://docs.rs/nom/4.0.0/nom/macro.alt_complete.html): equivalent to the `alt!` combinator, except that it will not return `Incomplete` when one of the constituting parsers returns `Incomplete`. Instead, it will try the next alternative in the chain.
- [`separated_list_complete!`](https://docs.rs/nom/4.0.0/nom/macro.separated_list_complete.html): equivalent to the `separated_list!` combinator, except that it will return Error when either the separator or element subparser returns `Incomplete`.
- [`separated_nonempty_list_complete!`](https://docs.rs/nom/4.0.0/nom/macro.separated_nonempty_list_complete.html): equivalent to the `separated_nonempty_list!` combinator, except that it will return `Error` when either the separator or element subparser returns `Incomplete`.

## Modifiers

Most of these are especially useful when used within a `do_parse!` block.

- [`cond!`](https://docs.rs/nom/4.0.0/nom/macro.cond.html): wraps another parser and calls it if the condition is met. This combinator returns an `Option` of the return type of the child parser. If the subparser returns an `Err(nom::Err::Error(_))`, then a `OK((a, None))` is returned, where `a` is the unchanged input.
- [`cond_reduce!`](https://docs.rs/nom/4.0.0/nom/macro.cond_reduce.html): same as `cond!`, but returns an error if the condition is false.
- [`cond_with_error!`](https://docs.rs/nom/4.0.0/nom/macro.cond_with_error.html): same as `cond!`, but an error from the subparser is propagated.
- [`expr_opt!`](https://docs.rs/nom/4.0.0/nom/macro.expr_opt.html): evaluates an expression that returns an `Option` and returns a `IResult::Ok` if it receives a `Result::Some`, otherwise an error.
- [`expr_res!`](https://docs.rs/nom/4.0.0/nom/macro.expr_res.html): evaluates an expression that returns a `Result` and returns a `IResult::Ok` if it receives a `Result::Ok`, otherwise an error.
- [`flat_map!`](https://docs.rs/nom/4.0.0/nom/macro.flat_map.html): chains multiple parsers. Like `tuple!`, but does not return any intermediate result.
- [`map!`](https://docs.rs/nom/4.0.0/nom/macro.map.html): maps a function on the result of a parser.
- [`map_opt!`](https://docs.rs/nom/4.0.0/nom/macro.map_opt.html): maps a function returning an `Option` on the output of a parser.
- [`map_res!`](https://docs.rs/nom/4.0.0/nom/macro.map_res.html): maps a function returning a `Result` on the output of a parser.
- [`map_res_err!`](https://docs.rs/nom/4.0.0/nom/macro.map_res_err.html): maps a function returning a Result on the output of a parser, preserving the returned error.
- [`not!`](https://docs.rs/nom/4.0.0/nom/macro.not.html): returns a result only if the embedded parser returns `Error` or `Incomplete` does not consume the input.
- [`opt!`](https://docs.rs/nom/4.0.0/nom/macro.opt.html): make the underlying parser optional.
- [`opt_res!`](https://docs.rs/nom/4.0.0/nom/macro.opt_res.html): make the underlying parser optional.
- [`parse_to!`](https://docs.rs/nom/4.0.0/nom/macro.parse_to.html): uses the parse method from `std::str::FromStr` to convert the current input to the specified type.
- [`peek!`](https://docs.rs/nom/4.0.0/nom/macro.peek.html): returns a result without consuming the input.
- [`recognize!`](https://docs.rs/nom/4.0.0/nom/macro.recognize.html): if the child parser was successful, return the consumed input as produced value.
- [`return_error!`](https://docs.rs/nom/4.0.0/nom/macro.return_error.html): prevents backtracking if the child parser fails.
- [`tap!`](https://docs.rs/nom/4.0.0/nom/macro.tap.html): allows access to the parser's result without consuming it.
- [`verify!`](https://docs.rs/nom/4.0.0/nom/macro.verify.html): returns the result of the child parser if it satisfies a verification function.

## Error management and debugging

- [`add_return_error!`](https://docs.rs/nom/4.0.0/nom/macro.add_return_error.html): adds an error if the child parser fails.
- [`dbg!`](https://docs.rs/nom/4.0.0/nom/macro.dbg.html): prints a message if the parser fails.
- [`dbg_dmp!`](https://docs.rs/nom/4.0.0/nom/macro.dbg_dmp.html): prints a message and the input if the parser fails.
- [`error_node_position!`](https://docs.rs/nom/4.0.0/nom/macro.error_node_position.html): creates a parse error from a `nom::ErrorKind`, the position in the input and the next error in the parsing tree. if "verbose-errors" is not activated, it default to only the error code.
- [`error_position!`](https://docs.rs/nom/4.0.0/nom/macro.error_position.html): creates a parse error from a `nom::ErrorKind` and the position in the input if "verbose-errors" is not activated, it default to only the error code.
- [`fix_error!`](https://docs.rs/nom/4.0.0/nom/macro.fix_error.html): translates the parser result from `IResult` to `IResult` with a custom type.

## Text parsing

- [`escaped!`](https://docs.rs/nom/4.0.0/nom/macro.escaped.html): matches a byte string with escaped characters.
- [`escaped_transform!`](https://docs.rs/nom/4.0.0/nom/macro.escaped_transform.html): matches a byte string with escaped characters, and returns a new string with the escaped characters replaced

## Binary format parsing
- [`length_data!`](https://docs.rs/nom/4.0.0/nom/macro.length_data.html) or [`length_bytes!`](https://docs.rs/nom/4.0.0/nom/macro.length_bytes.html): gets a number from the first parser, than takes a subslice of the input of that size, and returns that subslice.
- [`length_value!`](https://docs.rs/nom/4.0.0/nom/macro.length_value.html): gets a number from the first parser, takes a subslice of the input of that size, then applies the second parser on that subslice. If the second parser returns `Incomplete`, it will return an error.

## Bit stream parsing

- [`bits!`](https://docs.rs/nom/4.0.0/nom/macro.bits.html): transforms the current input type (byte slice `&[u8]`) to a bit stream on which bit specific parsers and more general combinators can be applied.
- [`bytes!`](https://docs.rs/nom/4.0.0/nom/macro.bytes.html): transforms its bits stream input back into a byte slice for the underlying parsers.
- [`tag_bits!`](https://docs.rs/nom/4.0.0/nom/macro.tag_bits.html): matches an integer pattern to a bitstream. The number of bits of the input to compare must be specified.
- [`take_bits!`](https://docs.rs/nom/4.0.0/nom/macro.take_bits.html): generates a parser consuming the specified number of bits.
- [`ws!`](https://docs.rs/nom/4.0.0/nom/macro.ws.html): used to ignore whitespaces (' ', '\t', '\r', '\n').

## Other combinators

- [`apply!`](https://docs.rs/nom/4.0.0/nom/macro.apply.html): emulate function currying: `apply!(my_function, arg1, arg2, ...)` becomes `my_function(input, arg1, arg2, ...)`.
- [`apply_m!`](https://docs.rs/nom/4.0.0/nom/macro.apply_m.html): emulate function currying for method calls on structs `apply_m!(self.my_function, arg1, arg2, ...)` becomes `self.my_function(input, arg1, arg2, ...)`.
- [`call!`](https://docs.rs/nom/4.0.0/nom/macro.call.html): used to wrap common expressions and function as macros.
- [`call_m!`](https://docs.rs/nom/4.0.0/nom/macro.call_m.html): used to called methods then move self back into self.
- [`closure!`](https://docs.rs/nom/4.0.0/nom/macro.closure.html): wraps a parser in a closure.
- [`method!`](https://docs.rs/nom/4.0.0/nom/macro.method.html): makes a method from a parser combination.
- [`named!`](https://docs.rs/nom/4.0.0/nom/macro.named.html): makes a function from a parser combination.
- [`named_args!`](https://docs.rs/nom/4.0.0/nom/macro.named_args.html): makes a function from a parser combination with arguments.
- [`named_attr!`](https://docs.rs/nom/4.0.0/nom/macro.named_attr.html): makes a function from a parser combination, with attributes.
- [`try_parse!`](https://docs.rs/nom/4.0.0/nom/macro.try_parse.html): like `std::try!`, this macro will return the remaining input and parsed value if the child parser returned `Ok`, and will do an early return for `Error` and `Incomplete`. To be used as an alternative to `do_parse!`.
- For building custom separator parsers
  - [`eat_separator!`](https://docs.rs/nom/4.0.0/nom/macro.eat_separator.html): helper macros to build a separator parser.
  - [`sep!`](https://docs.rs/nom/4.0.0/nom/macro.sep.html): sep is the parser rewriting macro for whitespace separated formats.
  - [`wrap_sep!`](https://docs.rs/nom/4.0.0/nom/macro.wrap_sep.html):

## Character test functions

These functions are to be used as the argument of a combinator like, for instance, `take_while!`.

- [`is_alphabetic`](https://docs.rs/nom/4.0.0/nom/fn.is_alphabetic.html): tests if byte is ASCII alphabetic: A-Z, a-z.
- [`is_alphanumeric`](https://docs.rs/nom/4.0.0/nom/fn.is_alphanumeric.html): tests if byte is ASCII alphanumeric: A-Z, a-z, 0-9.
- [`is_digit`](https://docs.rs/nom/4.0.0/nom/fn.is_digit.html): tests if byte is ASCII digit: 0-9.
- [`is_hex_digit`](https://docs.rs/nom/4.0.0/nom/fn.is_hex_digit.html): tests if byte is ASCII hex digit: 0-9, A-F, a-f.
- [`is_oct_digit`](https://docs.rs/nom/4.0.0/nom/fn.is_oct_digit.html): tests if byte is ASCII octal digit: 0-7.
- [`is_space`](https://docs.rs/nom/4.0.0/nom/fn.is_space.html): tests if byte is ASCII space or tab.

## Other functions

- [`alpha`](https://docs.rs/nom/4.0.0/nom/fn.alpha.html): recognizes one or more lowercase and uppercase alphabetic characters: a-z, A-Z.
- [`alphanumeric`](https://docs.rs/nom/4.0.0/nom/fn.alphanumeric.html): recognizes one or more numerical and alphabetic characters: 0-9, a-z, A-Z.
- [`anychar`](https://docs.rs/nom/4.0.0/nom/fn.anychar.html): matches one byte as a character.
- [`begin`](https://docs.rs/nom/4.0.0/nom/fn.begin.html): returns a `IResult` with the unchanged input, e.g. `Ok(((), input))`.
- [`crlf`](https://docs.rs/nom/4.0.0/nom/fn.crlf.html): tests for the sequence "\r\n".
- [`digit`](https://docs.rs/nom/4.0.0/nom/fn.digit.html): recognizes one or more numerical characters: 0-9.
- [`double`](https://docs.rs/nom/4.0.0/nom/fn.double.html): recognizes floating point number in a byte string and returns a f64.
- [`double_s`](https://docs.rs/nom/4.0.0/nom/fn.double_s.html): recognizes floating point number in a string and returns a f64.
- [`eol`](https://docs.rs/nom/4.0.0/nom/fn.eol.html): matches an end of line (analogous to `eol!` combinator).
- [`float`](https://docs.rs/nom/4.0.0/nom/fn.float.html): recognizes floating point number in a byte string and returns a f32.
- [`float_s`](https://docs.rs/nom/4.0.0/nom/fn.float_s.html): recognizes floating point number in a string and returns a f32.
- [`hex_digit`](https://docs.rs/nom/4.0.0/nom/fn.hex_digit.html): recognizes one or more hexadecimal numerical characters: 0-9, A-F, a-f.
- [`hex_u32`](https://docs.rs/nom/4.0.0/nom/fn.hex_u32.html): recognizes a hex-encoded integer.
- [`line_ending`](https://docs.rs/nom/4.0.0/nom/fn.line_ending.html), [`not_line_ending`](https://docs.rs/nom/4.0.0/nom/fn.not_line_ending.html): recognizes an end of line (both '\n' and "\r\n").
- [`multispace`](https://docs.rs/nom/4.0.0/nom/fn.multispace.html): recognizes one or more spaces, tabs, carriage returns and line feeds.
- [`newline`](https://docs.rs/nom/4.0.0/nom/fn.newline.html): matches a newline character '\n'.
- [`non_empty`](https://docs.rs/nom/4.0.0/nom/fn.non_empty.html): recognizes non empty buffers.
- [`oct_digit`](https://docs.rs/nom/4.0.0/nom/fn.oct_digit.html): recognizes one or more octal characters: 0-7.
- [`rest`](https://docs.rs/nom/4.0.0/nom/fn.rest.html): return the remaining input.
- [`rest_s`](https://docs.rs/nom/4.0.0/nom/fn.rest_s.html): return the remaining input, for strings.
- [`sized_buffer`](https://docs.rs/nom/4.0.0/nom/fn.sized_buffer.html): in a sequence of bytes, it interprets the first element as the number of bytes to take from the following sequence. For example `sized_buffer(&[2, 0, 1, 2, 3])` delivers `Ok(([2, 3], [0, 1]))`.
- [`space`](https://docs.rs/nom/4.0.0/nom/fn.space.html): recognizes one or more spaces and tabs.
- [`tab`](https://docs.rs/nom/4.0.0/nom/fn.tab.html): matches a tab character '\t'.
- [`tag_cl`](https://docs.rs/nom/4.0.0/nom/fn.tag_cl.html): closure version of `tag!`.
