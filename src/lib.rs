//! nom, eating data byte by byte
//!
//! nom is a parser combinator library with a focus on safe parsing,
//! streaming patterns, and as much as possible zero copy.
//!
//! The code is available on [Github](https://github.com/Geal/nom)
//!
//! There are a few [guides](http://rust.unhandledexpression.com/nom/home.html) with more details
//! about [the design of nom](http://rust.unhandledexpression.com/nom/how_nom_macros_work.html),
//! [how to write parsers](http://rust.unhandledexpression.com/nom/making_a_new_parser_from_scratch.html),
//! or the [error management system](http://rust.unhandledexpression.com/nom/error_management.html).
//!
//! If you are upgrading to nom 2.0, please read the
//! [migration document](http://rust.unhandledexpression.com/nom/upgrading_to_nom_2.html).
//!
//! See also the [FAQ](http://rust.unhandledexpression.com/nom/FAQ.html).
//!
//! # What are parser combinators?
//!
//! Parser combinators are a way to build parsers out of small functions. instead of
//! writing a huge grammar file then generaing code, like you would do with lex and yacc,
//! you write small functions, to parse small things like a character, or a number,
//! and then you assemble them in larger and larger functions, that can parse larger
//! parts of your formats.
//!
//! You end up with a list of small functions that you can reuse everywhere you need. Each
//! of them can be unit tested anf fuzzed separately.
//!
//! # nom parser design
//!
//! All nom parsers follow the same convention. They are all functions with the following signature:
//!
//! ```ignore
//!  fn parser(input: I) -> IResult<I,O> { ... }
//! ```
//!
//! Here is the definition of that `IResult` type:
//!
//! ```
//! # #[macro_use] extern crate nom;
//! # use nom::{Err,Needed};
//! # fn main() {}
//! pub enum IResult<I,O,E=u32> {
//!   Done(I,O),
//!   Error(Err<E>), // indicates the parser encountered an error. E is a custom error type you can redefine
//!   /// Incomplete contains a Needed, an enum than can represent a known quantity of input data, or unknown
//!   Incomplete(Needed) // if the parser did not have enough data to decide
//! }
//! ```
//!
//! What it means:
//!
//! * `Done(i,o)` means the parser was successful. `i` is the remaining part of the input, `o` is the correctly parsed value
//! The remaining part can then be used as input for other parsers called in a sequence
//! * `Error(e)` indicates the parser encountered an error. The `Err<E>` type is an enum of possible parser errors,
//! that can also contain a custom error that you'd specify, by redefining the `E` error type
//! * `Incomplete(i)` means the parser did not have enough information to decide, and tells you, if possible,
//! how much data it needs
//!
//! That way, you could write your own parser that recognizes the letter 'a' like this:
//!
//! ```
//! #[macro_use] extern crate nom;
//! use nom::{IResult,Needed,Err,ErrorKind};
//! # fn main() {}
//!
//! fn a(input: &[u8]) -> IResult<&[u8], char> {
//!  // if there is not enough data, we return Ìncomplete
//!  if input.len() == 0 {
//!    IResult::Incomplete(Needed::Size(1))
//!  } else {
//!    if input[0] == 'a' as u8 {
//!      // the first part of the returned value is the remaining slice
//!      IResult::Done(&input[1..], 'a')
//!    } else {
//!      IResult::Error(error_code!(ErrorKind::Custom(42)))
//!    }
//!  }
//! }
//! ```
//!
//! Writing all the parsers manually, like this, is dangerous, despite Rust's safety features. There
//! are still a lot of mistakes one can make. That's why nom provides a list of macros to help in
//! developing parsers. As an example, here is a parser that would recognize the phrase
//! "Hello <someone>" and return the name of the person we hail:
//!
//! ```
//! #[macro_use] extern crate nom;
//! use nom::alpha;
//!
//! named!(hello, preceded!(tag!("Hello "), alpha));
//! # use nom::IResult;
//! # fn main() {
//! #  assert_eq!(hello(b"Hello nom."), IResult::Done(&b"."[..], &b"nom"[..]));
//! # }
//! ```
//!
//! Let's deconstruct it:
//!
//! * `named!` generates a function with the correct type. Without `named` here, we could write the parser
//! as follows:
//!
//! ```
//! #[macro_use] extern crate nom;
//! use nom::{alpha,IResult};
//!
//! fn hello(input: &[u8]) -> IResult<&[u8], &[u8]> {
//!   preceded!(input,
//!     tag!("Hello "), alpha)
//! }
//! # fn main() {
//! #  assert_eq!(hello(b"Hello nom."), IResult::Done(&b"."[..], &b"nom"[..]));
//! # }
//! ```
//!
//! By default, `named` makes a function that takes `&[u8]` as input type, and returns `&[u8]` as output type.
//! You can override it like this:
//!
//! * `named!(hello<&str>, ...):` would take `&[u8]` as input type, and return `&str` as output type.
//! * `named!(hello<&str, &str>, ...):` would take `&str` as input type, and return `&str` as output type.
//!
//! *Note* : when we don't use `named!`, we must pass the input as first argument of the top
//! level combinator (see the line `preceded!(input,` in the preceding code example). This is a macro trick
//! in nom to pass input from one combinator to the next by rewriting the call.
//!
//! Next part of the parser: `preceded!(tag!("Hello "), alpha))`. Here, `tag!` is a combinator that recognizes
//! a specific serie of bytes or characters. `alpha` is a function that recognizes alphabetical characters.
//! The `preceded!` combinator assembles them in a more complex parser: if both parsers are successful,
//! it returns the result of the second one (`alpha` is preceded by `tag!`).
//!
//! *Note* : combinators can assemble other combinators (macros), or parser functions, as long as they follow
//! the same interface. Here, `alpha` is a parser function already implemented in nom.
//!
//! # List of parsers and combinators
//!
//! ## Basic elements
//!
//! Those are used to recognize the lowest level elements of your grammar, like, "here is a dot", or
//! "here is an big endian integer".
//!
//! * **char!**: matches one character: `char!('a')` will make a parser that recognizes the letter 'a' (works with non ASCII chars too)
//! * **eof!**: `eof!()` returns its input if it is at the end of input data
//! * **is_a!, is_a_s!**: matches a sequence of any of the characters passed as arguments. `is_a!("ab1")` could recognize `ababa` or `1bb`. `is_a_s!` is a legacy combinator, it does exactly the same thing as `is_a`
//! * **is_not!, is_not_s!**: matches a sequence of none of the characters passed as arguments
//! * **one_of!**: matches one of the provided characters. `one_of!("abc")` could recognize 'a', 'b', or 'c'. It also works with non ASCII characters
//! * **none_of!**: matches anything but the provided characters
//! * **tag!, tag_s!**: recognizes a specific suite of characters or bytes. `tag!("hello")` matches "hello"
//! * **tag_no_case!**: recognizes a suite of ASCII characters, case insensitive. `tag_no_case!("hello")` could match "hello", "Hello" or even "HeLlO"
//! * **tag_no_case_s!** works like `tag_no_case` but on UTF-8 characters too (uses `&str` as input). Note that case insensitive comparison is not well defined for unicode, and that you might have bad surprises. Also, this combinator allocates a new string for the comparison. Ponder for a bit before using this combinator
//! * **take!, take_s!**: takes a specific number of bytes or characters. `take!(5)` would return "hello" from the string "hello world"
//! * **take_str!**: same as `take!` but returning a `&str`
//! * **take_till!, take_till_s!**: returns the longest list of bytes until the provided function succeeds. `take_till!(is_alphabetic)` with input "123abc" would return "123"
//! * **take_till1!, take_till1_s!**: same as `take_till!`, but the result must not be empty: `take_till1!(is_alphabetic)` would fail on "abc"
//! * **take_until!, take_until_s!**: returns the longest list of bytes until the provided tag is found. `take_until!("world")` with input "Hello world!" would return "Hello " and leave "world!" as remaining input
//! * **take_until1!**: same as `take_until!`, but cannot return an empty result
//! * **take_until_and_consume!, take_until_and_consume_s!**: same as `take_until!` but consumes the tag. `take_until_and_consume!("world")` with input "Hello world!" would return "Hello " and leave "!" as remaining input
//! * **take_until_and_consume1!**: same as `take_until_and_consume!`, but cannot return an empty result
//! * **take_until_either!**: returns the longest list of bytes until any of the provided characters are found
//! * **take_until_either_and_consume!**: same as `take_until_either!`, but consumes the terminating character
//! * **take_while!, take_while_s!**: returns the longest list of bytes for which the function is true. `take_while!(is_alphabetic)` with input "abc123" would return "abc"
//! * **take_while1!, take_while1_s!**: same as `take_while!`, but cannot return an empty result
//! * **value!**: you can use `value!` to always return the same result value without consuming input, like this: `value!(42)`. Or you can replace the result of a child parser with a predefined value, like this: `value!(42, tag!("abcd"))` which would replace, if successful, the return value from "abcd", to 42
//!
//! Parsing integers from binary formats can be done in two ways: with parser functions, or combinators with configurable endianness:
//!
//! * configurable endianness: **i16!, i32!, i64!, u16!, u32!, u64!** are combinators that take as argument a `nom::Endianness`,
//! like this: `i16!(endianness)`. If the parameter is nom::Endianness::Big, parse a big endian i16 integer, otherwise a little endian i16 integer
//! * fixed endianness: the functions are prefixed by "be_" for big endian numbers, and by "le_" for little endian numbers, and the suffix is the type they parse to. As an example, "be_u32" parses a big endian unsigned integer stored in 32 bits.
//!   * **be_f32, be_f64, le_f32, le_f64**: recognize floating point numbers
//!   * **be_i8, be_i16, be_i32, be_i24, be_i32, be_i64**: big endian signed integers
//!   * **be_u8, be_u16, be_u32, be_u24, be_u32, be_u64**: big endian unsigned integers
//!   * **le_i8, le_i16, le_i32, le_i24, le_i32, le_i64**: little endian signed integers
//!   * **le_u8, le_u16, le_u32, le_u24, le_u32, le_u64**: little endian unsigned integers
//!
//! ## Modifiers
//!
//! * **complete!**: replaces a Incomplete returned by the child parser with an Error
//! * **cond!**: conditional combinator
//! * **cond_reduce!**: Conditional combinator with error
//! * **cond_with_error!**: Conditional combinator
//! * **expr_opt!**: evaluates an expression that returns a Option and returns a IResult::Done(I,T) if Some
//! * **expr_res!**: evaluates an expression that returns a Result and returns a IResult::Done(I,T) if Ok
//! * **flat_map!**:
//! * **map!**: maps a function on the result of a parser
//! * **map_opt!**: maps a function returning an Option on the output of a parser
//! * **map_res!**: maps a function returning a Result on the output of a parser
//! * **not!**: returns a result only if the embedded parser returns Error or Incomplete does not consume the input
//! * **opt!**: make the underlying parser optional
//! * **opt_res!**: make the underlying parser optional
//! * **parse_to!**: uses the parse method from std::str::FromStr to convert the current input to the specified type
//! * **peek!**: returns a result without consuming the input
//! * **recognize!**: if the child parser was successful, return the consumed input as produced value
//! * **return_error!**: prevents backtracking if the child parser fails
//! * **tap!**: allows access to the parser's result without affecting it
//! * **verify!**: returns the result of the child parser if it satisfies a verification function
//!
//! ## Error management and debugging
//!
//! * **add_return_error!**: Add an error if the child parser fails
//! * **dbg!**: Prints a message if the parser fails
//! * **dbg_dmp!**: Prints a message and the input if the parser fails
//! * **error_code!**: creates a parse error from a nom::ErrorKind
//! * **error_node!**: creates a parse error from a nom::ErrorKind and the next error in the parsing tree. if "verbose-errors" is not activated, it default to only the error code
//! * **error_node_position!**: creates a parse error from a nom::ErrorKind, the position in the input and the next error in the parsing tree. if "verbose-errors" is not activated, it default to only the error code
//! * **error_position!**: creates a parse error from a nom::ErrorKind and the position in the input if "verbose-errors" is not activated, it default to only the error code
//! * **fix_error!**: translate parser result from IResult to IResult with a custom type
//!
//! ## Choice combinators
//!
//! * **alt!**: try a list of parsers and return the result of the first successful one
//! * **alt_complete!**: is equivalent to the alt! combinator, except that it will not return Incomplete when one of the constituting parsers returns Incomplete. Instead, it will try the next alternative in the chain.
//! * **switch!**: choose the next parser depending on the result of the first one, if successful, and returns the result of the second parser
//!
//! # Sequence combinators
//!
//! * **delimited!**: delimited(opening, X, closing) returns X
//! * **do_parse!**: do_parse applies sub parsers in a sequence. it can store intermediary results and make them available for later parsers
//! * **pair!**: pair(X,Y), returns (x,y)
//! * **permutation!**: applies its sub parsers in a sequence, but independent from their order this parser will only succeed if all of its sub parsers succeed
//! * **preceded!**: preceded(opening, X) returns X
//! * **separated_pair!**: separated_pair(X,sep,Y) returns (x,y)
//! * **terminated!**: terminated(X, closing) returns X
//! * **tuple!**: chains parsers and assemble the sub results in a tuple.
//!
//! ## Applying a parser multiple times
//!
//! * **count!**: Applies the child parser a specified number of times
//! * **count_fixed!**: Applies the child parser a fixed number of times and returns a fixed size array The type must be specified and it must be Copy
//! * **fold_many0!**: Applies the parser 0 or more times and folds the list of return values
//! * **fold_many1!**: Applies the parser 1 or more times and folds the list of return values
//! * **fold_many_m_n!**: Applies the parser between m and n times (n included) and folds the list of return value
//! * **length_count!**: gets a number from the first parser, then applies the second parser that many times
//! * **many0!**: Applies the parser 0 or more times and returns the list of results in a Vec
//! * **many1!**: Applies the parser 1 or more times and returns the list of results in a Vec
//! * **many_m_n!**: Applies the parser between m and n times (n included) and returns the list of results in a Vec
//! * **many_till!**: Applies the first parser until the second applies. Returns a tuple containing the list of results from the first in a Vec and the result of the second.
//! * **separated_list!**: separated_list(sep, X) returns Vec will return Incomplete if there may be more elements
//! * **separated_list_complete!**: This is equivalent to the separated_list! combinator, except that it will return Error when either the separator or element subparser returns Incomplete.
//! * **separated_nonempty_list!**: separated_nonempty_list(sep, X) returns Vec will return Incomplete if there may be more elements
//! * **separated_nonempty_list_complete!**: This is equivalent to the separated_nonempty_list! combinator, except that it will return Error when either the separator or element subparser returns Incomplete.
//!
//! ## Text parsing
//!
//! * **escaped!**: matches a byte string with escaped characters.
//! * **escaped_transform!**: matches a byte string with escaped characters, and returns a new string with the escaped characters replaced
//!
//! ## Binary format parsing
//!
//! * **length_data!**: gets a number from the first parser, than takes a subslice of the input of that size, and returns that subslice
//! * **length_bytes!**: alias for `length_data`
//! * **length_value!**: gets a number from the first parser, takes a subslice of the input of that size, then applies the second parser on that subslice. If the second parser returns Incomplete, length_value will return an error
//!
//! ## Bit stream parsing
//!
//! * **bits!**: transforms the current input type (byte slice `&[u8]`) to a bit stream on which bit specific parsers and more general combinators can be applied
//! * **bytes!**: transforms its bits stream input back into a byte slice for the underlying parsers.
//! * **tag_bits!**: matches an integer pattern to a bitstream. The number of bits of the input to compare must be specified
//! * **take_bits!**: generates a parser consuming the specified number of bits
//!
//! ## Whitespace delimited formats parsing
//!
//! * **eat_separator!**: helper macros to build a separator parser
//! * **sep!**: sep is the parser rewriting macro for whitespace separated formats
//! * **wrap_sep!**:
//! * **ws!**:
//!
//! ## Remaining combinators
//!
//! * **apply!**: emulate function currying: apply!(my_function, arg1, arg2, ...) becomes my_function(input, arg1, arg2, ...)
//! * **apply_m!**: emulate function currying for method calls on structs apply_m!(self.my_function, arg1, arg2, ...) becomes self.my_function(input, arg1, arg2, ...)
//! * **call!**: Used to wrap common expressions and function as macros
//! * **call_m!**: Used to called methods then move self back into self
//! * **closure!**: Wraps a parser in a closure
//! * **method!**: Makes a method from a parser combination
//! * **named!**: Makes a function from a parser combination
//! * **named_args!**: Makes a function from a parser combination with arguments.
//! * **named_attr!**: Makes a function from a parser combination, with attributes
//! * **try_parse!**: A bit like std::try!, this macro will return the remaining input and parsed value if the child parser returned Done, and will do an early return for Error and Incomplete this can provide more flexibility than do_parse! if needed
//!
//! ## Character test functions
//!
//! use those functions with a combinator like `take_while!`:
//!
//! * **is_alphabetic**: Tests if byte is ASCII alphabetic: A-Z, a-z
//! * **is_alphanumeric**: Tests if byte is ASCII alphanumeric: A-Z, a-z, 0-9
//! * **is_digit**: Tests if byte is ASCII digit: 0-9
//! * **is_hex_digit**: Tests if byte is ASCII hex digit: 0-9, A-F, a-f
//! * **is_oct_digit**: Tests if byte is ASCII octal digit: 0-7
//! * **is_space**: Tests if byte is ASCII space or tab
//!
//! ## Remaining functions (sort those out in the other categories)
//!
//! * **alpha**: Recognizes one or more lowercase and uppercase alphabetic characters: a-zA-Z
//! * **alphanumeric**: Recognizes one or more numerical and alphabetic characters: 0-9a-zA-Z
//! * **anychar**: 
//! * **begin**: 
//! * **crlf**: 
//! * **digit**: Recognizes one or more numerical characters: 0-9
//! * **double**: Recognizes floating point number in a byte string and returns a f64
//! * **double_s**: Recognizes floating point number in a string and returns a f64
//! * **eol**: 
//! * **float**: Recognizes floating point number in a byte string and returns a f32
//! * **float_s**: Recognizes floating point number in a string and returns a f32
//! * **hex_digit**: Recognizes one or more hexadecimal numerical characters: 0-9, A-F, a-f
//! * **hex_u32**: Recognizes a hex-encoded integer
//! * **line_ending**: Recognizes an end of line (both '\n' and "\r\n")
//! * **multispace**: Recognizes one or more spaces, tabs, carriage returns and line feeds
//! * **newline**: Matches a newline character '\n'
//! * **non_empty**: Recognizes non empty buffers
//! * **not_line_ending**: 
//! * **oct_digit**: Recognizes one or more octal characters: 0-7
//! * **rest**: Return the remaining input.
//! * **rest_s**: Return the remaining input, for strings.
//! * **shift**: 
//! * **sized_buffer**: 
//! * **space**: Recognizes one or more spaces and tabs
//! * **tab**: Matches a tab character '\t'
//! * **tag_cl**: 
//!
//! # Example
//!
//! ```
//! #[macro_use]
//! extern crate nom;
//!
//! use nom::{IResult,digit};
//!
//! // Parser definition
//!
//! use std::str;
//! use std::str::FromStr;
//!
//! // We parse any expr surrounded by parens, ignoring all whitespaces around those
//! named!(parens<i64>, ws!(delimited!( tag!("("), expr, tag!(")") )) );
//!
//! // We transform an integer string into a i64, ignoring surrounding whitespaces
//! // We look for a digit suite, and try to convert it.
//! // If either str::from_utf8 or FromStr::from_str fail,
//! // we fallback to the parens parser defined above
//! named!(factor<i64>, alt!(
//!     map_res!(
//!       map_res!(
//!         ws!(digit),
//!         str::from_utf8
//!       ),
//!       FromStr::from_str
//!     )
//!   | parens
//!   )
//! );
//!
//! // We read an initial factor and for each time we find
//! // a * or / operator followed by another factor, we do
//! // the math by folding everything
//! named!(term <i64>, do_parse!(
//!     init: factor >>
//!     res:  fold_many0!(
//!         pair!(alt!(tag!("*") | tag!("/")), factor),
//!         init,
//!         |acc, (op, val): (&[u8], i64)| {
//!             if (op[0] as char) == '*' { acc * val } else { acc / val }
//!         }
//!     ) >>
//!     (res)
//!   )
//! );
//!
//! named!(expr <i64>, do_parse!(
//!     init: term >>
//!     res:  fold_many0!(
//!         pair!(alt!(tag!("+") | tag!("-")), term),
//!         init,
//!         |acc, (op, val): (&[u8], i64)| {
//!             if (op[0] as char) == '+' { acc + val } else { acc - val }
//!         }
//!     ) >>
//!     (res)
//!   )
//! );
//!
//! fn main() {
//!   assert_eq!(expr(b"1+2"),         IResult::Done(&b""[..], 3));
//!   assert_eq!(expr(b"12+6-4+3"),    IResult::Done(&b""[..], 17));
//!   assert_eq!(expr(b"1+2*3+4"),     IResult::Done(&b""[..], 11));
//!
//!   assert_eq!(expr(b"(2)"),         IResult::Done(&b""[..], 2));
//!   assert_eq!(expr(b"2*(3+4)"),     IResult::Done(&b""[..], 14));
//!   assert_eq!(expr(b"2*2/(5-1)+3"), IResult::Done(&b""[..], 4));
//! }
//! ```
#![cfg_attr(not(feature = "std"), feature(no_std))]
#![cfg_attr(not(feature = "std"), feature(collections))]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(test))]
#![cfg_attr(feature = "nightly", feature(const_fn))]
#![cfg_attr(feature = "nightly", feature(plugin))]
#![cfg_attr(feature = "nightly", plugin(compiler_error))]
//#![warn(missing_docs)]

#[cfg(not(feature = "std"))]
extern crate collections;
#[cfg(feature = "regexp")]
extern crate regex;
#[cfg(feature = "regexp_macros")]
#[macro_use] extern crate lazy_static;
extern crate memchr;
#[cfg(feature = "nightly")]
extern crate test;

#[cfg(not(feature = "nightly"))]
#[allow(unused_macros)]
#[macro_export]
macro_rules! compiler_error {
    ($e:expr) => {
      INVALID_NOM_SYNTAX_PLEASE_SEE_FAQ //https://github.com/Geal/nom/blob/master/doc/FAQ.md#using-nightly-to-get-better-error-messages
    }
}

#[cfg(not(feature = "std"))]
mod std {
#[macro_use]
  pub use core::{fmt, cmp, iter, option, result, ops, slice, str, mem, convert};
  pub use collections::{boxed, vec, string};
  pub mod prelude {
    pub use core::prelude as v1;
  }
}

pub use self::util::*;
pub use self::traits::*;

#[cfg(feature = "verbose-errors")]
pub use self::verbose_errors::*;

#[cfg(not(feature = "verbose-errors"))]
pub use self::simple_errors::*;

pub use self::internal::*;
pub use self::macros::*;
pub use self::branch::*;
pub use self::sequence::*;
pub use self::multi::*;
pub use self::methods::*;
pub use self::bytes::*;
pub use self::bits::*;

pub use self::nom::*;
pub use self::character::*;

pub use self::whitespace::*;

#[cfg(feature = "regexp")]
pub use self::regexp::*;

#[cfg(feature = "std")]
#[cfg(feature = "stream")]
pub use self::stream::*;

pub use self::str::*;

#[macro_use] mod util;
mod traits;

#[cfg(feature = "verbose-errors")] #[macro_use] pub mod verbose_errors;

#[cfg(not(feature = "verbose-errors"))] #[macro_use] pub mod simple_errors;

#[macro_use] mod internal;
#[macro_use] mod macros;
#[macro_use] mod branch;
#[macro_use] mod sequence;
#[macro_use] mod multi;
#[macro_use] pub mod methods;
#[macro_use] mod bytes;
#[macro_use] pub mod bits;

#[macro_use] mod nom;
#[macro_use] mod character;

#[macro_use]
pub mod whitespace;

#[cfg(feature = "regexp")]
#[macro_use] mod regexp;

#[macro_use]
#[cfg(feature = "std")]
#[cfg(feature = "stream")]
mod stream;

mod str;
