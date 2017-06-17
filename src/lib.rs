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
//! * char	matches one character: `char!(char) => &[u8] -> IResult<&[u8], char>
//! * eof	eof!(i) returns i if it is at the end of input data
//! * i16	if the parameter is nom::Endianness::Big, parse a big endian i16 integer, otherwise a little endian i16 integer
//! * i32	if the parameter is nom::Endianness::Big, parse a big endian i32 integer, otherwise a little endian i32 integer
//! * i64	if the parameter is nom::Endianness::Big, parse a big endian i64 integer, otherwise a little endian i64 integer
//! * u16	if the parameter is nom::Endianness::Big, parse a big endian u16 integer, otherwise a little endian u16 integer
//! * u32	if the parameter is nom::Endianness::Big, parse a big endian u32 integer, otherwise a little endian u32 integer
//! * u64	if the parameter is nom::Endianness::Big, parse a big endian u64 integer, otherwise a little endian u64 integer
//! * is_a	is_a!(&[T]) => &[T] -> IResult<&[T], &[T]> returns the longest list of bytes that appear in the provided array
//! * is_a_s	is_a_s!(&str) => &str -> IResult<&str, &str> returns the longest list of characters that appear in the provided array
//! * is_not	is_not!(&[T:AsBytes]) => &[T] -> IResult<&[T], &[T]> returns the longest list of bytes that do not appear in the provided array
//! * is_not_s	is_not_s!(&str) => &str -> IResult<&str, &str> returns the longest list of characters that do not appear in the provided array
//! * none_of	matches anything but the provided characters
//! * one_of	matches one of the provided characters
//! * tag	tag!(&[T]: nom::AsBytes) => &[T] -> IResult<&[T], &[T]> declares a byte array as a suite to recognize
//! * tag_no_case	tag_no_case!(&[T]) => &[T] -> IResult<&[T], &[T]> declares a case insensitive ascii string as a suite to recognize
//! * tag_no_case_s	tag_no_case_s!(&str) => &str -> IResult<&str, &str> declares a case-insensitive string as a suite to recognize
//! * tag_s	tag_s!(&str) => &str -> IResult<&str, &str> declares a string as a suite to recognize
//! * take	take!(nb) => &[T] -> IResult<&[T], &[T]> generates a parser consuming the specified number of bytes
//! * take_s	take_s!(nb) => &str -> IResult<&str, &str> generates a parser consuming the specified number of characters
//! * take_str	take!(nb) => &[T] -> IResult<&[T], &str> same as take! but returning a &str
//! * take_till	take_till!(T -> bool) => &[T] -> IResult<&[T], &[T]> returns the longest list of bytes until the provided function succeeds
//! * take_till1	take_till1!(T -> bool) => &[T] -> IResult<&[T], &[T]> returns the longest non empty list of bytes until the provided function succeeds
//! * take_till1_s	take_till1_s!(char -> bool) => &str -> IResult<&str, &str> returns the longest non empty list of characters until the provided function succeeds
//! * take_till_s	take_till_s!(char -> bool) => &str -> IResult<&str, &str> returns the longest list of characters until the provided function succeeds
//! * take_until	take_until!(tag) => &[T] -> IResult<&[T], &[T]> consumes data until it finds the specified tag
//! * take_until1	take_until1!(tag) => &[T] -> IResult<&[T], &[T]> consumes data until it finds the specified tag
//! * take_until_and_consume	take_until_and_consume!(tag) => &[T] -> IResult<&[T], &[T]> generates a parser consuming bytes until the specified byte sequence is found, and consumes it
//! * take_until_and_consume1	take_until_and_consume1!(tag) => &[T] -> IResult<&[T], &[T]> generates a parser consuming bytes (at least 1) until the specified byte sequence is found, and consumes it
//! * take_until_and_consume_s	take_until_and_consume_s!(&str) => &str -> IResult<&str, &str> generates a parser consuming all chars until the specified string is found and consumes it
//! * take_until_either	take_until_either!(tag) => &[T] -> IResult<&[T], &[T]>
//! * take_until_either_and_consume	take_until_either_and_consume!(tag) => &[T] -> IResult<&[T], &[T]> consumes data until it finds any of the specified characters, and consume it
//! * take_until_s	take_until_s!(&str) => &str -> IResult<&str, &str> generates a parser consuming all chars until the specified string is found and leaves it in the remaining input
//! * take_while	take_while!(T -> bool) => &[T] -> IResult<&[T], &[T]> returns the longest list of bytes until the provided function fails.
//! * take_while1	take_while1!(T -> bool) => &[T] -> IResult<&[T], &[T]> returns the longest (non empty) list of bytes until the provided function fails.
//! * take_while1_s	take_while1_s!(char -> bool) => &str -> IResult<&str, &str> returns the longest (non empty) list of characters until the provided function fails.
//! * take_while_s	take_while_s!(char -> bool) => &str -> IResult<&str, &str> returns the longest list of characters until the provided function fails.
//! * value	value!(T, R -> IResult<R, S> ) => R -> IResult<R, T>
//!
//! ## Modifiers
//!
//! * complete	replaces a Incomplete returned by the child parser with an Error
//! * cond	cond!(bool, I -> IResult<I,O>) => I -> IResult<I, Option<O>> Conditional combinator
//! * cond_reduce	cond_reduce!(bool, I -> IResult<I,O>) => I -> IResult<I, O> Conditional combinator with error
//! * cond_with_error	cond_with_error!(bool, I -> IResult<I,O>) => I -> IResult<I, Option<O>> Conditional combinator
//! * consumer_from_parser	
//! * expr_opt	expr_opt!(Option<O>) => I -> IResult<I, O> evaluate an expression that returns a Option and returns a IResult::Done(I,T) if Some
//! * expr_res	expr_res!(Result<E,O>) => I -> IResult<I, O> evaluate an expression that returns a Result and returns a IResult::Done(I,T) if Ok
//! * flat_map	flat_map!(R -> IResult<R,S>, S -> IResult<S,T>) => R -> IResult<R, T>
//! * map	map!(I -> IResult<I,O>, O -> P) => I -> IResult<I, P> maps a function on the result of a parser
//! * map_opt	map_opt!(I -> IResult<I,O>, O -> Option<P>) => I -> IResult<I, P> maps a function returning an Option on the output of a parser
//! * map_res	map_res!(I -> IResult<I,O>, O -> Result<P>) => I -> IResult<I, P> maps a function returning a Result on the output of a parser
//! * not	not!(I -> IResult<I,O>) => I -> IResult<I, O> returns a result only if the embedded parser returns Error or Incomplete does not consume the input
//! * opt	opt!(I -> IResult<I,O>) => I -> IResult<I, Option<O>> make the underlying parser optional
//! * opt_res	opt_res!(I -> IResult<I,O>) => I -> IResult<I, Result<nom::Err,O>> make the underlying parser optional
//! * parse_to	parse_to!(O) => I -> IResult<I, O> uses the parse method from std::str::FromStr to convert the current input to the specified type
//! * peek	peek!(I -> IResult<I,O>) => I -> IResult<I, O> returns a result without consuming the input
//! * recognize	recognize!(I -> IResult<I, O> ) => I -> IResult<I, I> if the child parser was successful, return the consumed input as produced value
//! * return_error	Prevents backtracking if the child parser fails
//! * tap	tap!(name: I -> IResult<I,O> => { block }) => I -> IResult<I, O> allows access to the parser's result without affecting it
//! * verify	verify!(I -> IResult<I,O>, O -> bool) => I -> IResult<I, O> returns the result of the child parser if it satisfies a verifcation function
//!
//! ## Error management and debugging
//!
//! * add_return_error	Add an error if the child parser fails
//! * dbg	Prints a message if the parser fails
//! * dbg_dmp	Prints a message and the input if the parser fails
//! * error_code	creates a parse error from a nom::ErrorKind
//! * error_node	creates a parse error from a nom::ErrorKind and the next error in the parsing tree. if "verbose-errors" is not activated, it default to only the error code
//! * error_node_position	creates a parse error from a nom::ErrorKind, the position in the input and the next error in the parsing tree. if "verbose-errors" is not activated, it default to only the error code
//! * error_position	creates a parse error from a nom::ErrorKind and the position in the input if "verbose-errors" is not activated, it default to only the error code
//! * fix_error	translate parser result from IResult to IResult with a custom type
//!
//! ## Choice combinators
//!
//! * alt	Try a list of parsers and return the result of the first successful one
//! * alt_complete	Is equivalent to the alt! combinator, except that it will not return Incomplete when one of the constituting parsers returns Incomplete. Instead, it will try the next alternative in the chain.
//! * switch	switch!(I -> IResult<I,P>, P => I -> IResult<I,O> | ... | P => I -> IResult<I,O> ) => I -> IResult<I, O> choose the next parser depending on the result of the first one, if successful, and returns the result of the second parser
//!
//! # Sequence combinators
//!
//! * delimited	delimited!(I -> IResult<I,T>, I -> IResult<I,O>, I -> IResult<I,U>) => I -> IResult<I, O> delimited(opening, X, closing) returns X
//! * do_parse	do_parse!(I->IResult<I,A> >> I->IResult<I,B> >> ... I->IResult<I,X> , ( O ) ) => I -> IResult<I, O> do_parse applies sub parsers in a sequence. it can store intermediary results and make them available for later parsers
//! * pair	pair!(I -> IResult<I,O>, I -> IResult<I,P>) => I -> IResult<I, (O,P)> pair(X,Y), returns (x,y)
//! * permutation	permutation!(I -> IResult<I,A>, I -> IResult<I,B>, ... I -> IResult<I,X> ) => I -> IResult<I, (A,B,...X)> applies its sub parsers in a sequence, but independent from their order this parser will only succeed if all of its sub parsers succeed
//! * preceded	preceded!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, O> preceded(opening, X) returns X
//! * separated_pair	separated_pair!(I -> IResult<I,O>, I -> IResult<I, T>, I -> IResult<I,P>) => I -> IResult<I, (O,P)> separated_pair(X,sep,Y) returns (x,y)
//! * terminated	terminated!(I -> IResult<I,O>, I -> IResult<I,T>) => I -> IResult<I, O> terminated(X, closing) returns X
//! * tuple	tuple!(I->IResult<I,A>, I->IResult<I,B>, ... I->IResult<I,X>) => I -> IResult<I, (A, B, ..., X)> chains parsers and assemble the sub results in a tuple.
//!
//! ## Applying a parser multiple times
//!
//! * count	count!(I -> IResult<I,O>, nb) => I -> IResult<I, Vec<O>> Applies the child parser a specified number of times
//! * count_fixed	count_fixed!(O, I -> IResult<I,O>, nb) => I -> IResult<I, [O; nb]> Applies the child parser a fixed number of times and returns a fixed size array The type must be specified and it must be Copy
//! * fold_many0	fold_many0!(I -> IResult<I,O>, R, Fn(R, O) -> R) => I -> IResult<I, R> Applies the parser 0 or more times and folds the list of return values
//! * fold_many1	fold_many1!(I -> IResult<I,O>, R, Fn(R, O) -> R) => I -> IResult<I, R> Applies the parser 1 or more times and folds the list of return values
//! * fold_many_m_n	fold_many_m_n!(usize, usize, I -> IResult<I,O>, R, Fn(R, O) -> R) => I -> IResult<I, R> Applies the parser between m and n times (n included) and folds the list of return value
//! * length_count	length_count!(I -> IResult<I, nb>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>> gets a number from the first parser, then applies the second parser that many times
//! * many0	many0!(I -> IResult<I,O>) => I -> IResult<I, Vec<O>> Applies the parser 0 or more times and returns the list of results in a Vec
//! * many1	many1!(I -> IResult<I,O>) => I -> IResult<I, Vec<O>> Applies the parser 1 or more times and returns the list of results in a Vec
//! * many_m_n	many_m_n!(usize, usize, I -> IResult<I,O>) => I -> IResult<I, Vec<O>> Applies the parser between m and n times (n included) and returns the list of results in a Vec
//! * many_till	many_till!(I -> IResult<I,O>, I -> IResult<I,P>) => I -> IResult<I, (Vec<O>, P)> Applies the first parser until the second applies. Returns a tuple containing the list of results from the first in a Vec and the result of the second.
//! * separated_list	separated_list!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>> separated_list(sep, X) returns Vec will return Incomplete if there may be more elements
//! * separated_list_complete	separated_list_complete!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>> This is equivalent to the separated_list! combinator, except that it will return Error when either the separator or element subparser returns Incomplete.
//! * separated_nonempty_list	separated_nonempty_list!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>> separated_nonempty_list(sep, X) returns Vec will return Incomplete if there may be more elements
//! * separated_nonempty_list_complete	separated_nonempty_list_complete!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>> This is equivalent to the separated_nonempty_list! combinator, except that it will return Error when either the separator or element subparser returns Incomplete.
//!
//! ## Text parsing
//!
//! * escaped	escaped!(&[T] -> IResult<&[T], &[T]>, T, &[T] -> IResult<&[T], &[T]>) => &[T] -> IResult<&[T], &[T]> matches a byte string with escaped characters.
//! * escaped_transform	escaped_transform!(&[T] -> IResult<&[T], &[T]>, T, &[T] -> IResult<&[T], &[T]>) => &[T] -> IResult<&[T], Vec<T>> matches a byte string with escaped characters.
//!
//! ## Binary format parsing
//!
//! * length_bytes	length_bytes!(&[T] -> IResult<&[T], nb>) => &[T] -> IResult<&[T], &[T]> Gets a number from the first parser, then extracts that many bytes from the remaining stream
//! * length_data	length_data!(I -> IResult<I, nb>) => O
//! * length_value	length_value!(I -> IResult<I, nb>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>> gets a number from the first parser, takes a subslice of the input of that size, then applies the second parser on that subslice. If the second parser returns Incomplete, length_value will return an error
//!
//! ## Bit stream parsing
//!
//! * bits	bits!( parser ) => ( &[u8], (&[u8], usize) -> IResult<(&[u8], usize), T> ) -> IResult<&[u8], T> transforms its byte slice input into a bit stream for the underlying parsers
//! * tag_bits	matches an integer pattern to a bitstream. The number of bits of the input to compare must be specified
//! * take_bits	take_bits!(type, nb) => ( (&[T], usize), U, usize) -> IResult<(&[T], usize), U> generates a parser consuming the specified number of bits.
//!
//! ## Whitespace delimited formats parsing
//!
//! * eat_separator	helper macros to build a separator parser
//! * sep	sep is the parser rewriting macro for whitespace separated formats
//! * wrap_sep	
//! * ws
//!
//! ## Remaining combinators
//!
//! * apply	emulate function currying: apply!(my_function, arg1, arg2, ...) becomes my_function(input, arg1, arg2, ...)
//! * apply_m	emulate function currying for method calls on structs apply_m!(self.my_function, arg1, arg2, ...) becomes self.my_function(input, arg1, arg2, ...)
//! * call	Used to wrap common expressions and function as macros
//! * call_m	Used to called methods then move self back into self
//! * closure	Wraps a parser in a closure
//! * method	Makes a method from a parser combination
//! * named	Makes a function from a parser combination
//! * named_args	Makes a function from a parser combination with arguments.
//! * named_attr	Makes a function from a parser combination, with attributes
//! * try_parse	A bit like std::try!, this macro will return the remaining input and parsed value if the child parser returned Done, and will do an early return for Error and Incomplete this can provide more flexibility than do_parse! if needed
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
