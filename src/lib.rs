//! # nom, eating data byte by byte
//!
//! nom is a parser combinator library with a focus on safe parsing,
//! streaming patterns, and as much as possible zero copy.
//!
//! ## Example
//!
//! ```rust
//! #[macro_use]
//! extern crate nom;
//!
//! #[derive(Debug,PartialEq)]
//! pub struct Color {
//!   pub red:     u8,
//!   pub green:   u8,
//!   pub blue:    u8,
//! }
//!
//! fn from_hex(input: &str) -> Result<u8, std::num::ParseIntError> {
//!   u8::from_str_radix(input, 16)
//! }
//!
//! fn is_hex_digit(c: char) -> bool {
//!   let c = c as u8;
//!   (c >= 0x30 && c <= 0x39) || (c >= 0x41 && c <= 0x46) || (c >= 0x61 && c <= 0x66)
//! }
//!
//! named!(hex_primary<&str, u8>,
//!   map_res!(dbg_dmp!(take_while_m_n!(2, 2, is_hex_digit)), from_hex)
//! );
//!
//! named!(hex_color<&str, Color>,
//!   do_parse!(
//!            tag!("#")   >>
//!     red:   hex_primary >>
//!     green: hex_primary >>
//!     blue:  hex_primary >>
//!     (Color { red, green, blue })
//!   )
//! );
//!
//! fn main() {
//!   assert_eq!(hex_color("#2F14DF"), Ok(("", Color {
//!     red: 47,
//!     green: 20,
//!     blue: 223,
//!   })));
//! }
//! ```
//!
//! The code is available on [Github](https://github.com/Geal/nom)
//!
//! There are a few [guides](https://github.com/Geal/nom/tree/master/doc) with more details
//! about [the design of nom](https://github.com/Geal/nom/blob/master/doc/how_nom_macros_work.md),
//! [how to write parsers](https://github.com/Geal/nom/blob/master/doc/making_a_new_parser_from_scratch.md),
//! or the [error management system](https://github.com/Geal/nom/blob/master/doc/error_management.md).
//!
//! **Looking for a specific combinator? Read the
//! ["choose a combinator" guide](https://github.com/Geal/nom/blob/master/doc/choosing_a_combinator.md)**
//!
//! If you are upgrading to nom 2.0, please read the
//! [migration document](https://github.com/Geal/nom/blob/master/doc/upgrading_to_nom_2.md).
//!
//! If you are upgrading to nom 4.0, please read the
//! [migration document](https://github.com/Geal/nom/blob/master/doc/upgrading_to_nom_4.md).
//!
//! See also the [FAQ](https://github.com/Geal/nom/blob/master/doc/FAQ.md).
//!
//! ## Parser combinators
//!
//! Parser combinators are an approach to parsers that is very different from software like [lex](https://en.wikipedia.org/wiki/Lex_(software)) and [yacc](https://en.wikipedia.org/wiki/Yacc). Instead of writing the grammar in a separate file and generating the corresponding code, you use very small functions with very specific purpose, like "take 5 bytes", or "recognize the word 'HTTP'", and assemble then in meaningful patterns like "recognize 'HTTP', then a space, then a version".
//! The resulting code is small, and looks like the grammar you would have written with other parser approaches.
//!
//! This has a few advantages:
//!
//! - the parsers are small and easy to write
//! - the parsers components are easy to reuse (if they're general enough, please add them to nom!)
//! - the parsers components are easy to test separately (unit tests and property-based tests)
//! - the parser combination code looks close to the grammar you would have written
//! - you can build partial parsers, specific to the data you need at the moment, and ignore the rest
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
//! Here is an example of one such parser, to recognize text between parentheses:
//! 
//! ```rust
//! #[macro_use]
//! extern crate nom;
//! 
//! named!(parens, delimited!(char!('('), is_not!(")"), char!(')')));
//! ```
//! 
//! It defines a function named `parens`, which will recognize a sequence of the character `(`, the longest byte array not containing `)`, then the character `)`, and will return the byte array in the middle.
//! 
//! Here is another parser, written without using nom's macros this time:
//! 
//! ```rust
//! #[macro_use]
//! extern crate nom;
//! 
//! use nom::{IResult,Err,Needed};
//! 
//! fn take4(i:&[u8]) -> IResult<&[u8], &[u8]>{
//!   if i.len() < 4 {
//!     Err(Err::Incomplete(Needed::Size(4)))
//!   } else {
//!     Ok((&i[4..],&i[0..4]))
//!   }
//! }
//! ```
//! 
//! This function takes a byte array as input, and tries to consume 4 bytes. With macros, you would write it like this:
//! 
//! ```rust
//! #[macro_use]
//! extern crate nom;
//! 
//! named!(take4, take!(4));
//! ```
//! //! A parser in nom is a function which, for an input type `I`, an output type `O` and an optional error type `E`, will have the following signature:
//! 
//! ```rust
//! fn parser(input: I) -> IResult<I, O, E>;
//! ```
//! 
//! Or like this, if you don't want to specify a custom error type (it will be `u32` by default):
//! 
//! ```rust
//! fn parser(input: I) -> IResult<I, O>;
//! ```
//! 
//! `IResult` is an alias for the `Result` type:
//! 
//! ```rust
//! use nom::{Needed, Context};
//! 
//! type IResult<I, O, E = u32> = Result<(I, O), Err<I, E>>;
//! 
//! enum Err<I, E = u32> {
//!   Incomplete(Needed),
//!   Error(Context<I, E>),
//!   Failure(Context<I, E>),
//! }
//! ```
//! 
//! It can have the following values:
//! 
//! - a correct result `Ok((I,O))` with the first element being the remaining of the input (not parsed yet), and the second the output value;
//! - an error `Err(Err::Error(c))` with `c` an enum that contians an error code with its position in the input, and optionally a chain of accumulated errors;
//! - an error `Err(Err::Incomplete(Needed))` indicating that more input is necessary. `Needed` can indicate how much data is needed
//! - an error `Err(Err::Failure(c))`. It works like the `Error` case, except it indicates an unrecoverable error: we cannot backtrack and test another parser
//! 
//! There is already a large list of basic parsers available, like:
//! 
//! - **`length_value`**: a byte indicating the size of the following buffer
//! - **`not_line_ending`**: returning as much data as possible until a line ending (\r or \n) is found
//! - **`line_ending`**: matches a line ending
//! - **`alpha`**: will return the longest alphabetical array from the beginning of the input
//! - **`digit`**: will return the longest numerical array from the beginning of the input
//! - **`alphanumeric`**: will return the longest alphanumeric array from the beginning of the input
//! - **`space`**: will return the longest array containing only spaces
//! - **`multispace`**: will return the longest array containing space, \r or \n
//! - **`be_u8`**, **`be_u16`**, **`be_u32`**, **`be_u64`** to parse big endian unsigned integers of multiple sizes
//! - **`be_i8`**, **`be_i16`**, **`be_i32`**, **`be_i64`** to parse big endian signed integers of multiple sizes
//! - **`be_f32`**, **`be_f64`** to parse big endian floating point numbers
//! - **`eof`**: a parser that is successful only if the input is over. In any other case, it returns an error.
//! 
//! Please refer to the [documentation][doc] for an exhaustive list of parsers.
//! 
//! #### Making new parsers with macros
//! 
//! Macros are the main way to make new parsers by combining other ones. Those macros accept other macros or function names as arguments. You then need to make a function out of that combinator with **`named!`**, or a closure with **`closure!`**. Here is how you would do, with the **`tag!`** and **`take!`** combinators:
//! 
//! ```rust
//! named!(abcd_parser, tag!("abcd")); // will consume bytes if the input begins with "abcd"
//! 
//! 
//! named!(take_10, take!(10));        // will consume and return 10 bytes of input
//! ```
//! 
//! The **`named!`** macro can take three different syntaxes:
//! 
//! ```rust
//! named!(my_function( &[u8] ) -> &[u8], tag!("abcd"));
//! 
//! named!(my_function<&[u8], &[u8]>, tag!("abcd"));
//! 
//! named!(my_function, tag!("abcd")); // when you know the parser takes &[u8] as input, and returns &[u8] as output
//! ```
//! 
//! **IMPORTANT NOTE**: Rust's macros can be very sensitive to the syntax, so you may encounter an error compiling parsers like this one:
//! 
//! ```rust
//! named!(my_function<&[u8], Vec<&[u8]>>, many0!(tag!("abcd")));
//! ```
//! 
//! You will get the following error: "error: expected an item keyword". This happens because `>>` is seen as an operator, so the macro parser does not recognize what we want. There is a way to avoid it, by inserting a space:
//! 
//! ```rust
//! named!(my_function<&[u8], Vec<&[u8]> >, many0!(tag!("abcd")));
//! ```
//! 
//! This will compile correctly. I am very sorry for this inconvenience.
//! 
//! #### Common combinators
//! 
//! Here are the basic macros available:
//! 
//! - **`tag!`**: will match the byte array provided as argument
//! - **`is_not!`**: will match the longest array not containing any of the bytes of the array provided to the macro
//! - **`is_a!`**: will match the longest array containing only bytes of the array provided to the macro
//! - **`take_while!`**: will walk the whole array and apply the closure to each suffix until the function fails
//! - **`take!`**: will take as many bytes as the number provided
//! - **`take_until!`**: will take as many bytes as possible until it encounters the provided byte array, and will leave it in the remaining input
//! - **`take_until_and_consume!`**: will take as many bytes as possible until it encounters the provided byte array, and will skip it
//! - **`take_until_either_and_consume!`**: will take as many bytes as possible until it encounters one of the bytes of the provided array, and will skip it
//! - **`take_until_either!`**: will take as many bytes as possible until it encounters one of the bytes of the provided array, and will leave it in the remaining input
//! - **`map!`**: applies a function to the output of a `IResult` and puts the result in the output of a `IResult` with the same remaining input
//! - **`flat_map!`**: applies a parser to the output of a `IResult` and returns a new `IResult` with the same remaining input.
//! - **`map_opt!`**: applies a function returning an Option to the output of `IResult`, returns `Done(input, o)` if the result is `Some(o)`, or `Error(0)`
//! - **`map_res!`**: applies a function returning a Result to the output of `IResult`, returns `Done(input, o)` if the result is `Ok(o)`, or `Error(0)`
//! 
//! Please refer to the [documentation][doc] for an exhaustive list of combinators.
//! 
//! #### Combining parsers
//! 
//! There are more high level patterns, like the **`alt!`** combinator, which provides a choice between multiple parsers. If one branch fails, it tries the next, and returns the result of the first parser that succeeds:
//! 
//! ```rust
//! named!(alt_tags, alt!(tag!("abcd") | tag!("efgh")));
//! 
//! assert_eq!(alt_tags(b"abcdxxx"), Done(&b"xxx"[..], &b"abcd"[..]));
//! assert_eq!(alt_tags(b"efghxxx"), Done(&b"xxx"[..], &b"efgh"[..]));
//! assert_eq!(alt_tags(b"ijklxxx"), Error(Position(Alt, &b"ijklxxx"[..])));
//! ```
//! 
//! The pipe `|` character is used as separator.
//! 
//! The **`opt!`** combinator makes a parser optional. If the child parser returns an error, **`opt!`** will succeed and return None:
//! 
//! ```rust
//! named!( abcd_opt< &[u8], Option<&[u8]> >, opt!( tag!("abcd") ) );
//! 
//! assert_eq!(abcd_opt(b"abcdxxx"), Done(&b"xxx"[..], Some(&b"abcd"[..])));
//! assert_eq!(abcd_opt(b"efghxxx"), Done(&b"efghxxx"[..], None));
//! ```
//! 
//! **`many0!`** applies a parser 0 or more times, and returns a vector of the aggregated results:
//! 
//! ```rust
//! use std::str;
//! named!(multi< Vec<&str> >, many0!( map_res!(tag!( "abcd" ), str::from_utf8) ) );
//! let a = b"abcdef";
//! let b = b"abcdabcdef";
//! let c = b"azerty";
//! assert_eq!(multi(a), Done(&b"ef"[..],     vec!["abcd"]));
//! assert_eq!(multi(b), Done(&b"ef"[..],     vec!["abcd", "abcd"]));
//! assert_eq!(multi(c), Done(&b"azerty"[..], Vec::new()));
//! ```
//! 
//! Here are some basic combining macros available:
//! 
//! - **`opt!`**: will make the parser optional (if it returns the `O` type, the new parser returns `Option<O>`)
//! - **`many0!`**: will apply the parser 0 or more times (if it returns the `O` type, the new parser returns `Vec<O>`)
//! - **`many1!`**: will apply the parser 1 or more times
//! 
//! Please refer to the [documentation][doc] for an exhaustive list of combinators.
//! 
//! There are more complex (and more useful) parsers like `do_parse!` and `tuple!`, which are used to apply a series of parsers then assemble their results.
//! 
//! Example with `tuple!`:
//! 
//! ```rust
//! named!(tpl<&[u8], (u16, &[u8], &[u8]) >,
//!   tuple!(
//!     be_u16 ,
//!     take!(3),
//!     tag!("fg")
//!   )
//! );
//! 
//! assert_eq!(
//!   tpl(&b"abcdefgh"[..]),
//!   Done(
//!     &b"h"[..],
//!     (0x6162u16, &b"cde"[..], &b"fg"[..])
//!   )
//! );
//! assert_eq!(tpl(&b"abcde"[..]), Incomplete(Needed::Size(7)));
//! let input = &b"abcdejk"[..];
//! assert_eq!(tpl(input), Error(Position(ErrorKind::Tag, &input[5..])));
//! ```
//! 
//! Example with `do_parse!`:
//! 
//! ```rust
//! #[derive(Debug, PartialEq)]
//! struct A {
//!   a: u8,
//!   b: u8
//! }
//! 
//! fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) }
//! fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) }
//! 
//! named!(f<&[u8],A>,
//!   do_parse!(    // the parser takes a byte array as input, and returns an A struct
//!     tag!("abcd")       >>      // begins with "abcd"
//!     opt!(tag!("abcd")) >>      // this is an optional parser
//!     aa: ret_int1       >>      // the return value of ret_int1, if it does not fail, will be stored in aa
//!     tag!("efgh")       >>
//!     bb: ret_int2       >>
//!     tag!("efgh")       >>
//! 
//!     (A{a: aa, b: bb})          // the final tuple will be able to use the variable defined previously
//!   )
//! );
//! 
//! let r = f(b"abcdabcdefghefghX");
//! assert_eq!(r, Done(&b"X"[..], A{a: 1, b: 2}));
//! 
//! let r2 = f(b"abcdefghefghX");
//! assert_eq!(r2, Done(&b"X"[..], A{a: 1, b: 2}));
//! ```
//! 
//! The double right arrow `>>` is used as separator between every parser in the sequence, and the last closure can see the variables storing the result of parsers. Unless the specified return type is already a tuple, the final line should be that type wrapped in a tuple.
//! 
//! More examples of [`do_parse!`](http://rust.unhandledexpression.com/nom/macro.do_parse.html) and [`tuple!`](http://rust.unhandledexpression.com/nom/macro.tuple.html) usage can be found in the [INI file parser example](tests/ini.rs).
//! 
//! ## nom parser design
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
//! # use nom::{Context,Needed};
//! # fn main() {}
//! pub type IResult<I,O,E=u32> = Result<(I,O), Err<I,E>>;
//!
//! pub enum Err<I,E=u32> {
//!   Incomplete(Needed),
//!   Error(Context<I,E>),
//!   Failure(Context<I,E>),
//! }
//! ```
//!
//! What it means:
//!
//! * `Ok((i,o))` means the parser was successful. `i` is the remaining part of the input
//!   (called *remainder*), `o` is the correctly parsed value
//! The remaining part can then be used as input for other parsers called in a sequence
//! * `Err(Err::Error(e))` indicates the parser encountered an error. The `Context<I,E>` type is an enum of possible parser errors,
//! that can also contain a custom error that you'd specify, by redefining the `E` error type
//! * `Err(Err::Failure(e))` indicates the parser encountered an error that we cannot recover from (to prevent `alt` and other
//! combinators from trying alternatives. The `Context<I,E>` type is an enum of possible parser errors, that can also contain
//! a custom error that you'd specify, by redefining the `E` error type
//! * `Err(Err::Incomplete(i))` means the parser did not have enough information to decide, and tells you, if possible,
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
//!    Err(Err::Incomplete(Needed::Size(1)))
//!  } else {
//!    if input[0] == 'a' as u8 {
//!      // the first part of the returned value is the remaining slice
//!      Ok((&input[1..], 'a'))
//!    } else {
//!      Err(Err::Error(error_position!(input, ErrorKind::Custom(42))))
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
//! #  assert_eq!(hello(b"Hello nom."), Ok((&b"."[..], &b"nom"[..])));
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
//! #  assert_eq!(hello(b"Hello nom."), Ok((&b"."[..], &b"nom"[..])));
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
//! a specific series of bytes or characters. `alpha` is a function that recognizes alphabetical characters.
//! The `preceded!` combinator assembles them in a more complex parser: if both parsers are successful,
//! it returns the result of the second one (`alpha` is preceded by `tag!`).
//!
//! *Note* : combinators can assemble other combinators (macros), or parser functions, as long as they follow
//! the same interface. Here, `alpha` is a parser function already implemented in nom.
//!
//!
#![cfg_attr(not(feature = "std"), feature(alloc))]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(test))]
#![cfg_attr(feature = "nightly", feature(const_fn))]
#![cfg_attr(feature = "nightly", feature(plugin))]
//#![warn(missing_docs)]

#![cfg_attr(feature = "cargo-clippy", allow(doc_markdown))]

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;
#[cfg(feature = "regexp")]
extern crate regex;
#[cfg(feature = "regexp_macros")]
#[macro_use]
extern crate lazy_static;
extern crate memchr;
#[cfg(feature = "nightly")]
extern crate test;

#[cfg(not(feature = "std"))]
mod std {
  #[macro_use]
  pub use alloc::{boxed, vec, string};
  pub use core::{fmt, cmp, iter, option, result, ops, slice, str, mem, convert};
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
pub use self::str::*;

#[macro_use]
mod util;
mod traits;

#[cfg(feature = "verbose-errors")]
#[macro_use]
pub mod verbose_errors;

#[cfg(not(feature = "verbose-errors"))]
#[macro_use]
pub mod simple_errors;

#[macro_use]
mod internal;
#[macro_use]
mod macros;
#[macro_use]
mod branch;
#[macro_use]
mod sequence;
#[macro_use]
mod multi;
#[macro_use]
pub mod methods;

#[macro_use]
mod bytes;
#[macro_use]
pub mod bits;

#[macro_use]
mod character;
#[macro_use]
mod nom;

#[macro_use]
pub mod whitespace;

#[cfg(feature = "regexp")]
#[macro_use]
mod regexp;

mod str;

pub mod types;
