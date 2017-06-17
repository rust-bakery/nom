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
//!
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
