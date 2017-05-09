//! nom, eating data byte by byte
//!
//! nom is a parser combinator library with a focus on safe parsing,
//! streaming patterns, and as much as possible zero copy.
//!
//! The code is available on [Github](https://github.com/Geal/nom)
//!
//! There are a few [guides](home.html) with more details
//! about [the design of nom](how_nom_macros_work.html),
//! [how to write parsers](making_a_new_parser_from_scratch.html),
//! or the [error management system](error_management.html).
//!
//! If you are upgrading to nom 2.0, please read the
//! [migration document](upgrading_to_nom_2.html).
//!
//! See also the [FAQ](FAQ.html).
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
//#![warn(missing_docs)]

#[cfg(not(feature = "std"))]
extern crate collections;
#[cfg(feature = "regexp")]
extern crate regex;
#[cfg(feature = "regexp_macros")]
#[macro_use] extern crate lazy_static;
#[cfg(feature = "nightly")]
extern crate test;

#[cfg(not(feature = "std"))]
mod std {
#[macro_use]
  pub use core::{fmt, cmp, iter, option, result, ops, slice, str, mem};
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
