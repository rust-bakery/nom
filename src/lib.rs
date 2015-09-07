//! Nom, eating data byte by byte
//!
//! The goal is to make a parser combinator library that is safe,
//! supports streaming (push and pull), and as much as possible zero copy.
//!
//! The code is available on [Github](https://github.com/Geal/nom)
//!
//! # Example
//!
//! ```
//! #[macro_use]
//! extern crate nom;
//!
//! use nom::{IResult,digit,multispace};
//! use nom::IResult::*;
//!
//! // Parser definition
//!
//! use std::str;
//! use std::str::FromStr;
//!
//! named!(parens<i64>, delimited!(
//!     delimited!(opt!(multispace), tag!("("), opt!(multispace)),
//!     expr,
//!     delimited!(opt!(multispace), tag!(")"), opt!(multispace))
//!   )
//! );
//!
//! // We transform an integer string into a i64
//! // we look for a digit suite, and try to convert it.
//! // if either str::from_utf8 or FromStr::from_str fail,
//! // the parser will fail
//! named!(factor<i64>,
//!   alt!(
//!     map_res!(
//!       map_res!(
//!         delimited!(opt!(multispace), digit, opt!(multispace)),
//!         str::from_utf8
//!       ),
//!       FromStr::from_str
//!     )
//!   | parens
//!   )
//! );
//!
//! // we define acc as mutable to update its value whenever a new term is found
//! named!(term <i64>,
//!   chain!(
//!     mut acc: factor  ~
//!              many0!(
//!                alt!(
//!                  tap!(mul: preceded!(tag!("*"), factor) => acc = acc * mul) |
//!                  tap!(div: preceded!(tag!("/"), factor) => acc = acc / div)
//!                )
//!              ),
//!     || { return acc }
//!   )
//! );
//!
//! named!(expr <i64>,
//!   chain!(
//!     mut acc: term  ~
//!              many0!(
//!                alt!(
//!                  tap!(add: preceded!(tag!("+"), term) => acc = acc + add) |
//!                  tap!(sub: preceded!(tag!("-"), term) => acc = acc - sub)
//!                )
//!              ),
//!     || { return acc }
//!   )
//! );
//!
//! fn main() {
//!   assert_eq!(expr(&b" 1 +  2 "[..]),             IResult::Done(&b""[..], 3));
//!   assert_eq!(expr(&b" 12 + 6 - 4+  3"[..]),      IResult::Done(&b""[..], 17));
//!   assert_eq!(expr(&b" 1 + 2*3 + 4"[..]),         IResult::Done(&b""[..], 11));
//!
//!   assert_eq!(expr(&b" (  2 )"[..]),              IResult::Done(&b""[..], 2));
//!   assert_eq!(expr(&b" 2* (  3 + 4 ) "[..]),      IResult::Done(&b""[..], 14));
//!   assert_eq!(expr(&b"  2*2 / ( 5 - 1) + 3"[..]), IResult::Done(&b""[..], 4));
//! }
//! ```

#![cfg_attr(feature = "core", feature(no_std))]
#![cfg_attr(feature = "core", feature(core))]
#![cfg_attr(feature = "core", feature(collections))]
#![cfg_attr(feature = "core", no_std)]
#![cfg_attr(feature = "regexp_macros", feature(plugin))]
#![cfg_attr(feature = "regexp_macros", plugin(regex_macros))]

#[macro_use]
#[cfg(feature = "core")]
extern crate core;
#[cfg(feature = "core")]
extern crate collections;
#[cfg(feature = "regexp")]
extern crate regex;

#[cfg(feature = "core")]
mod std {
#[macro_use]
  pub use core::{fmt, iter, option, ops, slice, mem};
  pub use collections::{boxed, vec, string};
  pub mod prelude {
    pub use core::prelude as v1;
  }
}

pub use self::util::*;
pub use self::internal::*;//{IResult, IResultClosure, GetInput, GetOutput};
pub use self::macros::*;
pub use self::bytes::*;
pub use self::bits::*;
pub use self::accumulator::*;
#[cfg(not(feature = "core"))]
pub use self::producer::*;//{ProducerState,Producer,FileProducer,MemProducer};
#[cfg(not(feature = "core"))]
pub use self::consumer::*;//{ConsumerState,Consumer};

pub use self::nom::*;
pub use self::character::*;

#[cfg(feature = "regexp")]
pub use self::regexp::*;

#[macro_use] mod util;
mod internal;
#[macro_use] mod macros;
#[macro_use] mod bytes;
#[macro_use] mod bits;
#[macro_use] mod accumulator;

#[macro_use]
#[cfg(not(feature = "core"))]
mod producer;
#[cfg(not(feature = "core"))]
mod consumer;

#[macro_use] mod nom;
#[macro_use] mod character;

#[cfg(feature = "regexp")]
#[macro_use] mod regexp;

