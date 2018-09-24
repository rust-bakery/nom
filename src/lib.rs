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
//!   c.is_digit(16)
//! }
//!
//! named!(hex_primary<&str, u8>,
//!   map_res!(take_while_m_n!(2, 2, is_hex_digit), from_hex)
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
//! Parser combinators are an approach to parsers that is very different from
//! software like [lex](https://en.wikipedia.org/wiki/Lex_(software)) and
//! [yacc](https://en.wikipedia.org/wiki/Yacc). Instead of writing the grammar
//! in a separate file and generating the corresponding code, you use very small
//! functions with very specific purpose, like "take 5 bytes", or "recognize the
//! word 'HTTP'", and assemble then in meaningful patterns like "recognize
//! 'HTTP', then a space, then a version".
//! The resulting code is small, and looks like the grammar you would have
//! written with other parser approaches.
//!
//! This has a few advantages:
//!
//! - the parsers are small and easy to write
//! - the parsers components are easy to reuse (if they're general enough, please add them to nom!)
//! - the parsers components are easy to test separately (unit tests and property-based tests)
//! - the parser combination code looks close to the grammar you would have written
//! - you can build partial parsers, specific to the data you need at the moment, and ignore the rest
//!
//! Here is an example of one such parser, to recognize text between parentheses:
//!
//! ```rust
//! #[macro_use]
//! extern crate nom;
//!
//! # fn main() {
//! named!(parens, delimited!(char!('('), is_not!(")"), char!(')')));
//! # }
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
//! # fn main() {
//! fn take4(i:&[u8]) -> IResult<&[u8], &[u8]>{
//!   if i.len() < 4 {
//!     Err(Err::Incomplete(Needed::Size(4)))
//!   } else {
//!     Ok((&i[4..],&i[0..4]))
//!   }
//! }
//! # }
//! ```
//!
//! This function takes a byte array as input, and tries to consume 4 bytes.
//! Writing all the parsers manually, like this, is dangerous, despite Rust's safety features. There
//! are still a lot of mistakes one can make. That's why nom provides a list of macros to help in
//! developing parsers.
//!
//! With macros, you would write it like this:
//!
//! ```rust
//! #[macro_use]
//! extern crate nom;
//!
//! # fn main() {
//! named!(take4, take!(4));
//! # }
//! ```
//!
//! A parser in nom is a function which, for an input type `I`, an output type `O`
//! and an optional error type `E`, will have the following signature:
//!
//! ```rust,ignore
//! fn parser(input: I) -> IResult<I, O, E>;
//! ```
//!
//! Or like this, if you don't want to specify a custom error type (it will be `u32` by default):
//!
//! ```rust,ignore
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
//! - an error `Err(Err::Error(c))` with `c` an enum that contains an error code with its position in the input, and optionally a chain of accumulated errors;
//! - an error `Err(Err::Incomplete(Needed))` indicating that more input is necessary. `Needed` can indicate how much data is needed
//! - an error `Err(Err::Failure(c))`. It works like the `Error` case, except it indicates an unrecoverable error: we cannot backtrack and test another parser
//!
//! Please refer to the [documentation][doc] for an exhaustive list of parsers. See also the
//! ["choose a combinator" guide](https://github.com/Geal/nom/blob/master/doc/choosing_a_combinator.md)**.
//!
//! ## Making new parsers with macros
//!
//! Macros are the main way to make new parsers by combining other ones. Those macros accept other macros or function names as arguments. You then need to make a function out of that combinator with **`named!`**, or a closure with **`closure!`**. Here is how you would do, with the **`tag!`** and **`take!`** combinators:
//!
//! ```rust
//! # #[macro_use] extern crate nom;
//! # fn main() {
//! named!(abcd_parser, tag!("abcd")); // will consume bytes if the input begins with "abcd"
//!
//! named!(take_10, take!(10));        // will consume and return 10 bytes of input
//! # }
//! ```
//!
//! The **`named!`** macro can take three different syntaxes:
//!
//! ```rust,ignore
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
//! # #[macro_use] extern crate nom;
//! # #[cfg(feature = "alloc")]
//! # fn main() {
//! named!(my_function<&[u8], Vec<&[u8]>>, many0!(tag!("abcd")));
//! # }
//!
//! # #[cfg(not(feature = "alloc"))]
//! # fn main() {}
//! ```
//!
//! You will get the following error: `error: expected an item keyword`. This
//! happens because `>>` is seen as an operator, so the macro parser does not
//! recognize what we want. There is a way to avoid it, by inserting a space:
//!
//! ```rust
//! # #[macro_use] extern crate nom;
//! # #[cfg(feature = "alloc")]
//! # fn main() {
//! named!(my_function<&[u8], Vec<&[u8]> >, many0!(tag!("abcd")));
//! # }
//! # #[cfg(not(feature = "alloc"))]
//! # fn main() {}
//! ```
//!
//! This will compile correctly. I am very sorry for this inconvenience.
//!
//! ## Combining parsers
//!
//! There are more high level patterns, like the **`alt!`** combinator, which provides a choice between multiple parsers. If one branch fails, it tries the next, and returns the result of the first parser that succeeds:
//!
//! ```rust
//! # #[macro_use] extern crate nom;
//! # fn main() {
//! named!(alt_tags, alt!(tag!("abcd") | tag!("efgh")));
//!
//! assert_eq!(alt_tags(b"abcdxxx"), Ok((&b"xxx"[..], &b"abcd"[..])));
//! assert_eq!(alt_tags(b"efghxxx"), Ok((&b"xxx"[..], &b"efgh"[..])));
//! assert_eq!(alt_tags(b"ijklxxx"), Err(nom::Err::Error(error_position!(&b"ijklxxx"[..], nom::ErrorKind::Alt))));
//! # }
//! ```
//!
//! The pipe `|` character is used as separator.
//!
//! The **`opt!`** combinator makes a parser optional. If the child parser returns an error, **`opt!`** will succeed and return None:
//!
//! ```rust
//! # #[macro_use] extern crate nom;
//! # fn main() {
//! named!( abcd_opt< &[u8], Option<&[u8]> >, opt!( tag!("abcd") ) );
//!
//! assert_eq!(abcd_opt(b"abcdxxx"), Ok((&b"xxx"[..], Some(&b"abcd"[..]))));
//! assert_eq!(abcd_opt(b"efghxxx"), Ok((&b"efghxxx"[..], None)));
//! # }
//! ```
//!
//! **`many0!`** applies a parser 0 or more times, and returns a vector of the aggregated results:
//!
//! ```rust
//! # #[macro_use] extern crate nom;
//! # #[cfg(feature = "alloc")]
//! # fn main() {
//! use std::str;
//!
//! named!(multi< Vec<&str> >, many0!( map_res!(tag!( "abcd" ), str::from_utf8) ) );
//! let a = b"abcdef";
//! let b = b"abcdabcdef";
//! let c = b"azerty";
//! assert_eq!(multi(a), Ok((&b"ef"[..],     vec!["abcd"])));
//! assert_eq!(multi(b), Ok((&b"ef"[..],     vec!["abcd", "abcd"])));
//! assert_eq!(multi(c), Ok((&b"azerty"[..], Vec::new())));
//! # }
//! # #[cfg(not(feature = "alloc"))]
//! # fn main() {}
//! ```
//!
//! Here are some basic combining macros available:
//!
//! - **`opt!`**: will make the parser optional (if it returns the `O` type, the new parser returns `Option<O>`)
//! - **`many0!`**: will apply the parser 0 or more times (if it returns the `O` type, the new parser returns `Vec<O>`)
//! - **`many1!`**: will apply the parser 1 or more times
//!
//! There are more complex (and more useful) parsers like `do_parse!` and `tuple!`, which are used to apply a series of parsers then assemble their results.
//!
//! Example with `tuple!`:
//!
//! ```rust
//! # #[macro_use] extern crate nom;
//! # fn main() {
//! use nom::{ErrorKind, Needed,be_u16};
//!
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
//!   Ok((
//!     &b"h"[..],
//!     (0x6162u16, &b"cde"[..], &b"fg"[..])
//!   ))
//! );
//! assert_eq!(tpl(&b"abcde"[..]), Err(nom::Err::Incomplete(Needed::Size(2))));
//! let input = &b"abcdejk"[..];
//! assert_eq!(tpl(input), Err(nom::Err::Error(error_position!(&input[5..], ErrorKind::Tag))));
//! # }
//! ```
//!
//! Example with `do_parse!`:
//!
//! ```rust
//! # #[macro_use] extern crate nom;
//! # fn main() {
//! use nom::IResult;
//!
//! #[derive(Debug, PartialEq)]
//! struct A {
//!   a: u8,
//!   b: u8
//! }
//!
//! fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Ok((i,1)) }
//! fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Ok((i,2)) }
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
//! assert_eq!(r, Ok((&b"X"[..], A{a: 1, b: 2})));
//!
//! let r2 = f(b"abcdefghefghX");
//! assert_eq!(r2, Ok((&b"X"[..], A{a: 1, b: 2})));
//! # }
//! ```
//!
//! The double right arrow `>>` is used as separator between every parser in the sequence, and the last closure can see the variables storing the result of parsers. Unless the specified return type is already a tuple, the final line should be that type wrapped in a tuple.
//!
//! More examples of [`do_parse!`](macro.do_parse.html) and [`tuple!`](macro.tuple.html) usage can be found in the [INI file parser example](tests/ini.rs).
//!
//! **Going further:** read the [guides](https://github.com/Geal/nom/tree/master/doc)!
#![cfg_attr(all(not(feature = "std"), feature = "alloc"), feature(alloc))]
#![cfg_attr(not(feature = "std"), no_std)]
//#![warn(missing_docs)]
#![cfg_attr(feature = "cargo-clippy", allow(doc_markdown))]
#![cfg_attr(nightly, feature(test))]

#[cfg(all(not(feature = "std"), feature = "alloc"))]
#[macro_use]
extern crate alloc;
#[cfg(feature = "regexp_macros")]
#[macro_use]
extern crate lazy_static;
extern crate memchr;
#[cfg(feature = "regexp")]
extern crate regex;
#[cfg(nightly)]
extern crate test;

/// Lib module to re-export everything needed from `std` or `core`/`alloc`. This is how `serde` does
/// it, albeit there it is not public.
pub mod lib {
  /// `std` facade allowing `std`/`core` to be interchangeable. Reexports `alloc` crate optionally,
  /// as well as `core` or `std`
  #[cfg(not(feature = "std"))]
  pub mod std {
    #[cfg(feature = "alloc")]
    #[cfg_attr(feature = "alloc", macro_use)]
    pub use alloc::{boxed, string, vec};

    pub use core::{cmp, convert, fmt, iter, mem, ops, option, result, slice, str};
    pub mod prelude {
      pub use core::prelude as v1;
    }
  }

  #[cfg(feature = "std")]
  pub mod std {
    pub use std::{boxed, cmp, collections, convert, fmt, hash, iter, mem, ops, option, result, slice, str, string, vec};
    pub mod prelude {
      pub use std::prelude as v1;
    }
  }
}

pub use self::traits::*;
pub use self::util::*;

#[cfg(feature = "verbose-errors")]
pub use self::verbose_errors::*;

#[cfg(not(feature = "verbose-errors"))]
pub use self::simple_errors::*;

pub use self::branch::*;
pub use self::internal::*;
pub use self::macros::*;
pub use self::methods::*;
pub use self::multi::*;
pub use self::sequence::*;

pub use self::bits::*;
pub use self::bytes::*;

pub use self::character::*;
pub use self::nom::*;

pub use self::whitespace::*;

#[cfg(feature = "regexp")]
pub use self::regexp::*;
pub use self::str::*;

#[macro_use]
mod util;

#[cfg(feature = "verbose-errors")]
#[macro_use]
pub mod verbose_errors;

#[cfg(not(feature = "verbose-errors"))]
#[macro_use]
pub mod simple_errors;

#[macro_use]
mod internal;
mod traits;
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
