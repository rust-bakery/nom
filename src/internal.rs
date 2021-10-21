//! Basic types to build the parsers

use self::Needed::*;
use crate::error::{self, ParserKind};
use crate::lib::std::fmt;
use core::num::NonZeroUsize;

/// Holds the result of parsing functions
///
/// It depends on the input type `I`, the output type `O`, and the error type `E`
/// (by default `(I, nom::ParserKind)`)
///
/// The `Ok` side is a pair containing the remainder of the input (the part of the data that
/// was not parsed) and the produced value. The `Err` side contains an instance of `nom::Err`.
///
/// Outside of the parsing code, you can use the [Finish::finish] method to convert
/// it to a more common result type
pub type ParseResult<I, O, E = error::Context<I>> = Result<(I, O), Outcome<E>>;

/// Helper trait to convert a parser's result to a more manageable type
pub trait Finish<I, O, E> {
  /// converts the parser's result to a type that is more consumable by error
  /// management libraries. It keeps the same `Ok` branch, and merges `Outcome::Error`
  /// and `Outcome::Failure` into the `Err` side.
  ///
  /// *warning*: if the result is `Err(Outcome::Incomplete(_))`, this method will panic.
  /// - "complete" parsers: It will not be an issue, `Incomplete` is never used
  /// - "streaming" parsers: `Incomplete` will be returned if there's not enough data
  /// for the parser to decide, and you should gather more data before parsing again.
  /// Once the parser returns either `Ok(_)`, `Err(Outcome::Failure(_))` or `Err(Outcome::Failure(_))`,
  /// you can get out of the parsing loop and call `finish()` on the parser's result
  fn finish(self) -> Result<(I, O), E>;
}

impl<I, O, E> Finish<I, O, E> for ParseResult<I, O, E> {
  fn finish(self) -> Result<(I, O), E> {
    match self {
      Ok(res) => Ok(res),
      Err(Outcome::Failure(e)) | Err(Outcome::Invalid(e)) => Err(e),
      Err(Outcome::Incomplete(_)) => {
        panic!("Cannot call `finish()` on `Err(Outcome::Incomplete(_))`: this result means that the parser does not have enough data to decide, you should gather more data and try to reapply  the parser instead")
      }
    }
  }
}

/// Contains information on needed data if a parser returned `Incomplete`
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub enum Needed {
  /// Needs more data, but we do not know how much
  Unknown,
  /// Contains the required data size in bytes
  Size(NonZeroUsize),
}

impl Needed {
  /// Creates `Needed` instance, returns `Needed::Unknown` if the argument is zero
  pub fn new(s: usize) -> Self {
    match NonZeroUsize::new(s) {
      Some(sz) => Needed::Size(sz),
      None => Needed::Unknown,
    }
  }

  /// Indicates if we know how many bytes we need
  pub fn is_known(&self) -> bool {
    *self != Unknown
  }

  /// Maps a `Needed` to `Needed` by applying a function to a contained `Size` value.
  #[inline]
  pub fn map<F: Fn(NonZeroUsize) -> usize>(self, f: F) -> Needed {
    match self {
      Unknown => Unknown,
      Size(n) => Needed::new(f(n)),
    }
  }
}

/// The `Err` enum indicates the parser was not successful
///
/// It has three cases:
///
/// * `Incomplete` indicates that more data is needed to decide. The `Needed` enum
/// can contain how many additional bytes are necessary. If you are sure your parser
/// is working on full data, you can wrap your parser with the `complete` combinator
/// to transform that case in `Error`
/// * `Error` means some parser did not succeed, but another one might (as an example,
/// when testing different branches of an `alt` combinator)
/// * `Failure` indicates an unrecoverable error. As an example, if you recognize a prefix
/// to decide on the next parser to apply, and that parser fails, you know there's no need
/// to try other parsers, you were already in the right branch, so the data is invalid
///
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub enum Outcome<Context> {
  /// There was not enough data
  Incomplete(Needed),
  /// The parser had an error (recoverable)
  Failure(Context),
  /// The parser had an unrecoverable error: we got to the right
  /// branch and we know other branches won't work, so backtrack
  /// as fast as possible
  Invalid(Context),
}

impl<E> Outcome<E> {
  /// Tests if the result is Incomplete
  pub fn is_incomplete(&self) -> bool {
    if let Outcome::Incomplete(_) = self {
      true
    } else {
      false
    }
  }

  /// Applies the given function to the inner error
  pub fn map<E2, F>(self, f: F) -> Outcome<E2>
  where
    F: FnOnce(E) -> E2,
  {
    match self {
      Outcome::Incomplete(n) => Outcome::Incomplete(n),
      Outcome::Invalid(t) => Outcome::Invalid(f(t)),
      Outcome::Failure(t) => Outcome::Failure(f(t)),
    }
  }

  /// Automatically converts between errors if the underlying type supports it
  pub fn convert<F>(e: Outcome<F>) -> Self
  where
    E: From<F>,
  {
    e.map(crate::lib::std::convert::Into::into)
  }
}

impl<T> Outcome<(T, ParserKind)> {
  /// Maps `Err<(T, ParserKind)>` to `Err<(U, ParserKind)>` with the given `F: T -> U`
  pub fn map_input<U, F>(self, f: F) -> Outcome<(U, ParserKind)>
  where
    F: FnOnce(T) -> U,
  {
    match self {
      Outcome::Incomplete(n) => Outcome::Incomplete(n),
      Outcome::Invalid((input, k)) => Outcome::Invalid((f(input), k)),
      Outcome::Failure((input, k)) => Outcome::Failure((f(input), k)),
    }
  }
}

impl<T> Outcome<error::Context<T>> {
  /// Maps `Err<error::Error<T>>` to `Err<error::Error<U>>` with the given `F: T -> U`
  pub fn map_input<U, F>(self, f: F) -> Outcome<error::Context<U>>
  where
    F: FnOnce(T) -> U,
  {
    match self {
      Outcome::Incomplete(n) => Outcome::Incomplete(n),
      Outcome::Invalid(error::Context { input, code }) => Outcome::Invalid(error::Context {
        input: f(input),
        code,
      }),
      Outcome::Failure(error::Context { input, code }) => Outcome::Failure(error::Context {
        input: f(input),
        code,
      }),
    }
  }
}

#[cfg(feature = "alloc")]
use crate::lib::std::{borrow::ToOwned, string::String, vec::Vec};
#[cfg(feature = "alloc")]
impl Outcome<(&[u8], ParserKind)> {
  /// Obtaining ownership
  #[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
  pub fn to_owned(self) -> Outcome<(Vec<u8>, ParserKind)> {
    self.map_input(ToOwned::to_owned)
  }
}

#[cfg(feature = "alloc")]
impl Outcome<(&str, ParserKind)> {
  /// Obtaining ownership
  #[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
  pub fn to_owned(self) -> Outcome<(String, ParserKind)> {
    self.map_input(ToOwned::to_owned)
  }
}

#[cfg(feature = "alloc")]
impl Outcome<error::Context<&[u8]>> {
  /// Obtaining ownership
  #[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
  pub fn to_owned(self) -> Outcome<error::Context<Vec<u8>>> {
    self.map_input(ToOwned::to_owned)
  }
}

#[cfg(feature = "alloc")]
impl Outcome<error::Context<&str>> {
  /// Obtaining ownership
  #[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
  pub fn to_owned(self) -> Outcome<error::Context<String>> {
    self.map_input(ToOwned::to_owned)
  }
}

impl<E: Eq> Eq for Outcome<E> {}

impl<E> fmt::Display for Outcome<E>
where
  E: fmt::Debug,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Outcome::Incomplete(Needed::Size(u)) => write!(f, "Parsing requires {} bytes/chars", u),
      Outcome::Incomplete(Needed::Unknown) => write!(f, "Parsing requires more data"),
      Outcome::Invalid(c) => write!(f, "Parsing Failure: {:?}", c),
      Outcome::Failure(c) => write!(f, "Parsing Context: {:?}", c),
    }
  }
}

#[cfg(feature = "std")]
use std::error::Error;

#[cfg(feature = "std")]
impl<E> Error for Outcome<E>
where
  E: fmt::Debug,
{
  fn source(&self) -> Option<&(dyn Error + 'static)> {
    None // no underlying error
  }
}

/// All nom parsers implement this trait
pub trait Parser<I, O, E> {
  /// A parser takes in input type, and returns a `Result` containing
  /// either the remaining input and the output value, or an error
  fn parse(&mut self, input: I) -> ParseResult<I, O, E>;

  /// Maps a function over the result of a parser
  fn map<G, O2>(self, g: G) -> Map<Self, G, O>
  where
    G: Fn(O) -> O2,
    Self: core::marker::Sized,
  {
    Map {
      f: self,
      g,
      phantom: core::marker::PhantomData,
    }
  }

  /// Creates a second parser from the output of the first one, then apply over the rest of the input
  fn flat_map<G, H, O2>(self, g: G) -> FlatMap<Self, G, O>
  where
    G: Fn(O) -> H,
    H: Parser<I, O2, E>,
    Self: core::marker::Sized,
  {
    FlatMap {
      f: self,
      g,
      phantom: core::marker::PhantomData,
    }
  }

  /// Applies a second parser over the output of the first one
  fn and_then<G, O2>(self, g: G) -> AndThen<Self, G, O>
  where
    G: Parser<O, O2, E>,
    Self: core::marker::Sized,
  {
    AndThen {
      f: self,
      g,
      phantom: core::marker::PhantomData,
    }
  }

  /// Applies a second parser after the first one, return their results as a tuple
  fn and<G, O2>(self, g: G) -> And<Self, G>
  where
    G: Parser<I, O2, E>,
    Self: core::marker::Sized,
  {
    And { f: self, g }
  }

  /// Applies a second parser over the input if the first one failed
  fn or<G>(self, g: G) -> Or<Self, G>
  where
    G: Parser<I, O, E>,
    Self: core::marker::Sized,
  {
    Or { f: self, g }
  }

  /// automatically converts the parser's output and error values to another type, as long as they
  /// implement the `From` trait
  fn into<O2: From<O>, E2: From<E>>(self) -> Into<Self, O, O2, E, E2>
  where
    Self: core::marker::Sized,
  {
    Into {
      f: self,
      phantom_out1: core::marker::PhantomData,
      phantom_err1: core::marker::PhantomData,
      phantom_out2: core::marker::PhantomData,
      phantom_err2: core::marker::PhantomData,
    }
  }
}

impl<'a, I, O, E, F> Parser<I, O, E> for F
where
  F: FnMut(I) -> ParseResult<I, O, E> + 'a,
{
  fn parse(&mut self, i: I) -> ParseResult<I, O, E> {
    self(i)
  }
}

#[cfg(feature = "alloc")]
use alloc::boxed::Box;

#[cfg(feature = "alloc")]
impl<'a, I, O, E> Parser<I, O, E> for Box<dyn Parser<I, O, E> + 'a> {
  fn parse(&mut self, input: I) -> ParseResult<I, O, E> {
    (**self).parse(input)
  }
}

/// Implementation of `Parser::map`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct Map<F, G, O1> {
  f: F,
  g: G,
  phantom: core::marker::PhantomData<O1>,
}

impl<'a, I, O1, O2, E, F: Parser<I, O1, E>, G: Fn(O1) -> O2> Parser<I, O2, E> for Map<F, G, O1> {
  fn parse(&mut self, i: I) -> ParseResult<I, O2, E> {
    match self.f.parse(i) {
      Err(e) => Err(e),
      Ok((i, o)) => Ok((i, (self.g)(o))),
    }
  }
}

/// Implementation of `Parser::flat_map`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct FlatMap<F, G, O1> {
  f: F,
  g: G,
  phantom: core::marker::PhantomData<O1>,
}

impl<'a, I, O1, O2, E, F: Parser<I, O1, E>, G: Fn(O1) -> H, H: Parser<I, O2, E>> Parser<I, O2, E>
  for FlatMap<F, G, O1>
{
  fn parse(&mut self, i: I) -> ParseResult<I, O2, E> {
    let (i, o1) = self.f.parse(i)?;
    (self.g)(o1).parse(i)
  }
}

/// Implementation of `Parser::and_then`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct AndThen<F, G, O1> {
  f: F,
  g: G,
  phantom: core::marker::PhantomData<O1>,
}

impl<'a, I, O1, O2, E, F: Parser<I, O1, E>, G: Parser<O1, O2, E>> Parser<I, O2, E>
  for AndThen<F, G, O1>
{
  fn parse(&mut self, i: I) -> ParseResult<I, O2, E> {
    let (i, o1) = self.f.parse(i)?;
    let (_, o2) = self.g.parse(o1)?;
    Ok((i, o2))
  }
}

/// Implementation of `Parser::and`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct And<F, G> {
  f: F,
  g: G,
}

impl<'a, I, O1, O2, E, F: Parser<I, O1, E>, G: Parser<I, O2, E>> Parser<I, (O1, O2), E>
  for And<F, G>
{
  fn parse(&mut self, i: I) -> ParseResult<I, (O1, O2), E> {
    let (i, o1) = self.f.parse(i)?;
    let (i, o2) = self.g.parse(i)?;
    Ok((i, (o1, o2)))
  }
}

/// Implementation of `Parser::or`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct Or<F, G> {
  f: F,
  g: G,
}

impl<'a, I: Clone, O, E: crate::error::ParseContext<I>, F: Parser<I, O, E>, G: Parser<I, O, E>>
  Parser<I, O, E> for Or<F, G>
{
  fn parse(&mut self, i: I) -> ParseResult<I, O, E> {
    match self.f.parse(i.clone()) {
      Err(Outcome::Failure(e1)) => match self.g.parse(i) {
        Err(Outcome::Failure(e2)) => Err(Outcome::Failure(e1.or(e2))),
        res => res,
      },
      res => res,
    }
  }
}

/// Implementation of `Parser::into`
#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
pub struct Into<F, O1, O2: From<O1>, E1, E2: From<E1>> {
  f: F,
  phantom_out1: core::marker::PhantomData<O1>,
  phantom_err1: core::marker::PhantomData<E1>,
  phantom_out2: core::marker::PhantomData<O2>,
  phantom_err2: core::marker::PhantomData<E2>,
}

impl<
    'a,
    I: Clone,
    O1,
    O2: From<O1>,
    E1,
    E2: crate::error::ParseContext<I> + From<E1>,
    F: Parser<I, O1, E1>,
  > Parser<I, O2, E2> for Into<F, O1, O2, E1, E2>
{
  fn parse(&mut self, i: I) -> ParseResult<I, O2, E2> {
    match self.f.parse(i) {
      Ok((i, o)) => Ok((i, o.into())),
      Err(Outcome::Failure(e)) => Err(Outcome::Failure(e.into())),
      Err(Outcome::Invalid(e)) => Err(Outcome::Invalid(e.into())),
      Err(Outcome::Incomplete(e)) => Err(Outcome::Incomplete(e)),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::error::ParserKind;

  #[doc(hidden)]
  #[macro_export]
  macro_rules! assert_size (
    ($t:ty, $sz:expr) => (
      assert_eq!(crate::lib::std::mem::size_of::<$t>(), $sz);
    );
  );

  #[test]
  #[cfg(target_pointer_width = "64")]
  fn size_test() {
    assert_size!(ParseResult<&[u8], &[u8], (&[u8], u32)>, 40);
    assert_size!(ParseResult<&str, &str, u32>, 40);
    assert_size!(Needed, 8);
    assert_size!(Outcome<u32>, 16);
    assert_size!(ParserKind, 1);
  }

  #[test]
  fn err_map_test() {
    let e = Outcome::Failure(1);
    assert_eq!(e.map(|v| v + 1), Outcome::Failure(2));
  }
}
