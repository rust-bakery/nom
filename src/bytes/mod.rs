//! Parsers recognizing bytes streams

pub mod complete;
pub mod streaming;
#[cfg(test)]
mod tests;

use core::marker::PhantomData;

use crate::error::ErrorKind;
use crate::error::ParseError;
use crate::internal::{Err, Needed, Parser};
use crate::lib::std::result::Result::*;
use crate::traits::{Compare, CompareResult, InputLength};
use crate::Input;
use crate::IsStreaming;
use crate::Mode;
use crate::OutputMode;
use crate::ToUsize;

/// Recognizes a pattern.
///
/// The input data will be compared to the tag combinator's argument and will return the part of
/// the input that matches the argument.
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, Needed, IResult};
/// use nom::bytes::streaming::tag;
///
/// fn parser(s: &str) -> IResult<&str, &str> {
///   tag("Hello")(s)
/// }
///
/// assert_eq!(parser("Hello, World!"), Ok((", World!", "Hello")));
/// assert_eq!(parser("Something"), Err(Err::Error(Error::new("Something", ErrorKind::Tag))));
/// assert_eq!(parser("S"), Err(Err::Error(Error::new("S", ErrorKind::Tag))));
/// assert_eq!(parser("H"), Err(Err::Incomplete(Needed::new(4))));
/// ```
pub fn tag<T, I, Error: ParseError<I>>(tag: T) -> impl Parser<I, Output = I, Error = Error>
where
  I: Input + Compare<T>,
  T: InputLength + Clone,
{
  Tag {
    tag,
    e: PhantomData,
  }
}

/// Tag implementation
pub struct Tag<T, E> {
  tag: T,
  e: PhantomData<E>,
}

impl<I, Error: ParseError<I>, T> Parser<I> for Tag<T, Error>
where
  I: Input + Compare<T>,
  T: InputLength + Clone,
{
  type Output = I;

  type Error = Error;

  fn process<OM: OutputMode>(&mut self, i: I) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    let tag_len = self.tag.input_len();
    let t = self.tag.clone();

    match i.compare(t) {
      CompareResult::Ok => Ok((i.take_from(tag_len), OM::Output::bind(|| i.take(tag_len)))),
      CompareResult::Incomplete => {
        if OM::Incomplete::is_streaming() {
          Err(Err::Incomplete(Needed::new(tag_len - i.input_len())))
        } else {
          Err(Err::Error(OM::Error::bind(|| {
            let e: ErrorKind = ErrorKind::Tag;
            Error::from_error_kind(i, e)
          })))
        }
      }
      CompareResult::Error => Err(Err::Error(OM::Error::bind(|| {
        let e: ErrorKind = ErrorKind::Tag;
        Error::from_error_kind(i, e)
      }))),
    }
  }
}

/// TODO
pub fn take<C, I, Error: ParseError<I>>(count: C) -> impl Parser<I, Output = I, Error = Error>
where
  I: Input,
  C: ToUsize,
{
  Take {
    length: count.to_usize(),
    e: PhantomData,
  }
}

///
pub struct Take<E> {
  length: usize,
  e: PhantomData<E>,
}

impl<I, Error: ParseError<I>> Parser<I> for Take<Error>
where
  I: Input,
{
  type Output = I;
  type Error = Error;

  fn process<OM: OutputMode>(&mut self, i: I) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    match i.slice_index(self.length) {
      Err(needed) => {
        if OM::Incomplete::is_streaming() {
          Err(Err::Incomplete(needed))
        } else {
          Err(Err::Error(OM::Error::bind(|| {
            let e: ErrorKind = ErrorKind::Eof;
            Error::from_error_kind(i, e)
          })))
        }
      }
      Ok(index) => Ok((i.take_from(index), OM::Output::bind(|| i.take(index)))),
    }
  }
}

/// Returns the longest (at least 1) input slice that matches the predicate.
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// It will return an `Err(Err::Error((_, ErrorKind::TakeWhile1)))` if the pattern wasn't met.
///
/// # Streaming Specific
/// *Streaming version* will return a `Err::Incomplete(Needed::new(1))` or if the pattern reaches the end of the input.
///
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, Needed, IResult};
/// use nom::bytes::streaming::take_while1;
/// use nom::character::is_alphabetic;
///
/// fn alpha(s: &[u8]) -> IResult<&[u8], &[u8]> {
///   take_while1(is_alphabetic)(s)
/// }
///
/// assert_eq!(alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(alpha(b"latin"), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(alpha(b"12345"), Err(Err::Error(Error::new(&b"12345"[..], ErrorKind::TakeWhile1))));
/// ```
pub fn take_while1<F, I, Error: ParseError<I>>(cond: F) -> impl Parser<I, Output = I, Error = Error>
where
  I: Input,
  F: Fn(<I as Input>::Item) -> bool,
{
  TakeWhile1 {
    f: move |c| !cond(c),
    e: PhantomData,
  }
}

/// TODO
pub struct TakeWhile1<F, E> {
  f: F,
  e: PhantomData<E>,
}

impl<I, F, Error: ParseError<I>> Parser<I> for TakeWhile1<F, Error>
where
  I: Input,
  F: Fn(<I as Input>::Item) -> bool,
{
  type Output = I;
  type Error = Error;

  fn process<OM: crate::OutputMode>(
    &mut self,
    i: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    i.split_at_position_mode1::<OM, _, _>(|item| (self.f)(item), ErrorKind::TakeWhile1)
  }
}
