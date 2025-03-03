//! Character specific parsers and combinators
//!
//! Functions recognizing specific characters

use core::marker::PhantomData;

use crate::error::ErrorKind;
use crate::FindToken;
use crate::IsStreaming;
use crate::Mode;
use crate::{error::ParseError, AsChar, Err, IResult, Input, Needed, Parser};

#[cfg(test)]
mod tests;

pub mod complete;
pub mod streaming;

#[inline]
#[doc(hidden)]
#[deprecated(since = "8.0.0", note = "Replaced with `AsChar::is_alpha`")]
pub fn is_alphabetic(chr: u8) -> bool {
  matches!(chr, 0x41..=0x5A | 0x61..=0x7A)
}

#[inline]
#[doc(hidden)]
#[deprecated(since = "8.0.0", note = "Replaced with `AsChar::is_dec_digit`")]
pub fn is_digit(chr: u8) -> bool {
  matches!(chr, 0x30..=0x39)
}

#[inline]
#[doc(hidden)]
#[deprecated(since = "8.0.0", note = "Replaced with `AsChar::is_hex_digit`")]
pub fn is_hex_digit(chr: u8) -> bool {
  matches!(chr, 0x30..=0x39 | 0x41..=0x46 | 0x61..=0x66)
}

#[inline]
#[doc(hidden)]
#[deprecated(since = "8.0.0", note = "Replaced with `AsChar::is_oct_digit`")]
pub fn is_oct_digit(chr: u8) -> bool {
  matches!(chr, 0x30..=0x37)
}

/// Tests if byte is ASCII binary digit: 0-1
///
/// # Example
///
/// ```
/// # use nom::character::is_bin_digit;
/// assert_eq!(is_bin_digit(b'a'), false);
/// assert_eq!(is_bin_digit(b'2'), false);
/// assert_eq!(is_bin_digit(b'0'), true);
/// assert_eq!(is_bin_digit(b'1'), true);
/// ```
#[inline]
pub fn is_bin_digit(chr: u8) -> bool {
  matches!(chr, 0x30..=0x31)
}

#[inline]
#[doc(hidden)]
#[deprecated(since = "8.0.0", note = "Replaced with `AsChar::is_alphanum`")]
pub fn is_alphanumeric(chr: u8) -> bool {
  AsChar::is_alphanum(chr)
}

#[inline]
#[doc(hidden)]
#[deprecated(since = "8.0.0", note = "Replaced with `AsChar::is_space`")]
pub fn is_space(chr: u8) -> bool {
  chr == b' ' || chr == b'\t'
}

#[inline]
#[doc(hidden)]
#[deprecated(since = "8.0.0", note = "Replaced with `AsChar::is_newline`")]
pub fn is_newline(chr: u8) -> bool {
  chr == b'\n'
}

/// Recognizes one character.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::{ErrorKind, Error}, Needed, IResult};
/// # use nom::character::streaming::char;
/// fn parser(i: &str) -> IResult<&str, char> {
///     char('a')(i)
/// }
/// assert_eq!(parser("abc"), Ok(("bc", 'a')));
/// assert_eq!(parser("bc"), Err(Err::Error(Error::new("bc", ErrorKind::Char))));
/// assert_eq!(parser(""), Err(Err::Incomplete(Needed::new(1))));
/// ```
pub fn char<I, Error: ParseError<I>>(c: char) -> Char<Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
{
  Char { c, e: PhantomData }
}

/// Parser implementation for [char()]
pub struct Char<E> {
  c: char,
  e: PhantomData<E>,
}

impl<I, Error: ParseError<I>> Parser<I> for Char<Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
{
  type Output = char;
  type Error = Error;
  #[inline(always)]
  fn process<OM: crate::OutputMode>(
    &mut self,
    i: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    match (i).iter_elements().next().map(|t| {
      let b = t.as_char() == self.c;
      (&self.c, b)
    }) {
      None => {
        if OM::Incomplete::is_streaming() {
          Err(Err::Incomplete(Needed::new(self.c.len() - i.input_len())))
        } else {
          Err(Err::Error(OM::Error::bind(|| Error::from_char(i, self.c))))
        }
      }
      Some((_, false)) => Err(Err::Error(OM::Error::bind(|| Error::from_char(i, self.c)))),
      Some((c, true)) => Ok((i.take_from(c.len()), OM::Output::bind(|| c.as_char()))),
    }
  }
}

/// Recognizes one character and checks that it satisfies a predicate
///
/// # Example
///
/// ```
/// # use nom::{Err, error::{ErrorKind, Error}, Needed, IResult};
/// # use nom::character::complete::satisfy;
/// fn parser(i: &str) -> IResult<&str, char> {
///     satisfy(|c| c == 'a' || c == 'b')(i)
/// }
/// assert_eq!(parser("abc"), Ok(("bc", 'a')));
/// assert_eq!(parser("cd"), Err(Err::Error(Error::new("cd", ErrorKind::Satisfy))));
/// assert_eq!(parser(""), Err(Err::Error(Error::new("", ErrorKind::Satisfy))));
/// ```
pub fn satisfy<F, I, Error: ParseError<I>>(predicate: F) -> Satisfy<F, Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
  F: Fn(char) -> bool,
{
  Satisfy {
    predicate,
    error: PhantomData,
  }
}

/// Parser implementation for [`satisfy`]
pub struct Satisfy<F, E> {
  predicate: F,
  error: PhantomData<E>,
}

impl<I, Error: ParseError<I>, F> Parser<I> for Satisfy<F, Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
  F: Fn(char) -> bool,
{
  type Output = char;
  type Error = Error;

  #[inline(always)]
  fn process<OM: crate::OutputMode>(
    &mut self,
    i: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    process_satisfy::<OM, _, _, _, _>(i, &self.predicate, |i| {
      Error::from_error_kind(i, ErrorKind::Satisfy)
    })
  }
}

#[inline(always)]
fn process_satisfy<OM, I, F, Error, MakeError>(
  i: I,
  predicate: F,
  make_error: MakeError,
) -> crate::PResult<OM, I, char, Error>
where
  OM: crate::OutputMode,
  I: Input,
  <I as Input>::Item: AsChar,
  F: Fn(char) -> bool,
  Error: ParseError<I>,
  MakeError: FnOnce(I) -> Error,
{
  match i.iter_elements().next().map(|t| {
    let c = t.as_char();
    let b = predicate(c);
    (c, b)
  }) {
    None => {
      if OM::Incomplete::is_streaming() {
        Err(Err::Incomplete(Needed::Unknown))
      } else {
        Err(Err::Error(OM::Error::bind(|| make_error(i))))
      }
    }
    Some((_, false)) => Err(Err::Error(OM::Error::bind(|| make_error(i)))),
    Some((c, true)) => Ok((i.take_from(c.len()), OM::Output::bind(|| c.as_char()))),
  }
}

/// Recognizes one of the provided characters.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind};
/// # use nom::character::complete::one_of;
/// assert_eq!(one_of::<_, _, (&str, ErrorKind)>("abc")("b"), Ok(("", 'b')));
/// assert_eq!(one_of::<_, _, (&str, ErrorKind)>("a")("bc"), Err(Err::Error(("bc", ErrorKind::OneOf))));
/// assert_eq!(one_of::<_, _, (&str, ErrorKind)>("a")(""), Err(Err::Error(("", ErrorKind::OneOf))));
/// ```
pub fn one_of<I, T, Error: ParseError<I>>(list: T) -> OneOf<T, Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
  T: FindToken<char>,
{
  OneOf {
    list,
    error: PhantomData,
  }
}

/// Parser implementation for [`one_of`]
pub struct OneOf<T, E> {
  list: T,
  error: PhantomData<E>,
}

impl<I, T, Error: ParseError<I>> Parser<I> for OneOf<T, Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
  T: FindToken<char>,
{
  type Output = char;
  type Error = Error;

  #[inline(always)]
  fn process<OM: crate::OutputMode>(
    &mut self,
    i: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    process_satisfy::<OM, _, _, _, _>(
      i,
      |c| self.list.find_token(c),
      |i| Error::from_error_kind(i, ErrorKind::OneOf),
    )
  }
}

//. Recognizes a character that is not in the provided characters.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::character::streaming::none_of;
/// assert_eq!(none_of::<_, _, (_, ErrorKind)>("abc")("z"), Ok(("", 'z')));
/// assert_eq!(none_of::<_, _, (_, ErrorKind)>("ab")("a"), Err(Err::Error(("a", ErrorKind::NoneOf))));
/// assert_eq!(none_of::<_, _, (_, ErrorKind)>("a")(""), Err(Err::Incomplete(Needed::Unknown)));
/// ```
pub fn none_of<I, T, Error: ParseError<I>>(list: T) -> NoneOf<T, Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
  T: FindToken<char>,
{
  NoneOf {
    list,
    error: PhantomData,
  }
}

/// Parser implementation for [`none_of`]
pub struct NoneOf<T, E> {
  list: T,
  error: PhantomData<E>,
}

impl<I, T, Error: ParseError<I>> Parser<I> for NoneOf<T, Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
  T: FindToken<char>,
{
  type Output = char;
  type Error = Error;

  #[inline(always)]
  fn process<OM: crate::OutputMode>(
    &mut self,
    i: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    process_satisfy::<OM, _, _, _, _>(
      i,
      |c| !self.list.find_token(c),
      |i| Error::from_error_kind(i, ErrorKind::NoneOf),
    )
  }
}

/// Matches one byte as a character. Note that the input type will
/// accept a `str`, but not a `&[u8]`, unlike many other nom parsers.
///
/// # Example
///
/// ```
/// # use nom::{character::complete::anychar, Err, error::{Error, ErrorKind}, IResult};
/// fn parser(input: &str) -> IResult<&str, char> {
///     anychar(input)
/// }
///
/// assert_eq!(parser("abc"), Ok(("bc",'a')));
/// assert_eq!(parser(""), Err(Err::Error(Error::new("", ErrorKind::Eof))));
/// ```
pub fn anychar<T, E: ParseError<T>>(input: T) -> IResult<T, char, E>
where
  T: Input,
  <T as Input>::Item: AsChar,
{
  let mut it = input.iter_elements();
  match it.next() {
    None => Err(Err::Error(E::from_error_kind(input, ErrorKind::Eof))),
    Some(c) => Ok((input.take_from(c.len()), c.as_char())),
  }
}

/// Parser implementation for char
pub struct AnyChar<E> {
  e: PhantomData<E>,
}

impl<I, Error: ParseError<I>> Parser<I> for AnyChar<Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
{
  type Output = char;
  type Error = Error;

  fn process<OM: crate::OutputMode>(
    &mut self,
    i: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    match (i).iter_elements().next() {
      None => {
        if OM::Incomplete::is_streaming() {
          Err(Err::Incomplete(Needed::new(1)))
        } else {
          Err(Err::Error(OM::Error::bind(|| {
            Error::from_error_kind(i, ErrorKind::Eof)
          })))
        }
      }
      Some(c) => Ok((i.take_from(c.len()), OM::Output::bind(|| c.as_char()))),
    }
  }
}

/// Recognizes one or more ASCII numerical characters: 0-9
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there's not enough input data,
/// or if no terminating token is found (a non-digit character).
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::streaming::digit1;
/// assert_eq!(digit1::<_, (_, ErrorKind)>("21c"), Ok(("c", "21")));
/// assert_eq!(digit1::<_, (_, ErrorKind)>("c1"), Err(Err::Error(("c1", ErrorKind::Digit))));
/// assert_eq!(digit1::<_, (_, ErrorKind)>(""), Err(Err::Incomplete(Needed::new(1))));
/// ```
pub fn digit1<T, E: ParseError<T>>() -> Digit1<E>
where
  T: Input,
  <T as Input>::Item: AsChar,
{
  Digit1 { e: PhantomData }
}

/// Parser implementation for [`digit1`]
pub struct Digit1<E> {
  e: PhantomData<E>,
}

impl<I: Input, E: ParseError<I>> Parser<I> for Digit1<E>
where
  <I as Input>::Item: AsChar,
{
  type Output = I;

  type Error = E;

  #[inline]
  fn process<OM: crate::OutputMode>(
    &mut self,
    input: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    input.split_at_position_mode1::<OM, _, _>(|item| !item.is_dec_digit(), ErrorKind::Digit)
  }
}

/// Recognizes zero or more spaces, tabs, carriage returns and line feeds.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there's not enough input data,
/// or if no terminating token is found (a non-space character).
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::streaming::multispace0;
/// assert_eq!(multispace0::<_, (_, ErrorKind)>(" \t\n\r21c"), Ok(("21c", " \t\n\r")));
/// assert_eq!(multispace0::<_, (_, ErrorKind)>("Z21c"), Ok(("Z21c", "")));
/// assert_eq!(multispace0::<_, (_, ErrorKind)>(""), Err(Err::Incomplete(Needed::new(1))));
/// ```
pub fn multispace0<I, E: ParseError<I>>() -> MultiSpace0<E>
where
  I: Input,
  <I as Input>::Item: AsChar,
{
  MultiSpace0 { e: PhantomData }
  /*input.split_at_position(|item| {
    let c = item.as_char();
    !(c == ' ' || c == '\t' || c == '\r' || c == '\n')
  })*/
}

/// Parser implementation for [`multispace0`]
pub struct MultiSpace0<E> {
  e: PhantomData<E>,
}

impl<I, Error: ParseError<I>> Parser<I> for MultiSpace0<Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
{
  type Output = I;
  type Error = Error;

  fn process<OM: crate::OutputMode>(
    &mut self,
    i: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    i.split_at_position_mode::<OM, _, _>(|item| {
      let c = item.as_char();
      !(c == ' ' || c == '\t' || c == '\r' || c == '\n')
    })
  }
}
