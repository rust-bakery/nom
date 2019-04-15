#[macro_use]
mod macros;

pub mod streaming;
pub mod complete;

use internal::{Err, IResult, Needed};
use error::ParseError;
use ::lib::std::ops::RangeFrom;
use traits::{need_more, AsChar, AtEof, FindToken, InputIter, Slice};
use error::ErrorKind;

// backward compatible version that can handle streaming and complete versions at the same time
#[doc(hidden)]
pub fn char<I, Error: ParseError<I>>(c: char) -> impl Fn(I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter + AtEof,
  <I as InputIter>::Item: AsChar,
{
  move |i: I| match (i).iter_elements().next().map(|t| {
    let b = t.as_char() == c;
    (&c, b)
  }) {
    None => need_more(i, Needed::Size(1)),
    Some((_, false)) => {
      //let e: ErrorKind = ErrorKind::Char;
      Err(Err::Error(Error::from_char(i, c)))
    }
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
  }
}

// backward compatible version that can handle streaming and complete versions at the same time
#[doc(hidden)]
pub fn one_of<I, T, Error: ParseError<I>>(list: T) -> impl Fn(I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter + AtEof,
  <I as InputIter>::Item: AsChar + Copy,
  T: FindToken<<I as InputIter>::Item>,
{
  move |i: I| match (i).iter_elements().next().map(|c| (c, list.find_token(c))) {
    None => need_more(i, Needed::Size(1)),
    Some((_, false)) => Err(Err::Error(Error::from_error_kind(i, ErrorKind::OneOf))),
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
  }
}

// backward compatible version that can handle streaming and complete versions at the same time
#[doc(hidden)]
pub fn none_of<I, T, Error: ParseError<I>>(list: T) -> impl Fn(I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter + AtEof,
  <I as InputIter>::Item: AsChar + Copy,
  T: FindToken<<I as InputIter>::Item>,
{
  move |i: I| match (i).iter_elements().next().map(|c| (c, !list.find_token(c))) {
    None => need_more(i, Needed::Size(1)),
    Some((_, false)) => Err(Err::Error(Error::from_error_kind(i, ErrorKind::NoneOf))),
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
  }
}

named!(#[doc="Matches a newline character '\\n'"], pub newline<char>, char!('\n'));

named!(#[doc="Matches a tab character '\\t'"], pub tab<char>, char!('\t'));



/// Tests if byte is ASCII alphabetic: A-Z, a-z
#[inline]
pub fn is_alphabetic(chr: u8) -> bool {
  (chr >= 0x41 && chr <= 0x5A) || (chr >= 0x61 && chr <= 0x7A)
}

/// Tests if byte is ASCII digit: 0-9
#[inline]
pub fn is_digit(chr: u8) -> bool {
  chr >= 0x30 && chr <= 0x39
}

/// Tests if byte is ASCII hex digit: 0-9, A-F, a-f
#[inline]
pub fn is_hex_digit(chr: u8) -> bool {
  (chr >= 0x30 && chr <= 0x39) || (chr >= 0x41 && chr <= 0x46) || (chr >= 0x61 && chr <= 0x66)
}

/// Tests if byte is ASCII octal digit: 0-7
#[inline]
pub fn is_oct_digit(chr: u8) -> bool {
  chr >= 0x30 && chr <= 0x37
}

/// Tests if byte is ASCII alphanumeric: A-Z, a-z, 0-9
#[inline]
pub fn is_alphanumeric(chr: u8) -> bool {
  is_alphabetic(chr) || is_digit(chr)
}

/// Tests if byte is ASCII space or tab
#[inline]
pub fn is_space(chr: u8) -> bool {
  chr == b' ' || chr == b'\t'
}

