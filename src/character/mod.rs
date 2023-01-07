//! Character specific parsers and combinators
//!
//! Functions recognizing specific characters

use crate::{
  error::{ErrorKind, ParseError},
  AsChar, Compare, CompareResult, Err, IResult, Input, Needed,
};

#[cfg(test)]
mod tests;

pub mod complete;
pub mod streaming;

/// Tests if byte is ASCII alphabetic: A-Z, a-z
///
/// # Example
///
/// ```
/// # use nom::character::is_alphabetic;
/// assert_eq!(is_alphabetic(b'9'), false);
/// assert_eq!(is_alphabetic(b'a'), true);
/// ```
#[inline]
pub fn is_alphabetic(chr: u8) -> bool {
  matches!(chr, 0x41..=0x5A | 0x61..=0x7A)
}

/// Tests if byte is ASCII digit: 0-9
///
/// # Example
///
/// ```
/// # use nom::character::is_digit;
/// assert_eq!(is_digit(b'a'), false);
/// assert_eq!(is_digit(b'9'), true);
/// ```
#[inline]
pub fn is_digit(chr: u8) -> bool {
  matches!(chr, 0x30..=0x39)
}

/// Tests if byte is ASCII hex digit: 0-9, A-F, a-f
///
/// # Example
///
/// ```
/// # use nom::character::is_hex_digit;
/// assert_eq!(is_hex_digit(b'a'), true);
/// assert_eq!(is_hex_digit(b'9'), true);
/// assert_eq!(is_hex_digit(b'A'), true);
/// assert_eq!(is_hex_digit(b'x'), false);
/// ```
#[inline]
pub fn is_hex_digit(chr: u8) -> bool {
  matches!(chr, 0x30..=0x39 | 0x41..=0x46 | 0x61..=0x66)
}

/// Tests if byte is ASCII octal digit: 0-7
///
/// # Example
///
/// ```
/// # use nom::character::is_oct_digit;
/// assert_eq!(is_oct_digit(b'a'), false);
/// assert_eq!(is_oct_digit(b'9'), false);
/// assert_eq!(is_oct_digit(b'6'), true);
/// ```
#[inline]
pub fn is_oct_digit(chr: u8) -> bool {
  matches!(chr, 0x30..=0x37)
}

/// Tests if byte is ASCII alphanumeric: A-Z, a-z, 0-9
///
/// # Example
///
/// ```
/// # use nom::character::is_alphanumeric;
/// assert_eq!(is_alphanumeric(b'-'), false);
/// assert_eq!(is_alphanumeric(b'a'), true);
/// assert_eq!(is_alphanumeric(b'9'), true);
/// assert_eq!(is_alphanumeric(b'A'), true);
/// ```
#[inline]
pub fn is_alphanumeric(chr: u8) -> bool {
  is_alphabetic(chr) || is_digit(chr)
}

/// Tests if byte is ASCII space or tab
///
/// # Example
///
/// ```
/// # use nom::character::is_space;
/// assert_eq!(is_space(b'\n'), false);
/// assert_eq!(is_space(b'\r'), false);
/// assert_eq!(is_space(b' '), true);
/// assert_eq!(is_space(b'\t'), true);
/// ```
#[inline]
pub fn is_space(chr: u8) -> bool {
  chr == b' ' || chr == b'\t'
}

/// Tests if byte is ASCII newline: \n
///
/// # Example
///
/// ```
/// # use nom::character::is_newline;
/// assert_eq!(is_newline(b'\n'), true);
/// assert_eq!(is_newline(b'\r'), false);
/// assert_eq!(is_newline(b' '), false);
/// assert_eq!(is_newline(b'\t'), false);
/// ```
#[inline]
pub fn is_newline(chr: u8) -> bool {
  chr == b'\n'
}

/// Recognizes one character.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there's not enough input data.
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
pub fn char<I, Error: ParseError<I>>(c: char) -> impl Fn(I) -> IResult<I, char, Error>
where
  I: Input,
  <I as Input>::Item: AsChar,
{
  move |i: I| match (i).iter_elements().next().map(|t| {
    let b = t.as_char() == c;
    (&c, b)
  }) {
    None => {
      if I::is_streaming() {
        Err(Err::Incomplete(Needed::new(c.len() - i.input_len())))
      } else {
        Err(Err::Error(Error::from_char(i, c)))
      }
    }
    Some((_, false)) => Err(Err::Error(Error::from_char(i, c))),
    Some((c, true)) => Ok((i.take_from(c.len()), c.as_char())),
  }
}

/// Recognizes an end of line (both '\n' and '\r\n').
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::streaming::line_ending;
/// assert_eq!(line_ending::<_, (_, ErrorKind)>("\r\nc"), Ok(("c", "\r\n")));
/// assert_eq!(line_ending::<_, (_, ErrorKind)>("ab\r\nc"), Err(Err::Error(("ab\r\nc", ErrorKind::CrLf))));
/// assert_eq!(line_ending::<_, (_, ErrorKind)>(""), Err(Err::Incomplete(Needed::new(1))));
/// ```
pub fn line_ending<I, E: ParseError<I>>(input: I) -> IResult<I, I, E>
where
  I: Input,
  I: Compare<&'static str>,
{
  match input.compare("\n") {
    CompareResult::Ok => Ok(input.take_split(1)),
    CompareResult::Incomplete => {
      if I::is_streaming() {
        Err(Err::Incomplete(Needed::new(1)))
      } else {
        Err(Err::Error(E::from_error_kind(input, ErrorKind::CrLf)))
      }
    }
    CompareResult::Error => {
      match input.compare("\r\n") {
        //FIXME: is this the right index?
        CompareResult::Ok => Ok(input.take_split(2)),
        CompareResult::Incomplete => {
          if I::is_streaming() {
            Err(Err::Incomplete(Needed::new(2)))
          } else {
            Err(Err::Error(E::from_error_kind(input, ErrorKind::CrLf)))
          }
        }
        CompareResult::Error => Err(Err::Error(E::from_error_kind(input, ErrorKind::CrLf))),
      }
    }
  }
}
