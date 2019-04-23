//! Character specific parsers and combinators, complete input version.
//!
//! Functions recognizing specific characters.

use internal::{Err, IResult, Needed};
use error::ParseError;
use ::lib::std::ops::{Range, RangeFrom, RangeTo};
use traits::{AsChar, AtEof, FindToken, InputIter, InputLength, InputTakeAtPosition, Slice};
use traits::{Compare, CompareResult};
use error::ErrorKind;

/// Recognizes one character.
///
/// *complete version*: Will return an error if there's not enough input data.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind};
/// # use nom::character::complete::char;
/// # fn main() {
/// assert_eq!(char::<_, (&str, ErrorKind)>('a')("abc"), Ok(("bc", 'a')));
/// assert_eq!(char::<_, (&str, ErrorKind)>('a')("bc"), Err(Err::Error(("bc", ErrorKind::Char))));
/// assert_eq!(char::<_, (&str, ErrorKind)>('a')(""), Err(Err::Error(("", ErrorKind::Char))));
/// # }
/// ```
pub fn char<I, Error: ParseError<I>>(c: char) -> impl Fn(I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar,
{
  move |i: I| match (i).iter_elements().next().map(|t| {
    let b = t.as_char() == c;
    (&c, b)
  }) {
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
    _ => Err(Err::Error(Error::from_char(i, c))),
  }
}

/// Recognizes one of the provided characters.
///
/// *complete version*: Will return an error if there's not enough input data.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind};
/// # use nom::character::complete::one_of;
/// # fn main() {
/// assert_eq!(one_of::<_, _, (&str, ErrorKind)>("abc")("b"), Ok(("", 'b')));
/// assert_eq!(one_of::<_, _, (&str, ErrorKind)>("a")("bc"), Err(Err::Error(("bc", ErrorKind::OneOf))));
/// assert_eq!(one_of::<_, _, (&str, ErrorKind)>("a")(""), Err(Err::Error(("", ErrorKind::OneOf))));
/// # }
/// ```
pub fn one_of<I, T, Error: ParseError<I>>(list: T) -> impl Fn(I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar + Copy,
  T: FindToken<<I as InputIter>::Item>,
{
  move |i: I| match (i).iter_elements().next().map(|c| (c, list.find_token(c))) {
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
    _ => Err(Err::Error(Error::from_error_kind(i, ErrorKind::OneOf))),
  }
}

/// Recognizes a character that is not in the provided characters.
///
/// *complete version*: Will return an error if there's not enough input data.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind};
/// # use nom::character::complete::none_of;
/// # fn main() {
/// assert_eq!(none_of::<_, _, (&str, ErrorKind)>("abc")("z"), Ok(("", 'z')));
/// assert_eq!(none_of::<_, _, (&str, ErrorKind)>("ab")("a"), Err(Err::Error(("a", ErrorKind::NoneOf))));
/// assert_eq!(none_of::<_, _, (&str, ErrorKind)>("a")(""), Err(Err::Error(("", ErrorKind::NoneOf))));
/// # }
/// ```
pub fn none_of<I, T, Error: ParseError<I>>(list: T) -> impl Fn(I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar + Copy,
  T: FindToken<<I as InputIter>::Item>,
{
  move |i: I| match (i).iter_elements().next().map(|c| (c, !list.find_token(c))) {
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
    _ => Err(Err::Error(Error::from_error_kind(i, ErrorKind::NoneOf))),
  }
}

/// Recognizes the string "\r\n".
///
/// *complete version*: Will return an error if there's not enough input data.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult};
/// # use nom::character::complete::crlf;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     crlf(input)
/// }
///
/// assert_eq!(parser("\r\nc"), Ok(("c", "\r\n")));
/// assert_eq!(parser("ab\r\nc"), Err(Err::Error(("ab\r\nc", ErrorKind::CrLf))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::CrLf))));
/// # }
/// ```
pub fn crlf<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter,
  T: Compare<&'static str>,
{
  match input.compare("\r\n") {
    //FIXME: is this the right index?
    CompareResult::Ok => Ok((input.slice(2..), input.slice(0..2))),
    _ => {
      let e: ErrorKind = ErrorKind::CrLf;
      Err(Err::Error(E::from_error_kind(input, e)))
    }
  }
}

//FIXME: remove?
//FIXME: there's still an incomplete
/// Recognizes a string of any char except '\r' or '\n'.
///
/// *complete version*: Will return an error if there's not enough input data.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::not_line_ending;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     not_line_ending(input)
/// }
///
/// assert_eq!(parser("ab\r\nc"), Ok(("\r\nc", "ab")));
/// assert_eq!(parser("abc"), Err(Err::Incomplete(Needed::Unknown)));
/// assert_eq!(parser(""), Err(Err::Incomplete(Needed::Unknown)));
/// # }
/// ```
pub fn not_line_ending<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength + AtEof,
  T: Compare<&'static str>,
  <T as InputIter>::Item: AsChar,
  <T as InputIter>::RawItem: AsChar,
{
  match input.position(|item| {
    let c = item.as_char();
    c == '\r' || c == '\n'
  }) {
    None => {
      if input.at_eof() {
        Ok((input.slice(input.input_len()..), input))
      } else {
        Err(Err::Incomplete(Needed::Unknown))
      }
    }
    Some(index) => {
      let mut it = input.slice(index..).iter_elements();
      let nth = it.next().unwrap().as_char();
      if nth == '\r' {
        let sliced = input.slice(index..);
        let comp = sliced.compare("\r\n");
        match comp {
          //FIXME: calculate the right index
          CompareResult::Ok => Ok((input.slice(index..), input.slice(..index))),
          _ => {
            let e: ErrorKind = ErrorKind::Tag;
            Err(Err::Error(E::from_error_kind(input, e)))
          }
        }
      } else {
        Ok((input.slice(index..), input.slice(..index)))
      }
    }
  }
}

/// Recognizes an end of line (both '\n' and '\r\n').
///
/// *complete version*: Will return an error if there's not enough input data.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::line_ending;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     line_ending(input)
/// }
///
/// assert_eq!(parser("\r\nc"), Ok(("c", "\r\n")));
/// assert_eq!(parser("ab\r\nc"), Err(Err::Error(("ab\r\nc", ErrorKind::CrLf))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::CrLf))));
/// # }
/// ```
pub fn line_ending<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength,
  T: Compare<&'static str>,
{
  match input.compare("\n") {
    CompareResult::Ok => Ok((input.slice(1..), input.slice(0..1))),
    CompareResult::Incomplete => Err(Err::Error(E::from_error_kind(input, ErrorKind::CrLf))),
    CompareResult::Error => {
      match input.compare("\r\n") {
        //FIXME: is this the right index?
        CompareResult::Ok => Ok((input.slice(2..), input.slice(0..2))),
        _ => Err(Err::Error(E::from_error_kind(input, ErrorKind::CrLf))),
      }
    }
  }
}

//FIXME: remove
/// Alias for [`line_ending`].
///
/// *complete version*: Will return an error if there's not enough input data.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::eol;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     eol(input)
/// }
///
/// assert_eq!(parser("\r\nc"), Ok(("c", "\r\n")));
/// assert_eq!(parser("ab\r\nc"), Err(Err::Error(("ab\r\nc", ErrorKind::CrLf))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::CrLf))));
/// # }
/// ```
pub fn eol<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength,
  T: Compare<&'static str>,
{
  line_ending(input)
}

/// Matches a newline character '\n'.
///
/// *complete version*: Will return an error if there's not enough input data.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::newline;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, char> {
///     newline(input)
/// }
///
/// assert_eq!(parser("\nc"), Ok(("c", '\n')));
/// assert_eq!(parser("\r\nc"), Err(Err::Error(("\r\nc", ErrorKind::Char))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Char))));
/// # }
/// ```
pub fn newline<I, Error: ParseError<I>>(input: I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar,
{
  char('\n')(input)
}

/// Matches a tab character '\t'.
///
/// *complete version*: Will return an error if there's not enough input data.
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::tab;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, char> {
///     tab(input)
/// }
///
/// assert_eq!(parser("\tc"), Ok(("c", '\t')));
/// assert_eq!(parser("\r\nc"), Err(Err::Error(("\r\nc", ErrorKind::Char))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Char))));
/// # }
/// ```
pub fn tab<I, Error: ParseError<I>>(input: I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar,
{
  char('\t')(input)
}

/// Matches one byte as a character. Note that the input type will
/// accept a `str`, but not a `&[u8]`, unlike many other nom parsers.
///
/// *complete version*: Will return an error if there's not enough input data.
///
/// # Example
///
/// ```
/// # use nom::{character::complete::anychar, Err, error::ErrorKind, IResult};
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, char> {
///     anychar(input)
/// }
///
/// assert_eq!(parser("abc"), Ok(("bc",'a')));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Eof))));
/// # }
/// ```
pub fn anychar<T, E: ParseError<T>>(input: T) -> IResult<T, char, E>
where
  T: InputIter + InputLength + Slice<RangeFrom<usize>>,
  <T as InputIter>::Item: AsChar,
{
  let mut it = input.iter_indices();
  match it.next() {
    None => Err(Err::Error(E::from_error_kind(input, ErrorKind::Eof))),
    Some((_, c)) => match it.next() {
      None => Ok((input.slice(input.input_len()..), c.as_char())),
      Some((idx, _)) => Ok((input.slice(idx..), c.as_char())),
    },
  }
}

//FIXME: remove?
/// Recognizes one or more lowercase and uppercase alphabetic characters.
///
/// * For ASCII strings: a-zA-Z
/// * For UTF8 strings, any alphabetic code point (ie, not only the ASCII ones)
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non alphabetic character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::alpha;
/// # #[cfg(feature = "alloc")]
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     alpha(input)
/// }
///
/// assert_eq!(parser("ab1c"), Ok(("1c", "ab")));
/// assert_eq!(parser("1c"), Err(Err::Error(("1c", ErrorKind::Alpha))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Alpha))));
/// # }
/// # #[cfg(not(feature = "alloc"))]
/// # fn main() {}
/// ```
pub fn alpha<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  alpha1(input)
}

/// Recognizes zero or more lowercase and uppercase alphabetic characters.
///
/// * For ASCII strings: a-zA-Z
/// * For UTF8 strings, any alphabetic code point (ie, not only the ASCII ones)
///
/// *complete version*: Will return the whole input if no terminating token is found (a non
/// alphabetic character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::alpha0;
/// # #[cfg(feature = "alloc")]
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     alpha0(input)
/// }
///
/// assert_eq!(parser("ab1c"), Ok(("1c", "ab")));
/// assert_eq!(parser("1c"), Ok(("1c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// # }
/// # #[cfg(not(feature = "alloc"))]
/// # fn main() {}
/// ```
pub fn alpha0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position_complete(|item| !item.is_alpha())
}

/// Recognizes one or more lowercase and uppercase alphabetic characters.
///
/// * For ASCII strings: a-zA-Z
/// * For UTF8 strings, any alphabetic code point (ie, not only the ASCII ones)
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found  (a non alphabetic character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::alpha1;
/// # #[cfg(feature = "alloc")]
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     alpha1(input)
/// }
///
/// assert_eq!(parser("aB1c"), Ok(("1c", "aB")));
/// assert_eq!(parser("1c"), Err(Err::Error(("1c", ErrorKind::Alpha))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Alpha))));
/// # }
/// # #[cfg(not(feature = "alloc"))]
/// # fn main() {}
/// ```
pub fn alpha1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1_complete(|item| !item.is_alpha(), ErrorKind::Alpha)
}

//FIXME: remove?
/// Recognizes one or more numerical characters: 0-9
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non digit character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::digit;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     digit(input)
/// }
///
/// assert_eq!(parser("21c"), Ok(("c", "21")));
/// assert_eq!(parser("c1"), Err(Err::Error(("c1", ErrorKind::Digit))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Digit))));
/// # }
/// ```
pub fn digit<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  digit1(input)
}

/// Recognizes zero or more numerical characters: 0-9
///
/// *complete version*: Will return the whole input if no terminating token is found (a non digit
/// character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::digit0;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     digit0(input)
/// }
///
/// assert_eq!(parser("21c"), Ok(("c", "21")));
/// assert_eq!(parser("a21c"), Ok(("a21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// # }
/// ```
pub fn digit0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position_complete(|item| !item.is_dec_digit())
}

/// Recognizes one or more numerical characters: 0-9
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non digit character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::digit1;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     digit1(input)
/// }
///
/// assert_eq!(parser("21c"), Ok(("c", "21")));
/// assert_eq!(parser("c1"), Err(Err::Error(("c1", ErrorKind::Digit))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Digit))));
/// # }
/// ```
pub fn digit1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1_complete(|item| !item.is_dec_digit(), ErrorKind::Digit)
}

//FIXME: remove?
/// Recognizes one or more hexadecimal numerical characters: 0-9, A-F, a-f
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non hexadecimal digit character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::hex_digit;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     hex_digit(input)
/// }
///
/// assert_eq!(parser("21cZ"), Ok(("Z", "21c")));
/// assert_eq!(parser("H2"), Err(Err::Error(("H2", ErrorKind::HexDigit))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::HexDigit))));
/// # }
/// ```
pub fn hex_digit<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  hex_digit1(input)
}

/// Recognizes zero or more hexadecimal numerical characters: 0-9, A-F, a-f
///
/// *complete version*: Will return the whole input if no terminating token is found (a non hexadecimal digit character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::hex_digit0;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     hex_digit0(input)
/// }
///
/// assert_eq!(parser("21cZ"), Ok(("Z", "21c")));
/// assert_eq!(parser("Z21c"), Ok(("Z21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// # }
/// ```
pub fn hex_digit0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position_complete(|item| !item.is_hex_digit())
}
/// Recognizes one or more hexadecimal numerical characters: 0-9, A-F, a-f
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non hexadecimal digit character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::hex_digit1;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     hex_digit1(input)
/// }
///
/// assert_eq!(parser("21cZ"), Ok(("Z", "21c")));
/// assert_eq!(parser("H2"), Err(Err::Error(("H2", ErrorKind::HexDigit))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::HexDigit))));
/// # }
/// ```
pub fn hex_digit1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1_complete(|item| !item.is_hex_digit(), ErrorKind::HexDigit)
}

//FIXME: remove?
/// Recognizes one or more octal characters: 0-7
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non octal digit character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::oct_digit;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     oct_digit(input)
/// }
///
/// assert_eq!(parser("21cZ"), Ok(("cZ", "21")));
/// assert_eq!(parser("H2"), Err(Err::Error(("H2", ErrorKind::OctDigit))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::OctDigit))));
/// # }
/// ```
pub fn oct_digit<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  oct_digit1(input)
}

/// Recognizes zero or more octal characters: 0-7
///
/// *complete version*: Will return the whole input if no terminating token is found (a non octal
/// digit character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::oct_digit0;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     oct_digit0(input)
/// }
///
/// assert_eq!(parser("21cZ"), Ok(("cZ", "21")));
/// assert_eq!(parser("Z21c"), Ok(("Z21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// # }
/// ```
pub fn oct_digit0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position_complete(|item| !item.is_oct_digit())
}

/// Recognizes one or more octal characters: 0-7
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non octal digit character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::oct_digit1;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     oct_digit1(input)
/// }
///
/// assert_eq!(parser("21cZ"), Ok(("cZ", "21")));
/// assert_eq!(parser("H2"), Err(Err::Error(("H2", ErrorKind::OctDigit))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::OctDigit))));
/// # }
/// ```
pub fn oct_digit1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1_complete(|item| !item.is_oct_digit(), ErrorKind::OctDigit)
}

//FIXME: remove?
/// Recognizes one or more numerical and alphabetic characters.
///
/// * For ASCII strings: 0-9a-zA-Z
/// * For UTF8 strings, 0-9 and any alphabetic code point (ie, not only the ASCII ones)
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non alphanumerical character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::alphanumeric;
/// # #[cfg(feature = "alloc")]
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     alphanumeric(input)
/// }
///
/// assert_eq!(parser("21cZ%1"), Ok(("%1", "21cZ")));
/// assert_eq!(parser("&H2"), Err(Err::Error(("&H2", ErrorKind::AlphaNumeric))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::AlphaNumeric))));
/// # }
/// # #[cfg(not(feature = "alloc"))]
/// # fn main() {}
/// ```
pub fn alphanumeric<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  alphanumeric1(input)
}

/// Recognizes zero or more numerical and alphabetic characters.
///
/// * For ASCII strings: 0-9a-zA-Z
/// * For UTF8 strings, 0-9 and any alphabetic code point (ie, not only the ASCII ones)
///
/// *complete version*: Will return the whole input if no terminating token is found (a non
/// alphanumerical character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::alphanumeric0;
/// # #[cfg(feature = "alloc")]
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     alphanumeric0(input)
/// }
///
/// assert_eq!(parser("21cZ%1"), Ok(("%1", "21cZ")));
/// assert_eq!(parser("&Z21c"), Ok(("&Z21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// # }
/// # #[cfg(not(feature = "alloc"))]
/// # fn main() {}
/// ```
pub fn alphanumeric0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position_complete(|item| !item.is_alphanum())
}

/// Recognizes one or more numerical and alphabetic characters.
///
/// * For ASCII strings: 0-9a-zA-Z
/// * For UTF8 strings, 0-9 and any alphabetic code point (ie, not only the ASCII ones)
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non alphanumerical character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::alphanumeric1;
/// # #[cfg(feature = "alloc")]
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     alphanumeric1(input)
/// }
///
/// assert_eq!(parser("21cZ%1"), Ok(("%1", "21cZ")));
/// assert_eq!(parser("&H2"), Err(Err::Error(("&H2", ErrorKind::AlphaNumeric))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::AlphaNumeric))));
/// # }
/// # #[cfg(not(feature = "alloc"))]
/// # fn main() {}
/// ```
pub fn alphanumeric1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1_complete(|item| !item.is_alphanum(), ErrorKind::AlphaNumeric)
}

//FIXME: remove?
/// Recognizes one or more spaces and tabs.
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non space character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::space;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     space(input)
/// }
///
/// assert_eq!(parser(" \t21c"), Ok(("21c", " \t")));
/// assert_eq!(parser("H2"), Err(Err::Error(("H2", ErrorKind::Space))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Space))));
/// # }
/// ```
pub fn space<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  space1(input)
}

/// Recognizes zero or more spaces and tabs.
///
/// *complete version*: Will return the whole input if no terminating token is found (a non space
/// character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::space0;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     space0(input)
/// }
///
/// assert_eq!(parser(" \t21c"), Ok(("21c", " \t")));
/// assert_eq!(parser("Z21c"), Ok(("Z21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// # }
/// ```
pub fn space0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position_complete(|item| {
    let c = item.clone().as_char();
    !(c == ' ' || c == '\t')
  })
}

/// Recognizes one or more spaces and tabs.
///
/// *complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non space character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::space1;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     space1(input)
/// }
///
/// assert_eq!(parser(" \t21c"), Ok(("21c", " \t")));
/// assert_eq!(parser("H2"), Err(Err::Error(("H2", ErrorKind::Space))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Space))));
/// # }
/// ```
pub fn space1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position1_complete(
    |item| {
      let c = item.clone().as_char();
      !(c == ' ' || c == '\t')
    },
    ErrorKind::Space,
  )
}

//FIXME: remove?
/// Recognizes one or more spaces, tabs, carriage returns and line feeds.
///
/// *complete version*: will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non space character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::multispace;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     multispace(input)
/// }
///
/// assert_eq!(parser(" \t\n\r21c"), Ok(("21c", " \t\n\r")));
/// assert_eq!(parser("H2"), Err(Err::Error(("H2", ErrorKind::MultiSpace))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::MultiSpace))));
/// # }
/// ```
pub fn multispace<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  multispace1(input)
}

/// Recognizes zero or more spaces, tabs, carriage returns and line feeds.
///
/// *complete version*: will return the whole input if no terminating token is found (a non space
/// character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::multispace0;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     multispace0(input)
/// }
///
/// assert_eq!(parser(" \t\n\r21c"), Ok(("21c", " \t\n\r")));
/// assert_eq!(parser("Z21c"), Ok(("Z21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// # }
/// ```
pub fn multispace0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position_complete(|item| {
    let c = item.clone().as_char();
    !(c == ' ' || c == '\t' || c == '\r' || c == '\n')
  })
}
/// Recognizes one or more spaces, tabs, carriage returns and line feeds.
///
/// *complete version*: will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non space character).
///
/// # Example
///
/// ```
/// # use nom::{Err, error::ErrorKind, IResult, Needed};
/// # use nom::character::complete::multispace1;
/// # fn main() {
/// fn parser(input: &str) -> IResult<&str, &str> {
///     multispace1(input)
/// }
///
/// assert_eq!(parser(" \t\n\r21c"), Ok(("21c", " \t\n\r")));
/// assert_eq!(parser("H2"), Err(Err::Error(("H2", ErrorKind::MultiSpace))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::MultiSpace))));
/// # }
/// ```
pub fn multispace1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position1_complete(
    |item| {
      let c = item.clone().as_char();
      !(c == ' ' || c == '\t' || c == '\r' || c == '\n')
    },
    ErrorKind::MultiSpace,
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Err, Needed};

  macro_rules! assert_parse(
    ($left: expr, $right: expr) => {
      let res: $crate::IResult<_, _, (_, ErrorKind)> = $left;
      assert_eq!(res, $right);
    };
  );


  #[test]
  fn character() {
    let empty: &[u8] = b"";
    let a: &[u8] = b"abcd";
    let b: &[u8] = b"1234";
    let c: &[u8] = b"a123";
    let d: &[u8] = "azé12".as_bytes();
    let e: &[u8] = b" ";
    let f: &[u8] = b" ;";
    //assert_eq!(alpha::<_, (_, ErrorKind)>(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_parse!(alpha(a), Ok((empty, a)));
    assert_eq!(
      alpha(b),
      Err(Err::Error((b, ErrorKind::Alpha)))
    );
    assert_eq!(alpha::<_, (_, ErrorKind)>(c), Ok((&c[1..], &b"a"[..])));
    assert_eq!(alpha::<_, (_, ErrorKind)>(d), Ok(("é12".as_bytes(), &b"az"[..])));
    assert_eq!(
      digit(a),
      Err(Err::Error((a, ErrorKind::Digit)))
    );
    assert_eq!(digit::<_, (_, ErrorKind)>(b), Ok((empty, b)));
    assert_eq!(
      digit(c),
      Err(Err::Error((c, ErrorKind::Digit)))
    );
    assert_eq!(
      digit(d),
      Err(Err::Error((d, ErrorKind::Digit)))
    );
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(a), Ok((empty, a)));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(b), Ok((empty, b)));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(c), Ok((empty, c)));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(d), Ok(("zé12".as_bytes(), &b"a"[..])));
    assert_eq!(
      hex_digit(e),
      Err(Err::Error((e, ErrorKind::HexDigit)))
    );
    assert_eq!(
      oct_digit(a),
      Err(Err::Error((a, ErrorKind::OctDigit)))
    );
    assert_eq!(oct_digit::<_, (_, ErrorKind)>(b), Ok((empty, b)));
    assert_eq!(
      oct_digit(c),
      Err(Err::Error((c, ErrorKind::OctDigit)))
    );
    assert_eq!(
      oct_digit(d),
      Err(Err::Error((d, ErrorKind::OctDigit)))
    );
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(a), Ok((empty, a)));
    //assert_eq!(fix_error!(b,(), alphanumeric), Ok((empty, b)));
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(c), Ok((empty, c)));
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(d), Ok(("é12".as_bytes(), &b"az"[..])));
    assert_eq!(space::<_, (_, ErrorKind)>(e), Ok((empty, e)));
    assert_eq!(space::<_, (_, ErrorKind)>(f), Ok((&b";"[..], &b" "[..])));
  }

  #[cfg(feature = "alloc")]
  #[test]
  fn character_s() {
    let empty = "";
    let a = "abcd";
    let b = "1234";
    let c = "a123";
    let d = "azé12";
    let e = " ";
    assert_eq!(alpha::<_, (_, ErrorKind)>(a), Ok((empty, a)));
    assert_eq!(
      alpha(b),
      Err(Err::Error((b, ErrorKind::Alpha)))
    );
    assert_eq!(alpha::<_, (_, ErrorKind)>(c), Ok((&c[1..], &"a"[..])));
    assert_eq!(alpha::<_, (_, ErrorKind)>(d), Ok(("12", &"azé"[..])));
    assert_eq!(
      digit(a),
      Err(Err::Error((a, ErrorKind::Digit)))
    );
    assert_eq!(digit::<_, (_, ErrorKind)>(b), Ok((empty, b)));
    assert_eq!(
      digit(c),
      Err(Err::Error((c, ErrorKind::Digit)))
    );
    assert_eq!(
      digit(d),
      Err(Err::Error((d, ErrorKind::Digit)))
    );
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(a), Ok((empty, a)));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(b), Ok((empty, b)));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(c), Ok((empty, c)));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(d), Ok(("zé12", &"a"[..])));
    assert_eq!(
      hex_digit(e),
      Err(Err::Error((e, ErrorKind::HexDigit)))
    );
    assert_eq!(
      oct_digit(a),
      Err(Err::Error((a, ErrorKind::OctDigit)))
    );
    assert_eq!(oct_digit::<_, (_, ErrorKind)>(b), Ok((empty, b)));
    assert_eq!(
      oct_digit(c),
      Err(Err::Error((c, ErrorKind::OctDigit)))
    );
    assert_eq!(
      oct_digit(d),
      Err(Err::Error((d, ErrorKind::OctDigit)))
    );
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(a), Ok((empty, a)));
    //assert_eq!(fix_error!(b,(), alphanumeric), Ok((empty, b)));
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(c), Ok((empty, c)));
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(d), Ok((empty, d)));
    assert_eq!(space::<_, (_, ErrorKind)>(e), Ok((empty, e)));
  }

  use traits::Offset;
  #[test]
  fn offset() {
    let a = &b"abcd;"[..];
    let b = &b"1234;"[..];
    let c = &b"a123;"[..];
    let d = &b" \t;"[..];
    let e = &b" \t\r\n;"[..];
    let f = &b"123abcDEF;"[..];

    match alpha::<_, (_, ErrorKind)>(a) {
      Ok((i, _)) => {
        assert_eq!(a.offset(i) + i.len(), a.len());
      }
      _ => panic!("wrong return type in offset test for alpha"),
    }
    match digit::<_, (_, ErrorKind)>(b) {
      Ok((i, _)) => {
        assert_eq!(b.offset(i) + i.len(), b.len());
      }
      _ => panic!("wrong return type in offset test for digit"),
    }
    match alphanumeric::<_, (_, ErrorKind)>(c) {
      Ok((i, _)) => {
        assert_eq!(c.offset(i) + i.len(), c.len());
      }
      _ => panic!("wrong return type in offset test for alphanumeric"),
    }
    match space::<_, (_, ErrorKind)>(d) {
      Ok((i, _)) => {
        assert_eq!(d.offset(i) + i.len(), d.len());
      }
      _ => panic!("wrong return type in offset test for space"),
    }
    match multispace::<_, (_, ErrorKind)>(e) {
      Ok((i, _)) => {
        assert_eq!(e.offset(i) + i.len(), e.len());
      }
      _ => panic!("wrong return type in offset test for multispace"),
    }
    match hex_digit::<_, (_, ErrorKind)>(f) {
      Ok((i, _)) => {
        assert_eq!(f.offset(i) + i.len(), f.len());
      }
      _ => panic!("wrong return type in offset test for hex_digit"),
    }
    match oct_digit::<_, (_, ErrorKind)>(f) {
      Ok((i, _)) => {
        assert_eq!(f.offset(i) + i.len(), f.len());
      }
      _ => panic!("wrong return type in offset test for oct_digit"),
    }
  }

  #[test]
  fn is_not_line_ending_bytes() {
    let a: &[u8] = b"ab12cd\nefgh";
    assert_eq!(not_line_ending::<_, (_, ErrorKind)>(a), Ok((&b"\nefgh"[..], &b"ab12cd"[..])));

    let b: &[u8] = b"ab12cd\nefgh\nijkl";
    assert_eq!(
      not_line_ending::<_, (_, ErrorKind)>(b),
      Ok((&b"\nefgh\nijkl"[..], &b"ab12cd"[..]))
    );

    let c: &[u8] = b"ab12cd\r\nefgh\nijkl";
    assert_eq!(
      not_line_ending::<_, (_, ErrorKind)>(c),
      Ok((&b"\r\nefgh\nijkl"[..], &b"ab12cd"[..]))
    );

    let d: &[u8] = b"ab12cd";
    assert_eq!(not_line_ending::<_, (_, ErrorKind)>(d), Err(Err::Incomplete(Needed::Unknown)));
  }

  #[test]
  fn is_not_line_ending_str() {
    /*
    let a: &str = "ab12cd\nefgh";
    assert_eq!(not_line_ending(a), Ok((&"\nefgh"[..], &"ab12cd"[..])));

    let b: &str = "ab12cd\nefgh\nijkl";
    assert_eq!(not_line_ending(b), Ok((&"\nefgh\nijkl"[..], &"ab12cd"[..])));

    let c: &str = "ab12cd\r\nefgh\nijkl";
    assert_eq!(not_line_ending(c), Ok((&"\r\nefgh\nijkl"[..], &"ab12cd"[..])));

    let d = "βèƒôřè\nÂßÇáƒƭèř";
    assert_eq!(not_line_ending(d), Ok((&"\nÂßÇáƒƭèř"[..], &"βèƒôřè"[..])));

    let e = "βèƒôřè\r\nÂßÇáƒƭèř";
    assert_eq!(not_line_ending(e), Ok((&"\r\nÂßÇáƒƭèř"[..], &"βèƒôřè"[..])));
    */

    let f = "βèƒôřè\rÂßÇáƒƭèř";
    assert_eq!(
      not_line_ending(f),
      Err(Err::Error((f, ErrorKind::Tag)))
    );

    let g2: &str = "ab12cd";
    assert_eq!(not_line_ending::<_, (_, ErrorKind)>(g2), Err(Err::Incomplete(Needed::Unknown)));
  }

  #[test]
  fn hex_digit_test() {
    let i = &b"0123456789abcdefABCDEF;"[..];
    assert_parse!(hex_digit(i), Ok((&b";"[..], &i[..i.len() - 1])));

    let i = &b"g"[..];
    assert_parse!(
      hex_digit(i),
      Err(Err::Error(error_position!(i, ErrorKind::HexDigit)))
    );

    let i = &b"G"[..];
    assert_parse!(
      hex_digit(i),
      Err(Err::Error(error_position!(i, ErrorKind::HexDigit)))
    );

    assert!(::character::is_hex_digit(b'0'));
    assert!(::character::is_hex_digit(b'9'));
    assert!(::character::is_hex_digit(b'a'));
    assert!(::character::is_hex_digit(b'f'));
    assert!(::character::is_hex_digit(b'A'));
    assert!(::character::is_hex_digit(b'F'));
    assert!(!::character::is_hex_digit(b'g'));
    assert!(!::character::is_hex_digit(b'G'));
    assert!(!::character::is_hex_digit(b'/'));
    assert!(!::character::is_hex_digit(b':'));
    assert!(!::character::is_hex_digit(b'@'));
    assert!(!::character::is_hex_digit(b'\x60'));
  }

  #[test]
  fn oct_digit_test() {
    let i = &b"01234567;"[..];
    assert_parse!(oct_digit(i), Ok((&b";"[..], &i[..i.len() - 1])));

    let i = &b"8"[..];
    assert_parse!(
      oct_digit(i),
      Err(Err::Error(error_position!(i, ErrorKind::OctDigit)))
    );

    assert!(::character::is_oct_digit(b'0'));
    assert!(::character::is_oct_digit(b'7'));
    assert!(!::character::is_oct_digit(b'8'));
    assert!(!::character::is_oct_digit(b'9'));
    assert!(!::character::is_oct_digit(b'a'));
    assert!(!::character::is_oct_digit(b'A'));
    assert!(!::character::is_oct_digit(b'/'));
    assert!(!::character::is_oct_digit(b':'));
    assert!(!::character::is_oct_digit(b'@'));
    assert!(!::character::is_oct_digit(b'\x60'));
  }

  #[test]
  fn full_line_windows() {
    named!(
      take_full_line<(&[u8], &[u8])>,
      tuple!(not_line_ending, line_ending)
    );
    let input = b"abc\r\n";
    let output = take_full_line(input);
    assert_eq!(output, Ok((&b""[..], (&b"abc"[..], &b"\r\n"[..]))));
  }

  #[test]
  fn full_line_unix() {
    named!(
      take_full_line<(&[u8], &[u8])>,
      tuple!(not_line_ending, line_ending)
    );
    let input = b"abc\n";
    let output = take_full_line(input);
    assert_eq!(output, Ok((&b""[..], (&b"abc"[..], &b"\n"[..]))));
  }

  #[test]
  fn check_windows_lineending() {
    let input = b"\r\n";
    let output = line_ending(&input[..]);
    assert_parse!(output, Ok((&b""[..], &b"\r\n"[..])));
  }

  #[test]
  fn check_unix_lineending() {
    let input = b"\n";
    let output = line_ending(&input[..]);
    assert_parse!(output, Ok((&b""[..], &b"\n"[..])));
  }

  #[test]
  fn cr_lf() {
    assert_parse!(crlf(&b"\r\na"[..]), Ok((&b"a"[..], &b"\r\n"[..])));
    assert_parse!(crlf(&b"\r"[..]), Err(Err::Error(error_position!(&b"\r"[..], ErrorKind::CrLf))));
    assert_parse!(
      crlf(&b"\ra"[..]),
      Err(Err::Error(error_position!(&b"\ra"[..], ErrorKind::CrLf)))
    );

    assert_parse!(crlf("\r\na"), Ok(("a", "\r\n")));
    assert_parse!(crlf("\r"), Err(Err::Error(error_position!(&"\r"[..], ErrorKind::CrLf))));
    assert_parse!(
      crlf("\ra"),
      Err(Err::Error(error_position!("\ra", ErrorKind::CrLf)))
    );
  }

  #[test]
  fn end_of_line() {
    assert_parse!(eol(&b"\na"[..]), Ok((&b"a"[..], &b"\n"[..])));
    assert_parse!(eol(&b"\r\na"[..]), Ok((&b"a"[..], &b"\r\n"[..])));
    assert_parse!(eol(&b"\r"[..]), Err(Err::Error(error_position!(&b"\r"[..], ErrorKind::CrLf))));
    assert_parse!(
      eol(&b"\ra"[..]),
      Err(Err::Error(error_position!(&b"\ra"[..], ErrorKind::CrLf)))
    );

    assert_parse!(eol("\na"), Ok(("a", "\n")));
    assert_parse!(eol("\r\na"), Ok(("a", "\r\n")));
    assert_parse!(eol("\r"), Err(Err::Error(error_position!(&"\r"[..], ErrorKind::CrLf))));
    assert_parse!(
      eol("\ra"),
      Err(Err::Error(error_position!("\ra", ErrorKind::CrLf)))
    );
  }
}
