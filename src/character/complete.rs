//! Character specific parsers and combinators, complete input version.
//!
//! Functions recognizing specific characters.

use crate::branch::alt;
use crate::combinator::opt;
use crate::error::ParseContext;
use crate::error::ParserKind;
use crate::internal::{Outcome, ParseResult};
use crate::lib::std::ops::{Range, RangeFrom, RangeTo};
use crate::traits::{
  AsChar, FindToken, InputIter, InputLength, InputTake, InputTakeAtPosition, Slice,
};
use crate::traits::{Compare, CompareResult};

/// Recognizes one character.
///
/// *Complete version*: Will return an error if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{ParserKind, Context}, ParseResult};
/// # use nom::character::complete::char;
/// fn parser(i: &str) -> ParseResult<&str, char> {
///     char('a')(i)
/// }
/// assert_eq!(parser("abc"), Ok(("bc", 'a')));
/// assert_eq!(parser(" abc"), Err(Outcome::Failure(Context::new(" abc", ParserKind::Char))));
/// assert_eq!(parser("bc"), Err(Outcome::Failure(Context::new("bc", ParserKind::Char))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::Char))));
/// ```
pub fn char<I, Context: ParseContext<I>>(c: char) -> impl Fn(I) -> ParseResult<I, char, Context>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar,
{
  move |i: I| match (i).iter_elements().next().map(|t| {
    let b = t.as_char() == c;
    (&c, b)
  }) {
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
    _ => Err(Outcome::Failure(Context::from_char(i, c))),
  }
}

/// Recognizes one character and checks that it satisfies a predicate
///
/// *Complete version*: Will return an error if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{ParserKind, Context}, Needed, ParseResult};
/// # use nom::character::complete::satisfy;
/// fn parser(i: &str) -> ParseResult<&str, char> {
///     satisfy(|c| c == 'a' || c == 'b')(i)
/// }
/// assert_eq!(parser("abc"), Ok(("bc", 'a')));
/// assert_eq!(parser("cd"), Err(Outcome::Failure(Context::new("cd", ParserKind::Satisfy))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::Satisfy))));
/// ```
pub fn satisfy<F, I, Context: ParseContext<I>>(
  cond: F,
) -> impl Fn(I) -> ParseResult<I, char, Context>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar,
  F: Fn(char) -> bool,
{
  move |i: I| match (i).iter_elements().next().map(|t| {
    let c = t.as_char();
    let b = cond(c);
    (c, b)
  }) {
    Some((c, true)) => Ok((i.slice(c.len()..), c)),
    _ => Err(Outcome::Failure(Context::from_parser_kind(
      i,
      ParserKind::Satisfy,
    ))),
  }
}

/// Recognizes one of the provided characters.
///
/// *Complete version*: Will return an error if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{Outcome, error::ParserKind};
/// # use nom::character::complete::one_of;
/// assert_eq!(one_of::<_, _, (&str, ParserKind)>("abc")("b"), Ok(("", 'b')));
/// assert_eq!(one_of::<_, _, (&str, ParserKind)>("a")("bc"), Err(Outcome::Failure(("bc", ParserKind::OneOf))));
/// assert_eq!(one_of::<_, _, (&str, ParserKind)>("a")(""), Err(Outcome::Failure(("", ParserKind::OneOf))));
/// ```
pub fn one_of<I, T, Context: ParseContext<I>>(
  list: T,
) -> impl Fn(I) -> ParseResult<I, char, Context>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar + Copy,
  T: FindToken<<I as InputIter>::Item>,
{
  move |i: I| match (i).iter_elements().next().map(|c| (c, list.find_token(c))) {
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
    _ => Err(Outcome::Failure(Context::from_parser_kind(
      i,
      ParserKind::OneOf,
    ))),
  }
}

/// Recognizes a character that is not in the provided characters.
///
/// *Complete version*: Will return an error if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{Outcome, error::ParserKind};
/// # use nom::character::complete::none_of;
/// assert_eq!(none_of::<_, _, (&str, ParserKind)>("abc")("z"), Ok(("", 'z')));
/// assert_eq!(none_of::<_, _, (&str, ParserKind)>("ab")("a"), Err(Outcome::Failure(("a", ParserKind::NoneOf))));
/// assert_eq!(none_of::<_, _, (&str, ParserKind)>("a")(""), Err(Outcome::Failure(("", ParserKind::NoneOf))));
/// ```
pub fn none_of<I, T, Context: ParseContext<I>>(
  list: T,
) -> impl Fn(I) -> ParseResult<I, char, Context>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar + Copy,
  T: FindToken<<I as InputIter>::Item>,
{
  move |i: I| match (i).iter_elements().next().map(|c| (c, !list.find_token(c))) {
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
    _ => Err(Outcome::Failure(Context::from_parser_kind(
      i,
      ParserKind::NoneOf,
    ))),
  }
}

/// Recognizes the string "\r\n".
///
/// *Complete version*: Will return an error if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult};
/// # use nom::character::complete::crlf;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     crlf(input)
/// }
///
/// assert_eq!(parser("\r\nc"), Ok(("c", "\r\n")));
/// assert_eq!(parser("ab\r\nc"), Err(Outcome::Failure(Context::new("ab\r\nc", ParserKind::CrLf))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::CrLf))));
/// ```
pub fn crlf<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>>,
  T: InputIter,
  T: Compare<&'static str>,
{
  match input.compare("\r\n") {
    //FIXME: is this the right index?
    CompareResult::Ok => Ok((input.slice(2..), input.slice(0..2))),
    _ => {
      let e: ParserKind = ParserKind::CrLf;
      Err(Outcome::Failure(E::from_parser_kind(input, e)))
    }
  }
}

//FIXME: there's still an incomplete
/// Recognizes a string of any char except '\r\n' or '\n'.
///
/// *Complete version*: Will return an error if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::not_line_ending;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     not_line_ending(input)
/// }
///
/// assert_eq!(parser("ab\r\nc"), Ok(("\r\nc", "ab")));
/// assert_eq!(parser("ab\nc"), Ok(("\nc", "ab")));
/// assert_eq!(parser("abc"), Ok(("", "abc")));
/// assert_eq!(parser(""), Ok(("", "")));
/// assert_eq!(parser("a\rb\nc"), Err(Outcome::Failure(Context { input: "a\rb\nc", code: ParserKind::Tag })));
/// assert_eq!(parser("a\rbc"), Err(Outcome::Failure(Context { input: "a\rbc", code: ParserKind::Tag })));
/// ```
pub fn not_line_ending<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength,
  T: Compare<&'static str>,
  <T as InputIter>::Item: AsChar,
  <T as InputIter>::Item: AsChar,
{
  match input.position(|item| {
    let c = item.as_char();
    c == '\r' || c == '\n'
  }) {
    None => Ok((input.slice(input.input_len()..), input)),
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
            let e: ParserKind = ParserKind::Tag;
            Err(Outcome::Failure(E::from_parser_kind(input, e)))
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
/// *Complete version*: Will return an error if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::line_ending;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     line_ending(input)
/// }
///
/// assert_eq!(parser("\r\nc"), Ok(("c", "\r\n")));
/// assert_eq!(parser("ab\r\nc"), Err(Outcome::Failure(Context::new("ab\r\nc", ParserKind::CrLf))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::CrLf))));
/// ```
pub fn line_ending<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength,
  T: Compare<&'static str>,
{
  match input.compare("\n") {
    CompareResult::Ok => Ok((input.slice(1..), input.slice(0..1))),
    CompareResult::Incomplete => Err(Outcome::Failure(E::from_parser_kind(
      input,
      ParserKind::CrLf,
    ))),
    CompareResult::Error => {
      match input.compare("\r\n") {
        //FIXME: is this the right index?
        CompareResult::Ok => Ok((input.slice(2..), input.slice(0..2))),
        _ => Err(Outcome::Failure(E::from_parser_kind(
          input,
          ParserKind::CrLf,
        ))),
      }
    }
  }
}

/// Matches a newline character '\n'.
///
/// *Complete version*: Will return an error if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::newline;
/// fn parser(input: &str) -> ParseResult<&str, char> {
///     newline(input)
/// }
///
/// assert_eq!(parser("\nc"), Ok(("c", '\n')));
/// assert_eq!(parser("\r\nc"), Err(Outcome::Failure(Context::new("\r\nc", ParserKind::Char))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::Char))));
/// ```
pub fn newline<I, Context: ParseContext<I>>(input: I) -> ParseResult<I, char, Context>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar,
{
  char('\n')(input)
}

/// Matches a tab character '\t'.
///
/// *Complete version*: Will return an error if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::tab;
/// fn parser(input: &str) -> ParseResult<&str, char> {
///     tab(input)
/// }
///
/// assert_eq!(parser("\tc"), Ok(("c", '\t')));
/// assert_eq!(parser("\r\nc"), Err(Outcome::Failure(Context::new("\r\nc", ParserKind::Char))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::Char))));
/// ```
pub fn tab<I, Context: ParseContext<I>>(input: I) -> ParseResult<I, char, Context>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar,
{
  char('\t')(input)
}

/// Matches one byte as a character. Note that the input type will
/// accept a `str`, but not a `&[u8]`, unlike many other nom parsers.
///
/// *Complete version*: Will return an error if there's not enough input data.
/// # Example
///
/// ```
/// # use nom::{character::complete::anychar, Outcome, error::{Context, ParserKind}, ParseResult};
/// fn parser(input: &str) -> ParseResult<&str, char> {
///     anychar(input)
/// }
///
/// assert_eq!(parser("abc"), Ok(("bc",'a')));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::Eof))));
/// ```
pub fn anychar<T, E: ParseContext<T>>(input: T) -> ParseResult<T, char, E>
where
  T: InputIter + InputLength + Slice<RangeFrom<usize>>,
  <T as InputIter>::Item: AsChar,
{
  let mut it = input.iter_indices();
  match it.next() {
    None => Err(Outcome::Failure(E::from_parser_kind(
      input,
      ParserKind::Eof,
    ))),
    Some((_, c)) => match it.next() {
      None => Ok((input.slice(input.input_len()..), c.as_char())),
      Some((idx, _)) => Ok((input.slice(idx..), c.as_char())),
    },
  }
}

/// Recognizes zero or more lowercase and uppercase ASCII alphabetic characters: a-z, A-Z
///
/// *Complete version*: Will return the whole input if no terminating token is found (a non
/// alphabetic character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::ParserKind, ParseResult, Needed};
/// # use nom::character::complete::alpha0;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     alpha0(input)
/// }
///
/// assert_eq!(parser("ab1c"), Ok(("1c", "ab")));
/// assert_eq!(parser("1c"), Ok(("1c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// ```
pub fn alpha0<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position_complete(|item| !item.is_alpha())
}

/// Recognizes one or more lowercase and uppercase ASCII alphabetic characters: a-z, A-Z
///
/// *Complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found  (a non alphabetic character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::alpha1;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     alpha1(input)
/// }
///
/// assert_eq!(parser("aB1c"), Ok(("1c", "aB")));
/// assert_eq!(parser("1c"), Err(Outcome::Failure(Context::new("1c", ParserKind::Alpha))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::Alpha))));
/// ```
pub fn alpha1<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1_complete(|item| !item.is_alpha(), ParserKind::Alpha)
}

/// Recognizes zero or more ASCII numerical characters: 0-9
///
/// *Complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non digit character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::ParserKind, ParseResult, Needed};
/// # use nom::character::complete::digit0;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     digit0(input)
/// }
///
/// assert_eq!(parser("21c"), Ok(("c", "21")));
/// assert_eq!(parser("21"), Ok(("", "21")));
/// assert_eq!(parser("a21c"), Ok(("a21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// ```
pub fn digit0<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position_complete(|item| !item.is_dec_digit())
}

/// Recognizes one or more ASCII numerical characters: 0-9
///
/// *Complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non digit character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::digit1;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     digit1(input)
/// }
///
/// assert_eq!(parser("21c"), Ok(("c", "21")));
/// assert_eq!(parser("c1"), Err(Outcome::Failure(Context::new("c1", ParserKind::Digit))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::Digit))));
/// ```
pub fn digit1<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1_complete(|item| !item.is_dec_digit(), ParserKind::Digit)
}

/// Recognizes zero or more ASCII hexadecimal numerical characters: 0-9, A-F, a-f
///
/// *Complete version*: Will return the whole input if no terminating token is found (a non hexadecimal digit character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::ParserKind, ParseResult, Needed};
/// # use nom::character::complete::hex_digit0;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     hex_digit0(input)
/// }
///
/// assert_eq!(parser("21cZ"), Ok(("Z", "21c")));
/// assert_eq!(parser("Z21c"), Ok(("Z21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// ```
pub fn hex_digit0<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position_complete(|item| !item.is_hex_digit())
}
/// Recognizes one or more ASCII hexadecimal numerical characters: 0-9, A-F, a-f
///
/// *Complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non hexadecimal digit character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::hex_digit1;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     hex_digit1(input)
/// }
///
/// assert_eq!(parser("21cZ"), Ok(("Z", "21c")));
/// assert_eq!(parser("H2"), Err(Outcome::Failure(Context::new("H2", ParserKind::HexDigit))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::HexDigit))));
/// ```
pub fn hex_digit1<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1_complete(|item| !item.is_hex_digit(), ParserKind::HexDigit)
}

/// Recognizes zero or more octal characters: 0-7
///
/// *Complete version*: Will return the whole input if no terminating token is found (a non octal
/// digit character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::ParserKind, ParseResult, Needed};
/// # use nom::character::complete::oct_digit0;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     oct_digit0(input)
/// }
///
/// assert_eq!(parser("21cZ"), Ok(("cZ", "21")));
/// assert_eq!(parser("Z21c"), Ok(("Z21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// ```
pub fn oct_digit0<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position_complete(|item| !item.is_oct_digit())
}

/// Recognizes one or more octal characters: 0-7
///
/// *Complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non octal digit character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::oct_digit1;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     oct_digit1(input)
/// }
///
/// assert_eq!(parser("21cZ"), Ok(("cZ", "21")));
/// assert_eq!(parser("H2"), Err(Outcome::Failure(Context::new("H2", ParserKind::OctDigit))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::OctDigit))));
/// ```
pub fn oct_digit1<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1_complete(|item| !item.is_oct_digit(), ParserKind::OctDigit)
}

/// Recognizes zero or more ASCII numerical and alphabetic characters: 0-9, a-z, A-Z
///
/// *Complete version*: Will return the whole input if no terminating token is found (a non
/// alphanumerical character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::ParserKind, ParseResult, Needed};
/// # use nom::character::complete::alphanumeric0;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     alphanumeric0(input)
/// }
///
/// assert_eq!(parser("21cZ%1"), Ok(("%1", "21cZ")));
/// assert_eq!(parser("&Z21c"), Ok(("&Z21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// ```
pub fn alphanumeric0<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position_complete(|item| !item.is_alphanum())
}

/// Recognizes one or more ASCII numerical and alphabetic characters: 0-9, a-z, A-Z
///
/// *Complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non alphanumerical character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::alphanumeric1;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     alphanumeric1(input)
/// }
///
/// assert_eq!(parser("21cZ%1"), Ok(("%1", "21cZ")));
/// assert_eq!(parser("&H2"), Err(Outcome::Failure(Context::new("&H2", ParserKind::AlphaNumeric))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::AlphaNumeric))));
/// ```
pub fn alphanumeric1<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1_complete(|item| !item.is_alphanum(), ParserKind::AlphaNumeric)
}

/// Recognizes zero or more spaces and tabs.
///
/// *Complete version*: Will return the whole input if no terminating token is found (a non space
/// character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::ParserKind, ParseResult, Needed};
/// # use nom::character::complete::space0;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     space0(input)
/// }
///
/// assert_eq!(parser(" \t21c"), Ok(("21c", " \t")));
/// assert_eq!(parser("Z21c"), Ok(("Z21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// ```
pub fn space0<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position_complete(|item| {
    let c = item.as_char();
    !(c == ' ' || c == '\t')
  })
}

/// Recognizes one or more spaces and tabs.
///
/// *Complete version*: Will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non space character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::space1;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     space1(input)
/// }
///
/// assert_eq!(parser(" \t21c"), Ok(("21c", " \t")));
/// assert_eq!(parser("H2"), Err(Outcome::Failure(Context::new("H2", ParserKind::Space))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::Space))));
/// ```
pub fn space1<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position1_complete(
    |item| {
      let c = item.as_char();
      !(c == ' ' || c == '\t')
    },
    ParserKind::Space,
  )
}

/// Recognizes zero or more spaces, tabs, carriage returns and line feeds.
///
/// *Complete version*: will return the whole input if no terminating token is found (a non space
/// character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::ParserKind, ParseResult, Needed};
/// # use nom::character::complete::multispace0;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     multispace0(input)
/// }
///
/// assert_eq!(parser(" \t\n\r21c"), Ok(("21c", " \t\n\r")));
/// assert_eq!(parser("Z21c"), Ok(("Z21c", "")));
/// assert_eq!(parser(""), Ok(("", "")));
/// ```
pub fn multispace0<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position_complete(|item| {
    let c = item.as_char();
    !(c == ' ' || c == '\t' || c == '\r' || c == '\n')
  })
}

/// Recognizes one or more spaces, tabs, carriage returns and line feeds.
///
/// *Complete version*: will return an error if there's not enough input data,
/// or the whole input if no terminating token is found (a non space character).
/// # Example
///
/// ```
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult, Needed};
/// # use nom::character::complete::multispace1;
/// fn parser(input: &str) -> ParseResult<&str, &str> {
///     multispace1(input)
/// }
///
/// assert_eq!(parser(" \t\n\r21c"), Ok(("21c", " \t\n\r")));
/// assert_eq!(parser("H2"), Err(Outcome::Failure(Context::new("H2", ParserKind::MultiSpace))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::MultiSpace))));
/// ```
pub fn multispace1<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position1_complete(
    |item| {
      let c = item.as_char();
      !(c == ' ' || c == '\t' || c == '\r' || c == '\n')
    },
    ParserKind::MultiSpace,
  )
}

pub(crate) fn sign<T, E: ParseContext<T>>(input: T) -> ParseResult<T, bool, E>
where
  T: Clone + InputTake,
  T: for<'a> Compare<&'a [u8]>,
{
  use crate::bytes::complete::tag;
  use crate::combinator::value;

  let (i, opt_sign) = opt(alt((
    value(false, tag(&b"-"[..])),
    value(true, tag(&b"+"[..])),
  )))(input)?;
  let sign = opt_sign.unwrap_or(true);

  Ok((i, sign))
}

#[doc(hidden)]
macro_rules! ints {
    ($($t:tt)+) => {
        $(
        /// will parse a number in text form to a number
        ///
        /// *Complete version*: can parse until the end of input.
        pub fn $t<T, E: ParseContext<T>>(input: T) -> ParseResult<T, $t, E>
            where
            T: InputIter + Slice<RangeFrom<usize>> + InputLength + InputTake + Clone,
            <T as InputIter>::Item: AsChar,
            T: for <'a> Compare<&'a[u8]>,
            {
                let (i, sign) = sign(input.clone())?;

                if i.input_len() == 0 {
                    return Err(Outcome::Failure(E::from_parser_kind(input, ParserKind::Digit)));
                }

                let mut value: $t = 0;
                if sign {
                    for (pos, c) in i.iter_indices() {
                        match c.as_char().to_digit(10) {
                            None => {
                                if pos == 0 {
                                    return Err(Outcome::Failure(E::from_parser_kind(input, ParserKind::Digit)));
                                } else {
                                    return Ok((i.slice(pos..), value));
                                }
                            },
                            Some(d) => match value.checked_mul(10).and_then(|v| v.checked_add(d as $t)) {
                                None => return Err(Outcome::Failure(E::from_parser_kind(input, ParserKind::Digit))),
                                Some(v) => value = v,
                            }
                        }
                    }
                } else {
                    for (pos, c) in i.iter_indices() {
                        match c.as_char().to_digit(10) {
                            None => {
                                if pos == 0 {
                                    return Err(Outcome::Failure(E::from_parser_kind(input, ParserKind::Digit)));
                                } else {
                                    return Ok((i.slice(pos..), value));
                                }
                            },
                            Some(d) => match value.checked_mul(10).and_then(|v| v.checked_sub(d as $t)) {
                                None => return Err(Outcome::Failure(E::from_parser_kind(input, ParserKind::Digit))),
                                Some(v) => value = v,
                            }
                        }
                    }
                }

                Ok((i.slice(i.input_len()..), value))
            }
        )+
    }
}

ints! { i8 i16 i32 i64 i128 }

#[doc(hidden)]
macro_rules! uints {
    ($($t:tt)+) => {
        $(
        /// will parse a number in text form to a number
        ///
        /// *Complete version*: can parse until the end of input.
        pub fn $t<T, E: ParseContext<T>>(input: T) -> ParseResult<T, $t, E>
            where
            T: InputIter + Slice<RangeFrom<usize>> + InputLength,
            <T as InputIter>::Item: AsChar,
            {
                let i = input;

                if i.input_len() == 0 {
                    return Err(Outcome::Failure(E::from_parser_kind(i, ParserKind::Digit)));
                }

                let mut value: $t = 0;
                for (pos, c) in i.iter_indices() {
                    match c.as_char().to_digit(10) {
                        None => {
                            if pos == 0 {
                                return Err(Outcome::Failure(E::from_parser_kind(i, ParserKind::Digit)));
                            } else {
                                return Ok((i.slice(pos..), value));
                            }
                        },
                        Some(d) => match value.checked_mul(10).and_then(|v| v.checked_add(d as $t)) {
                            None => return Err(Outcome::Failure(E::from_parser_kind(i, ParserKind::Digit))),
                            Some(v) => value = v,
                        }
                    }
                }

                Ok((i.slice(i.input_len()..), value))
            }
        )+
    }
}

uints! { u8 u16 u32 u64 u128 }

#[cfg(test)]
mod tests {
  use super::*;
  use crate::internal::Outcome;
  use crate::traits::ParseTo;
  use proptest::prelude::*;

  macro_rules! assert_parse(
    ($left: expr, $right: expr) => {
      let res: $crate::ParseResult<_, _, (_, ParserKind)> = $left;
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
    //assert_eq!(alpha1::<_, (_, ParserKind)>(a), Err(Outcome::Incomplete(Needed::Size(1))));
    assert_parse!(alpha1(a), Ok((empty, a)));
    assert_eq!(alpha1(b), Err(Outcome::Failure((b, ParserKind::Alpha))));
    assert_eq!(alpha1::<_, (_, ParserKind)>(c), Ok((&c[1..], &b"a"[..])));
    assert_eq!(
      alpha1::<_, (_, ParserKind)>(d),
      Ok(("é12".as_bytes(), &b"az"[..]))
    );
    assert_eq!(digit1(a), Err(Outcome::Failure((a, ParserKind::Digit))));
    assert_eq!(digit1::<_, (_, ParserKind)>(b), Ok((empty, b)));
    assert_eq!(digit1(c), Err(Outcome::Failure((c, ParserKind::Digit))));
    assert_eq!(digit1(d), Err(Outcome::Failure((d, ParserKind::Digit))));
    assert_eq!(hex_digit1::<_, (_, ParserKind)>(a), Ok((empty, a)));
    assert_eq!(hex_digit1::<_, (_, ParserKind)>(b), Ok((empty, b)));
    assert_eq!(hex_digit1::<_, (_, ParserKind)>(c), Ok((empty, c)));
    assert_eq!(
      hex_digit1::<_, (_, ParserKind)>(d),
      Ok(("zé12".as_bytes(), &b"a"[..]))
    );
    assert_eq!(
      hex_digit1(e),
      Err(Outcome::Failure((e, ParserKind::HexDigit)))
    );
    assert_eq!(
      oct_digit1(a),
      Err(Outcome::Failure((a, ParserKind::OctDigit)))
    );
    assert_eq!(oct_digit1::<_, (_, ParserKind)>(b), Ok((empty, b)));
    assert_eq!(
      oct_digit1(c),
      Err(Outcome::Failure((c, ParserKind::OctDigit)))
    );
    assert_eq!(
      oct_digit1(d),
      Err(Outcome::Failure((d, ParserKind::OctDigit)))
    );
    assert_eq!(alphanumeric1::<_, (_, ParserKind)>(a), Ok((empty, a)));
    //assert_eq!(fix_error!(b,(), alphanumeric), Ok((empty, b)));
    assert_eq!(alphanumeric1::<_, (_, ParserKind)>(c), Ok((empty, c)));
    assert_eq!(
      alphanumeric1::<_, (_, ParserKind)>(d),
      Ok(("é12".as_bytes(), &b"az"[..]))
    );
    assert_eq!(space1::<_, (_, ParserKind)>(e), Ok((empty, e)));
    assert_eq!(space1::<_, (_, ParserKind)>(f), Ok((&b";"[..], &b" "[..])));
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
    assert_eq!(alpha1::<_, (_, ParserKind)>(a), Ok((empty, a)));
    assert_eq!(alpha1(b), Err(Outcome::Failure((b, ParserKind::Alpha))));
    assert_eq!(alpha1::<_, (_, ParserKind)>(c), Ok((&c[1..], &"a"[..])));
    assert_eq!(alpha1::<_, (_, ParserKind)>(d), Ok(("é12", &"az"[..])));
    assert_eq!(digit1(a), Err(Outcome::Failure((a, ParserKind::Digit))));
    assert_eq!(digit1::<_, (_, ParserKind)>(b), Ok((empty, b)));
    assert_eq!(digit1(c), Err(Outcome::Failure((c, ParserKind::Digit))));
    assert_eq!(digit1(d), Err(Outcome::Failure((d, ParserKind::Digit))));
    assert_eq!(hex_digit1::<_, (_, ParserKind)>(a), Ok((empty, a)));
    assert_eq!(hex_digit1::<_, (_, ParserKind)>(b), Ok((empty, b)));
    assert_eq!(hex_digit1::<_, (_, ParserKind)>(c), Ok((empty, c)));
    assert_eq!(hex_digit1::<_, (_, ParserKind)>(d), Ok(("zé12", &"a"[..])));
    assert_eq!(
      hex_digit1(e),
      Err(Outcome::Failure((e, ParserKind::HexDigit)))
    );
    assert_eq!(
      oct_digit1(a),
      Err(Outcome::Failure((a, ParserKind::OctDigit)))
    );
    assert_eq!(oct_digit1::<_, (_, ParserKind)>(b), Ok((empty, b)));
    assert_eq!(
      oct_digit1(c),
      Err(Outcome::Failure((c, ParserKind::OctDigit)))
    );
    assert_eq!(
      oct_digit1(d),
      Err(Outcome::Failure((d, ParserKind::OctDigit)))
    );
    assert_eq!(alphanumeric1::<_, (_, ParserKind)>(a), Ok((empty, a)));
    //assert_eq!(fix_error!(b,(), alphanumeric), Ok((empty, b)));
    assert_eq!(alphanumeric1::<_, (_, ParserKind)>(c), Ok((empty, c)));
    assert_eq!(alphanumeric1::<_, (_, ParserKind)>(d), Ok(("é12", "az")));
    assert_eq!(space1::<_, (_, ParserKind)>(e), Ok((empty, e)));
  }

  use crate::traits::Offset;
  #[test]
  fn offset() {
    let a = &b"abcd;"[..];
    let b = &b"1234;"[..];
    let c = &b"a123;"[..];
    let d = &b" \t;"[..];
    let e = &b" \t\r\n;"[..];
    let f = &b"123abcDEF;"[..];

    match alpha1::<_, (_, ParserKind)>(a) {
      Ok((i, _)) => {
        assert_eq!(a.offset(i) + i.len(), a.len());
      }
      _ => panic!("wrong return type in offset test for alpha"),
    }
    match digit1::<_, (_, ParserKind)>(b) {
      Ok((i, _)) => {
        assert_eq!(b.offset(i) + i.len(), b.len());
      }
      _ => panic!("wrong return type in offset test for digit"),
    }
    match alphanumeric1::<_, (_, ParserKind)>(c) {
      Ok((i, _)) => {
        assert_eq!(c.offset(i) + i.len(), c.len());
      }
      _ => panic!("wrong return type in offset test for alphanumeric"),
    }
    match space1::<_, (_, ParserKind)>(d) {
      Ok((i, _)) => {
        assert_eq!(d.offset(i) + i.len(), d.len());
      }
      _ => panic!("wrong return type in offset test for space"),
    }
    match multispace1::<_, (_, ParserKind)>(e) {
      Ok((i, _)) => {
        assert_eq!(e.offset(i) + i.len(), e.len());
      }
      _ => panic!("wrong return type in offset test for multispace"),
    }
    match hex_digit1::<_, (_, ParserKind)>(f) {
      Ok((i, _)) => {
        assert_eq!(f.offset(i) + i.len(), f.len());
      }
      _ => panic!("wrong return type in offset test for hex_digit"),
    }
    match oct_digit1::<_, (_, ParserKind)>(f) {
      Ok((i, _)) => {
        assert_eq!(f.offset(i) + i.len(), f.len());
      }
      _ => panic!("wrong return type in offset test for oct_digit"),
    }
  }

  #[test]
  fn is_not_line_ending_bytes() {
    let a: &[u8] = b"ab12cd\nefgh";
    assert_eq!(
      not_line_ending::<_, (_, ParserKind)>(a),
      Ok((&b"\nefgh"[..], &b"ab12cd"[..]))
    );

    let b: &[u8] = b"ab12cd\nefgh\nijkl";
    assert_eq!(
      not_line_ending::<_, (_, ParserKind)>(b),
      Ok((&b"\nefgh\nijkl"[..], &b"ab12cd"[..]))
    );

    let c: &[u8] = b"ab12cd\r\nefgh\nijkl";
    assert_eq!(
      not_line_ending::<_, (_, ParserKind)>(c),
      Ok((&b"\r\nefgh\nijkl"[..], &b"ab12cd"[..]))
    );

    let d: &[u8] = b"ab12cd";
    assert_eq!(
      not_line_ending::<_, (_, ParserKind)>(d),
      Ok((&[][..], &d[..]))
    );
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
      Err(Outcome::Failure((f, ParserKind::Tag)))
    );

    let g2: &str = "ab12cd";
    assert_eq!(not_line_ending::<_, (_, ParserKind)>(g2), Ok(("", g2)));
  }

  #[test]
  fn hex_digit_test() {
    let i = &b"0123456789abcdefABCDEF;"[..];
    assert_parse!(hex_digit1(i), Ok((&b";"[..], &i[..i.len() - 1])));

    let i = &b"g"[..];
    assert_parse!(
      hex_digit1(i),
      Err(Outcome::Failure(error_position!(i, ParserKind::HexDigit)))
    );

    let i = &b"G"[..];
    assert_parse!(
      hex_digit1(i),
      Err(Outcome::Failure(error_position!(i, ParserKind::HexDigit)))
    );

    assert!(crate::character::is_hex_digit(b'0'));
    assert!(crate::character::is_hex_digit(b'9'));
    assert!(crate::character::is_hex_digit(b'a'));
    assert!(crate::character::is_hex_digit(b'f'));
    assert!(crate::character::is_hex_digit(b'A'));
    assert!(crate::character::is_hex_digit(b'F'));
    assert!(!crate::character::is_hex_digit(b'g'));
    assert!(!crate::character::is_hex_digit(b'G'));
    assert!(!crate::character::is_hex_digit(b'/'));
    assert!(!crate::character::is_hex_digit(b':'));
    assert!(!crate::character::is_hex_digit(b'@'));
    assert!(!crate::character::is_hex_digit(b'\x60'));
  }

  #[test]
  fn oct_digit_test() {
    let i = &b"01234567;"[..];
    assert_parse!(oct_digit1(i), Ok((&b";"[..], &i[..i.len() - 1])));

    let i = &b"8"[..];
    assert_parse!(
      oct_digit1(i),
      Err(Outcome::Failure(error_position!(i, ParserKind::OctDigit)))
    );

    assert!(crate::character::is_oct_digit(b'0'));
    assert!(crate::character::is_oct_digit(b'7'));
    assert!(!crate::character::is_oct_digit(b'8'));
    assert!(!crate::character::is_oct_digit(b'9'));
    assert!(!crate::character::is_oct_digit(b'a'));
    assert!(!crate::character::is_oct_digit(b'A'));
    assert!(!crate::character::is_oct_digit(b'/'));
    assert!(!crate::character::is_oct_digit(b':'));
    assert!(!crate::character::is_oct_digit(b'@'));
    assert!(!crate::character::is_oct_digit(b'\x60'));
  }

  #[test]
  fn full_line_windows() {
    use crate::sequence::pair;
    fn take_full_line(i: &[u8]) -> ParseResult<&[u8], (&[u8], &[u8])> {
      pair(not_line_ending, line_ending)(i)
    }
    let input = b"abc\r\n";
    let output = take_full_line(input);
    assert_eq!(output, Ok((&b""[..], (&b"abc"[..], &b"\r\n"[..]))));
  }

  #[test]
  fn full_line_unix() {
    use crate::sequence::pair;
    fn take_full_line(i: &[u8]) -> ParseResult<&[u8], (&[u8], &[u8])> {
      pair(not_line_ending, line_ending)(i)
    }
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
    assert_parse!(
      crlf(&b"\r"[..]),
      Err(Outcome::Failure(error_position!(
        &b"\r"[..],
        ParserKind::CrLf
      )))
    );
    assert_parse!(
      crlf(&b"\ra"[..]),
      Err(Outcome::Failure(error_position!(
        &b"\ra"[..],
        ParserKind::CrLf
      )))
    );

    assert_parse!(crlf("\r\na"), Ok(("a", "\r\n")));
    assert_parse!(
      crlf("\r"),
      Err(Outcome::Failure(error_position!(
        &"\r"[..],
        ParserKind::CrLf
      )))
    );
    assert_parse!(
      crlf("\ra"),
      Err(Outcome::Failure(error_position!("\ra", ParserKind::CrLf)))
    );
  }

  #[test]
  fn end_of_line() {
    assert_parse!(line_ending(&b"\na"[..]), Ok((&b"a"[..], &b"\n"[..])));
    assert_parse!(line_ending(&b"\r\na"[..]), Ok((&b"a"[..], &b"\r\n"[..])));
    assert_parse!(
      line_ending(&b"\r"[..]),
      Err(Outcome::Failure(error_position!(
        &b"\r"[..],
        ParserKind::CrLf
      )))
    );
    assert_parse!(
      line_ending(&b"\ra"[..]),
      Err(Outcome::Failure(error_position!(
        &b"\ra"[..],
        ParserKind::CrLf
      )))
    );

    assert_parse!(line_ending("\na"), Ok(("a", "\n")));
    assert_parse!(line_ending("\r\na"), Ok(("a", "\r\n")));
    assert_parse!(
      line_ending("\r"),
      Err(Outcome::Failure(error_position!(
        &"\r"[..],
        ParserKind::CrLf
      )))
    );
    assert_parse!(
      line_ending("\ra"),
      Err(Outcome::Failure(error_position!("\ra", ParserKind::CrLf)))
    );
  }

  fn digit_to_i16(input: &str) -> ParseResult<&str, i16> {
    let i = input;
    let (i, opt_sign) = opt(alt((char('+'), char('-'))))(i)?;
    let sign = match opt_sign {
      Some('+') => true,
      Some('-') => false,
      _ => true,
    };

    let (i, s) = match digit1::<_, crate::error::Context<_>>(i) {
      Ok((i, s)) => (i, s),
      Err(_) => {
        return Err(Outcome::Failure(crate::error::Context::from_parser_kind(
          input,
          ParserKind::Digit,
        )))
      }
    };

    match s.parse_to() {
      Some(n) => {
        if sign {
          Ok((i, n))
        } else {
          Ok((i, -n))
        }
      }
      None => Err(Outcome::Failure(crate::error::Context::from_parser_kind(
        i,
        ParserKind::Digit,
      ))),
    }
  }

  fn digit_to_u32(i: &str) -> ParseResult<&str, u32> {
    let (i, s) = digit1(i)?;
    match s.parse_to() {
      Some(n) => Ok((i, n)),
      None => Err(Outcome::Failure(crate::error::Context::from_parser_kind(
        i,
        ParserKind::Digit,
      ))),
    }
  }

  proptest! {
    #[test]
    fn ints(s in "\\PC*") {
        let res1 = digit_to_i16(&s);
        let res2 = i16(s.as_str());
        assert_eq!(res1, res2);
    }

    #[test]
    fn uints(s in "\\PC*") {
        let res1 = digit_to_u32(&s);
        let res2 = u32(s.as_str());
        assert_eq!(res1, res2);
    }
  }
}
