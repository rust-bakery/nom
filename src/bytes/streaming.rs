//! Parsers recognizing bytes streams, streaming version

use crate::error::ErrorKind;
use crate::error::ParseError;
use crate::internal::{Err, IResult, Needed, Parser};
use crate::lib::std::ops::RangeFrom;
use crate::lib::std::result::Result::*;
use crate::traits::{
  Compare, CompareResult, FindSubstring, FindToken, InputIter, InputLength, InputTake,
  InputTakeAtPosition, Slice, ToUsize,
};

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
pub fn tag<T, Input, Error: ParseError<Input>>(
  tag: T,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + InputLength + Compare<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let tag_len = tag.input_len();
    let t = tag.clone();

    let res: IResult<_, _, Error> = match i.compare(t) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      CompareResult::Incomplete => Err(Err::Incomplete(Needed::new(tag_len - i.input_len()))),
      CompareResult::Error => {
        let e: ErrorKind = ErrorKind::Tag;
        Err(Err::Error(Error::from_error_kind(i, e)))
      }
    };
    res
  }
}

/// Recognizes a case insensitive pattern.
///
/// The input data will be compared to the tag combinator's argument and will return the part of
/// the input that matches the argument with no regard to case.
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, Needed, IResult};
/// use nom::bytes::streaming::tag_no_case;
///
/// fn parser(s: &str) -> IResult<&str, &str> {
///   tag_no_case("hello")(s)
/// }
///
/// assert_eq!(parser("Hello, World!"), Ok((", World!", "Hello")));
/// assert_eq!(parser("hello, World!"), Ok((", World!", "hello")));
/// assert_eq!(parser("HeLlO, World!"), Ok((", World!", "HeLlO")));
/// assert_eq!(parser("Something"), Err(Err::Error(Error::new("Something", ErrorKind::Tag))));
/// assert_eq!(parser(""), Err(Err::Incomplete(Needed::new(5))));
/// ```
pub fn tag_no_case<T, Input, Error: ParseError<Input>>(
  tag: T,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + InputLength + Compare<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let tag_len = tag.input_len();
    let t = tag.clone();

    let res: IResult<_, _, Error> = match (i).compare_no_case(t) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      CompareResult::Incomplete => Err(Err::Incomplete(Needed::new(tag_len - i.input_len()))),
      CompareResult::Error => {
        let e: ErrorKind = ErrorKind::Tag;
        Err(Err::Error(Error::from_error_kind(i, e)))
      }
    };
    res
  }
}

/// Parse till certain characters are met.
///
/// The parser will return the longest slice till one of the characters of the combinator's argument are met.
///
/// It doesn't consume the matched character.
///
/// It will return a `Err::Incomplete(Needed::new(1))` if the pattern wasn't met.
/// # Example
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, IResult};
/// use nom::bytes::streaming::is_not;
///
/// fn not_space(s: &str) -> IResult<&str, &str> {
///   is_not(" \t\r\n")(s)
/// }
///
/// assert_eq!(not_space("Hello, World!"), Ok((" World!", "Hello,")));
/// assert_eq!(not_space("Sometimes\t"), Ok(("\t", "Sometimes")));
/// assert_eq!(not_space("Nospace"), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(not_space(""), Err(Err::Incomplete(Needed::new(1))));
/// ```
pub fn is_not<T, Input, Error: ParseError<Input>>(
  arr: T,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  T: FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::IsNot;
    i.split_at_position1(|c| arr.find_token(c), e)
  }
}

/// Returns the longest slice of the matches the pattern.
///
/// The parser will return the longest slice consisting of the characters in provided in the
/// combinator's argument.
///
/// # Streaming specific
/// *Streaming version* will return a `Err::Incomplete(Needed::new(1))` if the pattern wasn't met
/// or if the pattern reaches the end of the input.
/// # Example
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, IResult};
/// use nom::bytes::streaming::is_a;
///
/// fn hex(s: &str) -> IResult<&str, &str> {
///   is_a("1234567890ABCDEF")(s)
/// }
///
/// assert_eq!(hex("123 and voila"), Ok((" and voila", "123")));
/// assert_eq!(hex("DEADBEEF and others"), Ok((" and others", "DEADBEEF")));
/// assert_eq!(hex("BADBABEsomething"), Ok(("something", "BADBABE")));
/// assert_eq!(hex("D15EA5E"), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(hex(""), Err(Err::Incomplete(Needed::new(1))));
/// ```
pub fn is_a<T, Input, Error: ParseError<Input>>(
  arr: T,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  T: FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::IsA;
    i.split_at_position1(|c| !arr.find_token(c), e)
  }
}

/// Returns the longest input slice (if any) that matches the predicate.
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// # Streaming Specific
/// *Streaming version* will return a `Err::Incomplete(Needed::new(1))` if the pattern reaches the end of the input.
/// # Example
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, IResult};
/// use nom::bytes::streaming::take_while;
/// use nom::character::is_alphabetic;
///
/// fn alpha(s: &[u8]) -> IResult<&[u8], &[u8]> {
///   take_while(is_alphabetic)(s)
/// }
///
/// assert_eq!(alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(alpha(b"12345"), Ok((&b"12345"[..], &b""[..])));
/// assert_eq!(alpha(b"latin"), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(alpha(b""), Err(Err::Incomplete(Needed::new(1))));
/// ```
pub fn take_while<F, Input, Error: ParseError<Input>>(
  cond: F,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position(|c| !cond(c))
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
pub fn take_while1<F, Input, Error: ParseError<Input>>(
  cond: F,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::TakeWhile1;
    i.split_at_position1(|c| !cond(c), e)
  }
}

/// Returns the longest (m <= len <= n) input slice  that matches the predicate.
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// It will return an `Err::Error((_, ErrorKind::TakeWhileMN))` if the pattern wasn't met.
/// # Streaming Specific
/// *Streaming version* will return a `Err::Incomplete(Needed::new(1))`  if the pattern reaches the end of the input or is too short.
///
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, Needed, IResult};
/// use nom::bytes::streaming::take_while_m_n;
/// use nom::character::is_alphabetic;
///
/// fn short_alpha(s: &[u8]) -> IResult<&[u8], &[u8]> {
///   take_while_m_n(3, 6, is_alphabetic)(s)
/// }
///
/// assert_eq!(short_alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(short_alpha(b"lengthy"), Ok((&b"y"[..], &b"length"[..])));
/// assert_eq!(short_alpha(b"latin"), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(short_alpha(b"ed"), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(short_alpha(b"12345"), Err(Err::Error(Error::new(&b"12345"[..], ErrorKind::TakeWhileMN))));
/// ```
pub fn take_while_m_n<F, Input, Error: ParseError<Input>>(
  m: usize,
  n: usize,
  cond: F,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + InputIter + InputLength,
  F: Fn(<Input as InputIter>::Item) -> bool,
{
  move |i: Input| {
    let input = i;

    match input.position(|c| !cond(c)) {
      Some(idx) => {
        if idx >= m {
          if idx <= n {
            let res: IResult<_, _, Error> = if let Ok(index) = input.slice_index(idx) {
              Ok(input.take_split(index))
            } else {
              Err(Err::Error(Error::from_error_kind(
                input,
                ErrorKind::TakeWhileMN,
              )))
            };
            res
          } else {
            let res: IResult<_, _, Error> = if let Ok(index) = input.slice_index(n) {
              Ok(input.take_split(index))
            } else {
              Err(Err::Error(Error::from_error_kind(
                input,
                ErrorKind::TakeWhileMN,
              )))
            };
            res
          }
        } else {
          let e = ErrorKind::TakeWhileMN;
          Err(Err::Error(Error::from_error_kind(input, e)))
        }
      }
      None => {
        let len = input.input_len();
        if len >= n {
          match input.slice_index(n) {
            Ok(index) => Ok(input.take_split(index)),
            Err(_needed) => Err(Err::Error(Error::from_error_kind(
              input,
              ErrorKind::TakeWhileMN,
            ))),
          }
        } else {
          let needed = if m > len { m - len } else { 1 };
          Err(Err::Incomplete(Needed::new(needed)))
        }
      }
    }
  }
}

/// Returns the longest input slice (if any) till a predicate is met.
///
/// The parser will return the longest slice till the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// # Streaming Specific
/// *Streaming version* will return a `Err::Incomplete(Needed::new(1))` if the match reaches the
/// end of input or if there was not match.
///
/// # Example
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, IResult};
/// use nom::bytes::streaming::take_till;
///
/// fn till_colon(s: &str) -> IResult<&str, &str> {
///   take_till(|c| c == ':')(s)
/// }
///
/// assert_eq!(till_colon("latin:123"), Ok((":123", "latin")));
/// assert_eq!(till_colon(":empty matched"), Ok((":empty matched", ""))); //allowed
/// assert_eq!(till_colon("12345"), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(till_colon(""), Err(Err::Incomplete(Needed::new(1))));
/// ```
pub fn take_till<F, Input, Error: ParseError<Input>>(
  cond: F,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position(|c| cond(c))
}

/// Returns the longest (at least 1) input slice till a predicate is met.
///
/// The parser will return the longest slice till the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// # Streaming Specific
/// *Streaming version* will return a `Err::Incomplete(Needed::new(1))` if the match reaches the
/// end of input or if there was not match.
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, Needed, IResult};
/// use nom::bytes::streaming::take_till1;
///
/// fn till_colon(s: &str) -> IResult<&str, &str> {
///   take_till1(|c| c == ':')(s)
/// }
///
/// assert_eq!(till_colon("latin:123"), Ok((":123", "latin")));
/// assert_eq!(till_colon(":empty matched"), Err(Err::Error(Error::new(":empty matched", ErrorKind::TakeTill1))));
/// assert_eq!(till_colon("12345"), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(till_colon(""), Err(Err::Incomplete(Needed::new(1))));
/// ```
pub fn take_till1<F, Input, Error: ParseError<Input>>(
  cond: F,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::TakeTill1;
    i.split_at_position1(|c| cond(c), e)
  }
}

/// Returns an input slice containing the first N input elements (Input[..N]).
///
/// # Streaming Specific
/// *Streaming version* if the input has less than N elements, `take` will
/// return a `Err::Incomplete(Needed::new(M))` where M is the number of
/// additional bytes the parser would need to succeed.
/// It is well defined for `&[u8]` as the number of elements is the byte size,
/// but for types like `&str`, we cannot know how many bytes correspond for
/// the next few chars, so the result will be `Err::Incomplete(Needed::Unknown)`
///
/// # Example
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, IResult};
/// use nom::bytes::streaming::take;
///
/// fn take6(s: &str) -> IResult<&str, &str> {
///   take(6usize)(s)
/// }
///
/// assert_eq!(take6("1234567"), Ok(("7", "123456")));
/// assert_eq!(take6("things"), Ok(("", "things")));
/// assert_eq!(take6("short"), Err(Err::Incomplete(Needed::Unknown)));
/// ```
pub fn take<C, Input, Error: ParseError<Input>>(
  count: C,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputIter + InputTake + InputLength,
  C: ToUsize,
{
  let c = count.to_usize();
  move |i: Input| match i.slice_index(c) {
    Err(i) => Err(Err::Incomplete(i)),
    Ok(index) => Ok(i.take_split(index)),
  }
}

/// Returns the input slice up to the first occurrence of the pattern.
///
/// It doesn't consume the pattern.
///
/// # Streaming Specific
/// *Streaming version* will return a `Err::Incomplete(Needed::new(N))` if the input doesn't
/// contain the pattern or if the input is smaller than the pattern.
/// # Example
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, IResult};
/// use nom::bytes::streaming::take_until;
///
/// fn until_eof(s: &str) -> IResult<&str, &str> {
///   take_until("eof")(s)
/// }
///
/// assert_eq!(until_eof("hello, worldeof"), Ok(("eof", "hello, world")));
/// assert_eq!(until_eof("hello, world"), Err(Err::Incomplete(Needed::Unknown)));
/// assert_eq!(until_eof("hello, worldeo"), Err(Err::Incomplete(Needed::Unknown)));
/// assert_eq!(until_eof("1eof2eof"), Ok(("eof2eof", "1")));
/// ```
pub fn take_until<T, Input, Error: ParseError<Input>>(
  tag: T,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + InputLength + FindSubstring<T>,
  T: Clone,
{
  move |i: Input| {
    let t = tag.clone();

    let res: IResult<_, _, Error> = match i.find_substring(t) {
      None => Err(Err::Incomplete(Needed::Unknown)),
      Some(index) => Ok(i.take_split(index)),
    };
    res
  }
}

/// Returns the non empty input slice up to the first occurrence of the pattern.
///
/// It doesn't consume the pattern.
///
/// # Streaming Specific
/// *Streaming version* will return a `Err::Incomplete(Needed::new(N))` if the input doesn't
/// contain the pattern or if the input is smaller than the pattern.
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, Needed, IResult};
/// use nom::bytes::streaming::take_until1;
///
/// fn until_eof(s: &str) -> IResult<&str, &str> {
///   take_until1("eof")(s)
/// }
///
/// assert_eq!(until_eof("hello, worldeof"), Ok(("eof", "hello, world")));
/// assert_eq!(until_eof("hello, world"), Err(Err::Incomplete(Needed::Unknown)));
/// assert_eq!(until_eof("hello, worldeo"), Err(Err::Incomplete(Needed::Unknown)));
/// assert_eq!(until_eof("1eof2eof"), Ok(("eof2eof", "1")));
/// assert_eq!(until_eof("eof"),  Err(Err::Error(Error::new("eof", ErrorKind::TakeUntil))));
/// ```
pub fn take_until1<T, Input, Error: ParseError<Input>>(
  tag: T,
) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + InputLength + FindSubstring<T>,
  T: Clone,
{
  move |i: Input| {
    let t = tag.clone();

    let res: IResult<_, _, Error> = match i.find_substring(t) {
      None => Err(Err::Incomplete(Needed::Unknown)),
      Some(0) => Err(Err::Error(Error::from_error_kind(i, ErrorKind::TakeUntil))),
      Some(index) => Ok(i.take_split(index)),
    };
    res
  }
}

/// Matches a byte string with escaped characters.
///
/// * The first argument matches the normal characters (it must not accept the control character)
/// * The second argument is the control character (like `\` in most languages)
/// * The third argument matches the escaped characters
/// # Example
/// ```
/// # use nom::{Err, error::ErrorKind, Needed, IResult};
/// # use nom::character::complete::digit1;
/// use nom::bytes::streaming::escaped;
/// use nom::character::streaming::one_of;
///
/// fn esc(s: &str) -> IResult<&str, &str> {
///   escaped(digit1, '\\', one_of("\"n\\"))(s)
/// }
///
/// assert_eq!(esc("123;"), Ok((";", "123")));
/// assert_eq!(esc("12\\\"34;"), Ok((";", "12\\\"34")));
/// ```
///
pub fn escaped<Input, Error, F, G, O1, O2>(
  mut normal: F,
  control_char: char,
  mut escapable: G,
) -> impl FnMut(Input) -> IResult<Input, Input, Error>
where
  Input: Clone
    + crate::traits::Offset
    + InputLength
    + InputTake
    + InputTakeAtPosition
    + Slice<RangeFrom<usize>>
    + InputIter,
  <Input as InputIter>::Item: crate::traits::AsChar,
  F: Parser<Input, O1, Error>,
  G: Parser<Input, O2, Error>,
  Error: ParseError<Input>,
{
  use crate::traits::AsChar;

  move |input: Input| {
    let mut i = input.clone();

    while i.input_len() > 0 {
      let current_len = i.input_len();

      match normal.parse(i.clone()) {
        Ok((i2, _)) => {
          if i2.input_len() == 0 {
            return Err(Err::Incomplete(Needed::Unknown));
          } else if i2.input_len() == current_len {
            let index = input.offset(&i2);
            return Ok(input.take_split(index));
          } else {
            i = i2;
          }
        }
        Err(Err::Error(_)) => {
          // unwrap() should be safe here since index < $i.input_len()
          if i.iter_elements().next().unwrap().as_char() == control_char {
            let next = control_char.len_utf8();
            if next >= i.input_len() {
              return Err(Err::Incomplete(Needed::new(1)));
            } else {
              match escapable.parse(i.slice(next..)) {
                Ok((i2, _)) => {
                  if i2.input_len() == 0 {
                    return Err(Err::Incomplete(Needed::Unknown));
                  } else {
                    i = i2;
                  }
                }
                Err(e) => return Err(e),
              }
            }
          } else {
            let index = input.offset(&i);
            return Ok(input.take_split(index));
          }
        }
        Err(e) => {
          return Err(e);
        }
      }
    }

    Err(Err::Incomplete(Needed::Unknown))
  }
}

/// Matches a byte string with escaped characters.
///
/// * The first argument matches the normal characters (it must not match the control character)
/// * The second argument is the control character (like `\` in most languages)
/// * The third argument matches the escaped characters and transforms them
///
/// As an example, the chain `abc\tdef` could be `abc    def` (it also consumes the control character)
///
/// ```
/// # use nom::{Err, error::ErrorKind, Needed, IResult};
/// # use std::str::from_utf8;
/// use nom::bytes::streaming::{escaped_transform, tag};
/// use nom::character::streaming::alpha1;
/// use nom::branch::alt;
/// use nom::combinator::value;
///
/// fn parser(input: &str) -> IResult<&str, String> {
///   escaped_transform(
///     alpha1,
///     '\\',
///     alt((
///       value("\\", tag("\\")),
///       value("\"", tag("\"")),
///       value("\n", tag("n")),
///     ))
///   )(input)
/// }
///
/// assert_eq!(parser("ab\\\"cd\""), Ok(("\"", String::from("ab\"cd"))));
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
pub fn escaped_transform<Input, Error, F, G, O1, O2, ExtendItem, Output>(
  mut normal: F,
  control_char: char,
  mut transform: G,
) -> impl FnMut(Input) -> IResult<Input, Output, Error>
where
  Input: Clone
    + crate::traits::Offset
    + InputLength
    + InputTake
    + InputTakeAtPosition
    + Slice<RangeFrom<usize>>
    + InputIter,
  Input: crate::traits::ExtendInto<Item = ExtendItem, Extender = Output>,
  O1: crate::traits::ExtendInto<Item = ExtendItem, Extender = Output>,
  O2: crate::traits::ExtendInto<Item = ExtendItem, Extender = Output>,
  <Input as InputIter>::Item: crate::traits::AsChar,
  F: Parser<Input, O1, Error>,
  G: Parser<Input, O2, Error>,
  Error: ParseError<Input>,
{
  use crate::traits::AsChar;

  move |input: Input| {
    let mut index = 0;
    let mut res = input.new_builder();

    let i = input.clone();

    while index < i.input_len() {
      let current_len = i.input_len();
      let remainder = i.slice(index..);
      match normal.parse(remainder.clone()) {
        Ok((i2, o)) => {
          o.extend_into(&mut res);
          if i2.input_len() == 0 {
            return Err(Err::Incomplete(Needed::Unknown));
          } else if i2.input_len() == current_len {
            return Ok((remainder, res));
          } else {
            index = input.offset(&i2);
          }
        }
        Err(Err::Error(_)) => {
          // unwrap() should be safe here since index < $i.input_len()
          if remainder.iter_elements().next().unwrap().as_char() == control_char {
            let next = index + control_char.len_utf8();
            let input_len = input.input_len();

            if next >= input_len {
              return Err(Err::Incomplete(Needed::Unknown));
            } else {
              match transform.parse(i.slice(next..)) {
                Ok((i2, o)) => {
                  o.extend_into(&mut res);
                  if i2.input_len() == 0 {
                    return Err(Err::Incomplete(Needed::Unknown));
                  } else {
                    index = input.offset(&i2);
                  }
                }
                Err(e) => return Err(e),
              }
            }
          } else {
            return Ok((remainder, res));
          }
        }
        Err(e) => return Err(e),
      }
    }
    Err(Err::Incomplete(Needed::Unknown))
  }
}

#[cfg(test)]
mod tests {
  use crate::character::is_alphabetic;
  use crate::character::streaming::{
    alpha1 as alpha, alphanumeric1 as alphanumeric, digit1 as digit, hex_digit1 as hex_digit,
    multispace1 as multispace, oct_digit1 as oct_digit, space1 as space,
  };
  use crate::error::ErrorKind;
  use crate::internal::{Err, IResult, Needed};
  #[cfg(feature = "alloc")]
  use crate::{
    branch::alt,
    bytes::complete::{escaped, escaped_transform, tag},
    combinator::{map, value},
    lib::std::string::String,
    lib::std::vec::Vec,
  };

  #[test]
  fn is_a() {
    use crate::bytes::streaming::is_a;

    fn a_or_b(i: &[u8]) -> IResult<&[u8], &[u8]> {
      is_a("ab")(i)
    }

    let a = &b"abcd"[..];
    assert_eq!(a_or_b(a), Ok((&b"cd"[..], &b"ab"[..])));

    let b = &b"bcde"[..];
    assert_eq!(a_or_b(b), Ok((&b"cde"[..], &b"b"[..])));

    let c = &b"cdef"[..];
    assert_eq!(
      a_or_b(c),
      Err(Err::Error(error_position!(c, ErrorKind::IsA)))
    );

    let d = &b"bacdef"[..];
    assert_eq!(a_or_b(d), Ok((&b"cdef"[..], &b"ba"[..])));
  }

  #[test]
  fn is_not() {
    use crate::bytes::streaming::is_not;

    fn a_or_b(i: &[u8]) -> IResult<&[u8], &[u8]> {
      is_not("ab")(i)
    }

    let a = &b"cdab"[..];
    assert_eq!(a_or_b(a), Ok((&b"ab"[..], &b"cd"[..])));

    let b = &b"cbde"[..];
    assert_eq!(a_or_b(b), Ok((&b"bde"[..], &b"c"[..])));

    let c = &b"abab"[..];
    assert_eq!(
      a_or_b(c),
      Err(Err::Error(error_position!(c, ErrorKind::IsNot)))
    );

    let d = &b"cdefba"[..];
    assert_eq!(a_or_b(d), Ok((&b"ba"[..], &b"cdef"[..])));

    let e = &b"e"[..];
    assert_eq!(a_or_b(e), Err(Err::Incomplete(Needed::new(1))));
  }

  #[cfg(feature = "alloc")]
  #[allow(unused_variables)]
  #[test]
  fn escaping() {
    use crate::character::streaming::one_of;

    fn esc(i: &[u8]) -> IResult<&[u8], &[u8]> {
      escaped(alpha, '\\', one_of("\"n\\"))(i)
    }
    assert_eq!(esc(&b"abcd;"[..]), Ok((&b";"[..], &b"abcd"[..])));
    assert_eq!(esc(&b"ab\\\"cd;"[..]), Ok((&b";"[..], &b"ab\\\"cd"[..])));
    assert_eq!(esc(&b"\\\"abcd;"[..]), Ok((&b";"[..], &b"\\\"abcd"[..])));
    assert_eq!(esc(&b"\\n;"[..]), Ok((&b";"[..], &b"\\n"[..])));
    assert_eq!(esc(&b"ab\\\"12"[..]), Ok((&b"12"[..], &b"ab\\\""[..])));
    assert_eq!(
      esc(&b"AB\\"[..]),
      Err(Err::Error(error_position!(
        &b"AB\\"[..],
        ErrorKind::Escaped
      )))
    );
    assert_eq!(
      esc(&b"AB\\A"[..]),
      Err(Err::Error(error_node_position!(
        &b"AB\\A"[..],
        ErrorKind::Escaped,
        error_position!(&b"A"[..], ErrorKind::OneOf)
      )))
    );

    fn esc2(i: &[u8]) -> IResult<&[u8], &[u8]> {
      escaped(digit, '\\', one_of("\"n\\"))(i)
    }
    assert_eq!(esc2(&b"12\\nnn34"[..]), Ok((&b"nn34"[..], &b"12\\n"[..])));
  }

  #[cfg(feature = "alloc")]
  #[test]
  fn escaping_str() {
    use crate::character::streaming::one_of;

    fn esc(i: &str) -> IResult<&str, &str> {
      escaped(alpha, '\\', one_of("\"n\\"))(i)
    }
    assert_eq!(esc("abcd;"), Ok((";", "abcd")));
    assert_eq!(esc("ab\\\"cd;"), Ok((";", "ab\\\"cd")));
    assert_eq!(esc("\\\"abcd;"), Ok((";", "\\\"abcd")));
    assert_eq!(esc("\\n;"), Ok((";", "\\n")));
    assert_eq!(esc("ab\\\"12"), Ok(("12", "ab\\\"")));
    assert_eq!(
      esc("AB\\"),
      Err(Err::Error(error_position!("AB\\", ErrorKind::Escaped)))
    );
    assert_eq!(
      esc("AB\\A"),
      Err(Err::Error(error_node_position!(
        "AB\\A",
        ErrorKind::Escaped,
        error_position!("A", ErrorKind::OneOf)
      )))
    );

    fn esc2(i: &str) -> IResult<&str, &str> {
      escaped(digit, '\\', one_of("\"n\\"))(i)
    }
    assert_eq!(esc2("12\\nnn34"), Ok(("nn34", "12\\n")));

    fn esc3(i: &str) -> IResult<&str, &str> {
      escaped(alpha, '\u{241b}', one_of("\"n"))(i)
    }
    assert_eq!(esc3("ab␛ncd;"), Ok((";", "ab␛ncd")));
  }

  #[cfg(feature = "alloc")]
  fn to_s(i: Vec<u8>) -> String {
    String::from_utf8_lossy(&i).into_owned()
  }

  #[cfg(feature = "alloc")]
  #[test]
  fn escape_transform() {
    fn esc(i: &[u8]) -> IResult<&[u8], String> {
      map(
        escaped_transform(
          alpha,
          '\\',
          alt((
            value(&b"\\"[..], tag("\\")),
            value(&b"\""[..], tag("\"")),
            value(&b"\n"[..], tag("n")),
          )),
        ),
        to_s,
      )(i)
    }

    assert_eq!(esc(&b"abcd;"[..]), Ok((&b";"[..], String::from("abcd"))));
    assert_eq!(
      esc(&b"ab\\\"cd;"[..]),
      Ok((&b";"[..], String::from("ab\"cd")))
    );
    assert_eq!(
      esc(&b"\\\"abcd;"[..]),
      Ok((&b";"[..], String::from("\"abcd")))
    );
    assert_eq!(esc(&b"\\n;"[..]), Ok((&b";"[..], String::from("\n"))));
    assert_eq!(
      esc(&b"ab\\\"12"[..]),
      Ok((&b"12"[..], String::from("ab\"")))
    );
    assert_eq!(
      esc(&b"AB\\"[..]),
      Err(Err::Error(error_position!(
        &b"\\"[..],
        ErrorKind::EscapedTransform
      )))
    );
    assert_eq!(
      esc(&b"AB\\A"[..]),
      Err(Err::Error(error_node_position!(
        &b"AB\\A"[..],
        ErrorKind::EscapedTransform,
        error_position!(&b"A"[..], ErrorKind::Tag)
      )))
    );

    fn esc2(i: &[u8]) -> IResult<&[u8], String> {
      map(
        escaped_transform(
          alpha,
          '&',
          alt((
            value("è".as_bytes(), tag("egrave;")),
            value("à".as_bytes(), tag("agrave;")),
          )),
        ),
        to_s,
      )(i)
    }
    assert_eq!(
      esc2(&b"ab&egrave;DEF;"[..]),
      Ok((&b";"[..], String::from("abèDEF")))
    );
    assert_eq!(
      esc2(&b"ab&egrave;D&agrave;EF;"[..]),
      Ok((&b";"[..], String::from("abèDàEF")))
    );
  }

  #[cfg(feature = "std")]
  #[test]
  fn escape_transform_str() {
    fn esc(i: &str) -> IResult<&str, String> {
      escaped_transform(
        alpha,
        '\\',
        alt((
          value("\\", tag("\\")),
          value("\"", tag("\"")),
          value("\n", tag("n")),
        )),
      )(i)
    }

    assert_eq!(esc("abcd;"), Ok((";", String::from("abcd"))));
    assert_eq!(esc("ab\\\"cd;"), Ok((";", String::from("ab\"cd"))));
    assert_eq!(esc("\\\"abcd;"), Ok((";", String::from("\"abcd"))));
    assert_eq!(esc("\\n;"), Ok((";", String::from("\n"))));
    assert_eq!(esc("ab\\\"12"), Ok(("12", String::from("ab\""))));
    assert_eq!(
      esc("AB\\"),
      Err(Err::Error(error_position!(
        "\\",
        ErrorKind::EscapedTransform
      )))
    );
    assert_eq!(
      esc("AB\\A"),
      Err(Err::Error(error_node_position!(
        "AB\\A",
        ErrorKind::EscapedTransform,
        error_position!("A", ErrorKind::Tag)
      )))
    );

    fn esc2(i: &str) -> IResult<&str, String> {
      escaped_transform(
        alpha,
        '&',
        alt((value("è", tag("egrave;")), value("à", tag("agrave;")))),
      )(i)
    }
    assert_eq!(esc2("ab&egrave;DEF;"), Ok((";", String::from("abèDEF"))));
    assert_eq!(
      esc2("ab&egrave;D&agrave;EF;"),
      Ok((";", String::from("abèDàEF")))
    );

    fn esc3(i: &str) -> IResult<&str, String> {
      escaped_transform(
        alpha,
        '␛',
        alt((value("\0", tag("0")), value("\n", tag("n")))),
      )(i)
    }
    assert_eq!(esc3("a␛0bc␛n"), Ok(("", String::from("a\0bc\n"))));
  }

  #[test]
  fn take_until_incomplete() {
    use crate::bytes::streaming::take_until;
    fn y(i: &[u8]) -> IResult<&[u8], &[u8]> {
      take_until("end")(i)
    }
    assert_eq!(y(&b"nd"[..]), Err(Err::Incomplete(Needed::Unknown)));
    assert_eq!(y(&b"123"[..]), Err(Err::Incomplete(Needed::Unknown)));
    assert_eq!(y(&b"123en"[..]), Err(Err::Incomplete(Needed::Unknown)));
  }

  #[test]
  fn take_until_incomplete_s() {
    use crate::bytes::streaming::take_until;
    fn ys(i: &str) -> IResult<&str, &str> {
      take_until("end")(i)
    }
    assert_eq!(ys("123en"), Err(Err::Incomplete(Needed::Unknown)));
  }

  #[test]
  fn recognize() {
    use crate::bytes::streaming::{tag, take};
    use crate::combinator::recognize;
    use crate::sequence::delimited;

    fn x(i: &[u8]) -> IResult<&[u8], &[u8]> {
      recognize(delimited(tag("<!--"), take(5_usize), tag("-->")))(i)
    }
    let r = x(&b"<!-- abc --> aaa"[..]);
    assert_eq!(r, Ok((&b" aaa"[..], &b"<!-- abc -->"[..])));

    let semicolon = &b";"[..];

    fn ya(i: &[u8]) -> IResult<&[u8], &[u8]> {
      recognize(alpha)(i)
    }
    let ra = ya(&b"abc;"[..]);
    assert_eq!(ra, Ok((semicolon, &b"abc"[..])));

    fn yd(i: &[u8]) -> IResult<&[u8], &[u8]> {
      recognize(digit)(i)
    }
    let rd = yd(&b"123;"[..]);
    assert_eq!(rd, Ok((semicolon, &b"123"[..])));

    fn yhd(i: &[u8]) -> IResult<&[u8], &[u8]> {
      recognize(hex_digit)(i)
    }
    let rhd = yhd(&b"123abcDEF;"[..]);
    assert_eq!(rhd, Ok((semicolon, &b"123abcDEF"[..])));

    fn yod(i: &[u8]) -> IResult<&[u8], &[u8]> {
      recognize(oct_digit)(i)
    }
    let rod = yod(&b"1234567;"[..]);
    assert_eq!(rod, Ok((semicolon, &b"1234567"[..])));

    fn yan(i: &[u8]) -> IResult<&[u8], &[u8]> {
      recognize(alphanumeric)(i)
    }
    let ran = yan(&b"123abc;"[..]);
    assert_eq!(ran, Ok((semicolon, &b"123abc"[..])));

    fn ys(i: &[u8]) -> IResult<&[u8], &[u8]> {
      recognize(space)(i)
    }
    let rs = ys(&b" \t;"[..]);
    assert_eq!(rs, Ok((semicolon, &b" \t"[..])));

    fn yms(i: &[u8]) -> IResult<&[u8], &[u8]> {
      recognize(multispace)(i)
    }
    let rms = yms(&b" \t\r\n;"[..]);
    assert_eq!(rms, Ok((semicolon, &b" \t\r\n"[..])));
  }

  #[test]
  fn take_while() {
    use crate::bytes::streaming::take_while;

    fn f(i: &[u8]) -> IResult<&[u8], &[u8]> {
      take_while(is_alphabetic)(i)
    }
    let a = b"";
    let b = b"abcd";
    let c = b"abcd123";
    let d = b"123";

    assert_eq!(f(&a[..]), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f(&b[..]), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f(&c[..]), Ok((&d[..], &b[..])));
    assert_eq!(f(&d[..]), Ok((&d[..], &a[..])));
  }

  #[test]
  fn take_while1() {
    use crate::bytes::streaming::take_while1;

    fn f(i: &[u8]) -> IResult<&[u8], &[u8]> {
      take_while1(is_alphabetic)(i)
    }
    let a = b"";
    let b = b"abcd";
    let c = b"abcd123";
    let d = b"123";

    assert_eq!(f(&a[..]), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f(&b[..]), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f(&c[..]), Ok((&b"123"[..], &b[..])));
    assert_eq!(
      f(&d[..]),
      Err(Err::Error(error_position!(&d[..], ErrorKind::TakeWhile1)))
    );
  }

  #[test]
  fn take_while_m_n() {
    use crate::bytes::streaming::take_while_m_n;

    fn x(i: &[u8]) -> IResult<&[u8], &[u8]> {
      take_while_m_n(2, 4, is_alphabetic)(i)
    }
    let a = b"";
    let b = b"a";
    let c = b"abc";
    let d = b"abc123";
    let e = b"abcde";
    let f = b"123";

    assert_eq!(x(&a[..]), Err(Err::Incomplete(Needed::new(2))));
    assert_eq!(x(&b[..]), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(x(&c[..]), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(x(&d[..]), Ok((&b"123"[..], &c[..])));
    assert_eq!(x(&e[..]), Ok((&b"e"[..], &b"abcd"[..])));
    assert_eq!(
      x(&f[..]),
      Err(Err::Error(error_position!(&f[..], ErrorKind::TakeWhileMN)))
    );
  }

  #[test]
  fn take_till() {
    use crate::bytes::streaming::take_till;

    fn f(i: &[u8]) -> IResult<&[u8], &[u8]> {
      take_till(is_alphabetic)(i)
    }
    let a = b"";
    let b = b"abcd";
    let c = b"123abcd";
    let d = b"123";

    assert_eq!(f(&a[..]), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f(&b[..]), Ok((&b"abcd"[..], &b""[..])));
    assert_eq!(f(&c[..]), Ok((&b"abcd"[..], &b"123"[..])));
    assert_eq!(f(&d[..]), Err(Err::Incomplete(Needed::new(1))));
  }

  #[test]
  fn take_till1() {
    use crate::bytes::streaming::take_till1;

    fn f(i: &[u8]) -> IResult<&[u8], &[u8]> {
      take_till1(is_alphabetic)(i)
    }
    let a = b"";
    let b = b"abcd";
    let c = b"123abcd";
    let d = b"123";

    assert_eq!(f(&a[..]), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(
      f(&b[..]),
      Err(Err::Error(error_position!(&b[..], ErrorKind::TakeTill1)))
    );
    assert_eq!(f(&c[..]), Ok((&b"abcd"[..], &b"123"[..])));
    assert_eq!(f(&d[..]), Err(Err::Incomplete(Needed::new(1))));
  }

  #[test]
  fn take_while_utf8() {
    use crate::bytes::streaming::take_while;

    fn f(i: &str) -> IResult<&str, &str> {
      take_while(|c| c != '點')(i)
    }

    assert_eq!(f(""), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f("abcd"), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f("abcd點"), Ok(("點", "abcd")));
    assert_eq!(f("abcd點a"), Ok(("點a", "abcd")));

    fn g(i: &str) -> IResult<&str, &str> {
      take_while(|c| c == '點')(i)
    }

    assert_eq!(g(""), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(g("點abcd"), Ok(("abcd", "點")));
    assert_eq!(g("點點點a"), Ok(("a", "點點點")));
  }

  #[test]
  fn take_till_utf8() {
    use crate::bytes::streaming::take_till;

    fn f(i: &str) -> IResult<&str, &str> {
      take_till(|c| c == '點')(i)
    }

    assert_eq!(f(""), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f("abcd"), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f("abcd點"), Ok(("點", "abcd")));
    assert_eq!(f("abcd點a"), Ok(("點a", "abcd")));

    fn g(i: &str) -> IResult<&str, &str> {
      take_till(|c| c != '點')(i)
    }

    assert_eq!(g(""), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(g("點abcd"), Ok(("abcd", "點")));
    assert_eq!(g("點點點a"), Ok(("a", "點點點")));
  }

  #[test]
  fn take_utf8() {
    use crate::bytes::streaming::{take, take_while};

    fn f(i: &str) -> IResult<&str, &str> {
      take(3_usize)(i)
    }

    assert_eq!(f(""), Err(Err::Incomplete(Needed::Unknown)));
    assert_eq!(f("ab"), Err(Err::Incomplete(Needed::Unknown)));
    assert_eq!(f("點"), Err(Err::Incomplete(Needed::Unknown)));
    assert_eq!(f("ab點cd"), Ok(("cd", "ab點")));
    assert_eq!(f("a點bcd"), Ok(("cd", "a點b")));
    assert_eq!(f("a點b"), Ok(("", "a點b")));

    fn g(i: &str) -> IResult<&str, &str> {
      take_while(|c| c == '點')(i)
    }

    assert_eq!(g(""), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(g("點abcd"), Ok(("abcd", "點")));
    assert_eq!(g("點點點a"), Ok(("a", "點點點")));
  }

  #[test]
  fn take_while_m_n_utf8() {
    use crate::bytes::streaming::take_while_m_n;

    fn parser(i: &str) -> IResult<&str, &str> {
      take_while_m_n(1, 1, |c| c == 'A' || c == '😃')(i)
    }
    assert_eq!(parser("A!"), Ok(("!", "A")));
    assert_eq!(parser("😃!"), Ok(("!", "😃")));
  }

  #[test]
  fn take_while_m_n_utf8_full_match() {
    use crate::bytes::streaming::take_while_m_n;

    fn parser(i: &str) -> IResult<&str, &str> {
      take_while_m_n(1, 1, |c: char| c.is_alphabetic())(i)
    }
    assert_eq!(parser("øn"), Ok(("n", "ø")));
  }

  #[test]
  #[cfg(feature = "std")]
  fn recognize_take_while() {
    use crate::bytes::streaming::take_while;
    use crate::character::is_alphanumeric;
    use crate::combinator::recognize;

    fn x(i: &[u8]) -> IResult<&[u8], &[u8]> {
      take_while(is_alphanumeric)(i)
    }
    fn y(i: &[u8]) -> IResult<&[u8], &[u8]> {
      recognize(x)(i)
    }
    assert_eq!(x(&b"ab."[..]), Ok((&b"."[..], &b"ab"[..])));
    println!("X: {:?}", x(&b"ab"[..]));
    assert_eq!(y(&b"ab."[..]), Ok((&b"."[..], &b"ab"[..])));
  }

  #[test]
  fn length_bytes() {
    use crate::{bytes::streaming::tag, multi::length_data, number::streaming::le_u8};

    fn x(i: &[u8]) -> IResult<&[u8], &[u8]> {
      length_data(le_u8)(i)
    }
    assert_eq!(x(b"\x02..>>"), Ok((&b">>"[..], &b".."[..])));
    assert_eq!(x(b"\x02.."), Ok((&[][..], &b".."[..])));
    assert_eq!(x(b"\x02."), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(x(b"\x02"), Err(Err::Incomplete(Needed::new(2))));

    fn y(i: &[u8]) -> IResult<&[u8], &[u8]> {
      let (i, _) = tag("magic")(i)?;
      length_data(le_u8)(i)
    }
    assert_eq!(y(b"magic\x02..>>"), Ok((&b">>"[..], &b".."[..])));
    assert_eq!(y(b"magic\x02.."), Ok((&[][..], &b".."[..])));
    assert_eq!(y(b"magic\x02."), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(y(b"magic\x02"), Err(Err::Incomplete(Needed::new(2))));
  }

  #[cfg(feature = "alloc")]
  #[test]
  fn case_insensitive() {
    use crate::bytes::streaming::tag_no_case;

    fn test(i: &[u8]) -> IResult<&[u8], &[u8]> {
      tag_no_case("ABcd")(i)
    }
    assert_eq!(test(&b"aBCdefgh"[..]), Ok((&b"efgh"[..], &b"aBCd"[..])));
    assert_eq!(test(&b"abcdefgh"[..]), Ok((&b"efgh"[..], &b"abcd"[..])));
    assert_eq!(test(&b"ABCDefgh"[..]), Ok((&b"efgh"[..], &b"ABCD"[..])));
    assert_eq!(test(&b"ab"[..]), Err(Err::Incomplete(Needed::new(2))));
    assert_eq!(
      test(&b"Hello"[..]),
      Err(Err::Error(error_position!(&b"Hello"[..], ErrorKind::Tag)))
    );
    assert_eq!(
      test(&b"Hel"[..]),
      Err(Err::Error(error_position!(&b"Hel"[..], ErrorKind::Tag)))
    );

    fn test2(i: &str) -> IResult<&str, &str> {
      tag_no_case("ABcd")(i)
    }
    assert_eq!(test2("aBCdefgh"), Ok(("efgh", "aBCd")));
    assert_eq!(test2("abcdefgh"), Ok(("efgh", "abcd")));
    assert_eq!(test2("ABCDefgh"), Ok(("efgh", "ABCD")));
    assert_eq!(test2("ab"), Err(Err::Incomplete(Needed::new(2))));
    assert_eq!(
      test2("Hello"),
      Err(Err::Error(error_position!(&"Hello"[..], ErrorKind::Tag)))
    );
    assert_eq!(
      test2("Hel"),
      Err(Err::Error(error_position!(&"Hel"[..], ErrorKind::Tag)))
    );
  }

  #[test]
  fn tag_fixed_size_array() {
    use crate::bytes::streaming::tag;

    fn test(i: &[u8]) -> IResult<&[u8], &[u8]> {
      tag([0x42])(i)
    }
    fn test2(i: &[u8]) -> IResult<&[u8], &[u8]> {
      tag(&[0x42])(i)
    }
    let input = [0x42, 0x00];
    assert_eq!(test(&input), Ok((&b"\x00"[..], &b"\x42"[..])));
    assert_eq!(test2(&input), Ok((&b"\x00"[..], &b"\x42"[..])));
  }
}
