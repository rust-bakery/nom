//! Parsers recognizing bytes streams, complete input version

use crate::error::ParseContext;
use crate::error::ParserKind;
use crate::internal::{Outcome, ParseResult, Parser};
use crate::lib::std::ops::RangeFrom;
use crate::lib::std::result::Result::*;
use crate::traits::{
  Compare, CompareResult, FindSubstring, FindToken, InputIter, InputLength, InputTake,
  InputTakeAtPosition, Slice, ToUsize,
};

/// Recognizes a pattern
///
/// The input data will be compared to the tag combinator's argument and will return the part of
/// the input that matches the argument
///
/// It will return `Err(Outcome::Failure((_, ParserKind::Tag)))` if the input doesn't match the pattern
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::complete::tag;
///
/// fn parser(s: &str) -> ParseResult<&str, &str> {
///   tag("Hello")(s)
/// }
///
/// assert_eq!(parser("Hello, World!"), Ok((", World!", "Hello")));
/// assert_eq!(parser("Something"), Err(Outcome::Failure(Context::new("Something", ParserKind::Tag))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::Tag))));
/// ```
pub fn tag<T, Input, Context: ParseContext<Input>>(
  tag: T,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTake + Compare<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let tag_len = tag.input_len();
    let t = tag.clone();
    let res: ParseResult<_, _, Context> = match i.compare(t) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      _ => {
        let e: ParserKind = ParserKind::Tag;
        Err(Outcome::Failure(Context::from_parser_kind(i, e)))
      }
    };
    res
  }
}

/// Recognizes a case insensitive pattern.
///
/// The input data will be compared to the tag combinator's argument and will return the part of
/// the input that matches the argument with no regard to case.
///
/// It will return `Err(Outcome::Failure((_, ParserKind::Tag)))` if the input doesn't match the pattern.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::complete::tag_no_case;
///
/// fn parser(s: &str) -> ParseResult<&str, &str> {
///   tag_no_case("hello")(s)
/// }
///
/// assert_eq!(parser("Hello, World!"), Ok((", World!", "Hello")));
/// assert_eq!(parser("hello, World!"), Ok((", World!", "hello")));
/// assert_eq!(parser("HeLlO, World!"), Ok((", World!", "HeLlO")));
/// assert_eq!(parser("Something"), Err(Outcome::Failure(Context::new("Something", ParserKind::Tag))));
/// assert_eq!(parser(""), Err(Outcome::Failure(Context::new("", ParserKind::Tag))));
/// ```
pub fn tag_no_case<T, Input, Context: ParseContext<Input>>(
  tag: T,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTake + Compare<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let tag_len = tag.input_len();
    let t = tag.clone();

    let res: ParseResult<_, _, Context> = match (i).compare_no_case(t) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      _ => {
        let e: ParserKind = ParserKind::Tag;
        Err(Outcome::Failure(Context::from_parser_kind(i, e)))
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
/// It will return a `Outcome::Failure(("", ParserKind::IsNot))` if the pattern wasn't met.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::complete::is_not;
///
/// fn not_space(s: &str) -> ParseResult<&str, &str> {
///   is_not(" \t\r\n")(s)
/// }
///
/// assert_eq!(not_space("Hello, World!"), Ok((" World!", "Hello,")));
/// assert_eq!(not_space("Sometimes\t"), Ok(("\t", "Sometimes")));
/// assert_eq!(not_space("Nospace"), Ok(("", "Nospace")));
/// assert_eq!(not_space(""), Err(Outcome::Failure(Context::new("", ParserKind::IsNot))));
/// ```
pub fn is_not<T, Input, Context: ParseContext<Input>>(
  arr: T,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTakeAtPosition,
  T: FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ParserKind = ParserKind::IsNot;
    i.split_at_position1_complete(|c| arr.find_token(c), e)
  }
}

/// Returns the longest slice of the matches the pattern.
///
/// The parser will return the longest slice consisting of the characters in provided in the
/// combinator's argument.
///
/// It will return a `Err(Outcome::Failure((_, ParserKind::IsA)))` if the pattern wasn't met.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::complete::is_a;
///
/// fn hex(s: &str) -> ParseResult<&str, &str> {
///   is_a("1234567890ABCDEF")(s)
/// }
///
/// assert_eq!(hex("123 and voila"), Ok((" and voila", "123")));
/// assert_eq!(hex("DEADBEEF and others"), Ok((" and others", "DEADBEEF")));
/// assert_eq!(hex("BADBABEsomething"), Ok(("something", "BADBABE")));
/// assert_eq!(hex("D15EA5E"), Ok(("", "D15EA5E")));
/// assert_eq!(hex(""), Err(Outcome::Failure(Context::new("", ParserKind::IsA))));
/// ```
pub fn is_a<T, Input, Context: ParseContext<Input>>(
  arr: T,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTakeAtPosition,
  T: FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ParserKind = ParserKind::IsA;
    i.split_at_position1_complete(|c| !arr.find_token(c), e)
  }
}

/// Returns the longest input slice (if any) that matches the predicate.
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::ParserKind, Needed, ParseResult};
/// use nom::bytes::complete::take_while;
/// use nom::character::is_alphabetic;
///
/// fn alpha(s: &[u8]) -> ParseResult<&[u8], &[u8]> {
///   take_while(is_alphabetic)(s)
/// }
///
/// assert_eq!(alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(alpha(b"12345"), Ok((&b"12345"[..], &b""[..])));
/// assert_eq!(alpha(b"latin"), Ok((&b""[..], &b"latin"[..])));
/// assert_eq!(alpha(b""), Ok((&b""[..], &b""[..])));
/// ```
pub fn take_while<F, Input, Context: ParseContext<Input>>(
  cond: F,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position_complete(|c| !cond(c))
}

/// Returns the longest (at least 1) input slice that matches the predicate.
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// It will return an `Err(Outcome::Failure((_, ParserKind::TakeWhile1)))` if the pattern wasn't met.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::complete::take_while1;
/// use nom::character::is_alphabetic;
///
/// fn alpha(s: &[u8]) -> ParseResult<&[u8], &[u8]> {
///   take_while1(is_alphabetic)(s)
/// }
///
/// assert_eq!(alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(alpha(b"latin"), Ok((&b""[..], &b"latin"[..])));
/// assert_eq!(alpha(b"12345"), Err(Outcome::Failure(Context::new(&b"12345"[..], ParserKind::TakeWhile1))));
/// ```
pub fn take_while1<F, Input, Context: ParseContext<Input>>(
  cond: F,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ParserKind = ParserKind::TakeWhile1;
    i.split_at_position1_complete(|c| !cond(c), e)
  }
}

/// Returns the longest (m <= len <= n) input slice  that matches the predicate.
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// It will return an `Outcome::Failure((_, ParserKind::TakeWhileMN))` if the pattern wasn't met or is out
/// of range (m <= len <= n).
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::complete::take_while_m_n;
/// use nom::character::is_alphabetic;
///
/// fn short_alpha(s: &[u8]) -> ParseResult<&[u8], &[u8]> {
///   take_while_m_n(3, 6, is_alphabetic)(s)
/// }
///
/// assert_eq!(short_alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(short_alpha(b"lengthy"), Ok((&b"y"[..], &b"length"[..])));
/// assert_eq!(short_alpha(b"latin"), Ok((&b""[..], &b"latin"[..])));
/// assert_eq!(short_alpha(b"ed"), Err(Outcome::Failure(Context::new(&b"ed"[..], ParserKind::TakeWhileMN))));
/// assert_eq!(short_alpha(b"12345"), Err(Outcome::Failure(Context::new(&b"12345"[..], ParserKind::TakeWhileMN))));
/// ```
pub fn take_while_m_n<F, Input, Context: ParseContext<Input>>(
  m: usize,
  n: usize,
  cond: F,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTake + InputIter + InputLength + Slice<RangeFrom<usize>>,
  F: Fn(<Input as InputIter>::Item) -> bool,
{
  move |i: Input| {
    let input = i;

    match input.position(|c| !cond(c)) {
      Some(idx) => {
        if idx >= m {
          if idx <= n {
            let res: ParseResult<_, _, Context> = if let Ok(index) = input.slice_index(idx) {
              Ok(input.take_split(index))
            } else {
              Err(Outcome::Failure(Context::from_parser_kind(
                input,
                ParserKind::TakeWhileMN,
              )))
            };
            res
          } else {
            let res: ParseResult<_, _, Context> = if let Ok(index) = input.slice_index(n) {
              Ok(input.take_split(index))
            } else {
              Err(Outcome::Failure(Context::from_parser_kind(
                input,
                ParserKind::TakeWhileMN,
              )))
            };
            res
          }
        } else {
          let e = ParserKind::TakeWhileMN;
          Err(Outcome::Failure(Context::from_parser_kind(input, e)))
        }
      }
      None => {
        let len = input.input_len();
        if len >= n {
          match input.slice_index(n) {
            Ok(index) => Ok(input.take_split(index)),
            Err(_needed) => Err(Outcome::Failure(Context::from_parser_kind(
              input,
              ParserKind::TakeWhileMN,
            ))),
          }
        } else if len >= m && len <= n {
          let res: ParseResult<_, _, Context> = Ok((input.slice(len..), input));
          res
        } else {
          let e = ParserKind::TakeWhileMN;
          Err(Outcome::Failure(Context::from_parser_kind(input, e)))
        }
      }
    }
  }
}

/// Returns the longest input slice (if any) till a predicate is met.
///
/// The parser will return the longest slice till the given predicate *(a function that
/// takes the input and returns a bool)*.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::ParserKind, Needed, ParseResult};
/// use nom::bytes::complete::take_till;
///
/// fn till_colon(s: &str) -> ParseResult<&str, &str> {
///   take_till(|c| c == ':')(s)
/// }
///
/// assert_eq!(till_colon("latin:123"), Ok((":123", "latin")));
/// assert_eq!(till_colon(":empty matched"), Ok((":empty matched", ""))); //allowed
/// assert_eq!(till_colon("12345"), Ok(("", "12345")));
/// assert_eq!(till_colon(""), Ok(("", "")));
/// ```
pub fn take_till<F, Input, Context: ParseContext<Input>>(
  cond: F,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position_complete(|c| cond(c))
}

/// Returns the longest (at least 1) input slice till a predicate is met.
///
/// The parser will return the longest slice till the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// It will return `Err(Outcome::Failure((_, ParserKind::TakeTill1)))` if the input is empty or the
/// predicate matches the first input.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::complete::take_till1;
///
/// fn till_colon(s: &str) -> ParseResult<&str, &str> {
///   take_till1(|c| c == ':')(s)
/// }
///
/// assert_eq!(till_colon("latin:123"), Ok((":123", "latin")));
/// assert_eq!(till_colon(":empty matched"), Err(Outcome::Failure(Context::new(":empty matched", ParserKind::TakeTill1))));
/// assert_eq!(till_colon("12345"), Ok(("", "12345")));
/// assert_eq!(till_colon(""), Err(Outcome::Failure(Context::new("", ParserKind::TakeTill1))));
/// ```
pub fn take_till1<F, Input, Context: ParseContext<Input>>(
  cond: F,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ParserKind = ParserKind::TakeTill1;
    i.split_at_position1_complete(|c| cond(c), e)
  }
}

/// Returns an input slice containing the first N input elements (Input[..N]).
///
/// It will return `Err(Outcome::Failure((_, ParserKind::Eof)))` if the input is shorter than the argument.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::complete::take;
///
/// fn take6(s: &str) -> ParseResult<&str, &str> {
///   take(6usize)(s)
/// }
///
/// assert_eq!(take6("1234567"), Ok(("7", "123456")));
/// assert_eq!(take6("things"), Ok(("", "things")));
/// assert_eq!(take6("short"), Err(Outcome::Failure(Context::new("short", ParserKind::Eof))));
/// assert_eq!(take6(""), Err(Outcome::Failure(Context::new("", ParserKind::Eof))));
/// ```
pub fn take<C, Input, Context: ParseContext<Input>>(
  count: C,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputIter + InputTake,
  C: ToUsize,
{
  let c = count.to_usize();
  move |i: Input| match i.slice_index(c) {
    Err(_needed) => Err(Outcome::Failure(Context::from_parser_kind(
      i,
      ParserKind::Eof,
    ))),
    Ok(index) => Ok(i.take_split(index)),
  }
}

/// Returns the input slice up to the first occurrence of the pattern.
///
/// It doesn't consume the pattern. It will return `Err(Outcome::Failure((_, ParserKind::TakeUntil)))`
/// if the pattern wasn't met.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::complete::take_until;
///
/// fn until_eof(s: &str) -> ParseResult<&str, &str> {
///   take_until("eof")(s)
/// }
///
/// assert_eq!(until_eof("hello, worldeof"), Ok(("eof", "hello, world")));
/// assert_eq!(until_eof("hello, world"), Err(Outcome::Failure(Context::new("hello, world", ParserKind::TakeUntil))));
/// assert_eq!(until_eof(""), Err(Outcome::Failure(Context::new("", ParserKind::TakeUntil))));
/// assert_eq!(until_eof("1eof2eof"), Ok(("eof2eof", "1")));
/// ```
pub fn take_until<T, Input, Context: ParseContext<Input>>(
  tag: T,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTake + FindSubstring<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let t = tag.clone();
    let res: ParseResult<_, _, Context> = match i.find_substring(t) {
      None => Err(Outcome::Failure(Context::from_parser_kind(
        i,
        ParserKind::TakeUntil,
      ))),
      Some(index) => Ok(i.take_split(index)),
    };
    res
  }
}

/// Returns the non empty input slice up to the first occurrence of the pattern.
///
/// It doesn't consume the pattern. It will return `Err(Outcome::Failure((_, ParserKind::TakeUntil)))`
/// if the pattern wasn't met.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::complete::take_until1;
///
/// fn until_eof(s: &str) -> ParseResult<&str, &str> {
///   take_until1("eof")(s)
/// }
///
/// assert_eq!(until_eof("hello, worldeof"), Ok(("eof", "hello, world")));
/// assert_eq!(until_eof("hello, world"), Err(Outcome::Failure(Context::new("hello, world", ParserKind::TakeUntil))));
/// assert_eq!(until_eof(""), Err(Outcome::Failure(Context::new("", ParserKind::TakeUntil))));
/// assert_eq!(until_eof("1eof2eof"), Ok(("eof2eof", "1")));
/// assert_eq!(until_eof("eof"), Err(Outcome::Failure(Context::new("eof", ParserKind::TakeUntil))));
/// ```
pub fn take_until1<T, Input, Context: ParseContext<Input>>(
  tag: T,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTake + FindSubstring<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let t = tag.clone();
    let res: ParseResult<_, _, Context> = match i.find_substring(t) {
      None => Err(Outcome::Failure(Context::from_parser_kind(
        i,
        ParserKind::TakeUntil,
      ))),
      Some(0) => Err(Outcome::Failure(Context::from_parser_kind(
        i,
        ParserKind::TakeUntil,
      ))),
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
/// # use nom::{Outcome, error::ParserKind, Needed, ParseResult};
/// # use nom::character::complete::digit1;
/// use nom::bytes::complete::escaped;
/// use nom::character::complete::one_of;
///
/// fn esc(s: &str) -> ParseResult<&str, &str> {
///   escaped(digit1, '\\', one_of(r#""n\"#))(s)
/// }
///
/// assert_eq!(esc("123;"), Ok((";", "123")));
/// assert_eq!(esc(r#"12\"34;"#), Ok((";", r#"12\"34"#)));
/// ```
///
pub fn escaped<'a, Input: 'a, Context, F, G, O1, O2>(
  mut normal: F,
  control_char: char,
  mut escapable: G,
) -> impl FnMut(Input) -> ParseResult<Input, Input, Context>
where
  Input: Clone
    + crate::traits::Offset
    + InputLength
    + InputTake
    + InputTakeAtPosition
    + Slice<RangeFrom<usize>>
    + InputIter,
  <Input as InputIter>::Item: crate::traits::AsChar,
  F: Parser<Input, O1, Context>,
  G: Parser<Input, O2, Context>,
  Context: ParseContext<Input>,
{
  use crate::traits::AsChar;

  move |input: Input| {
    let mut i = input.clone();

    while i.input_len() > 0 {
      let current_len = i.input_len();

      match normal.parse(i.clone()) {
        Ok((i2, _)) => {
          // return if we consumed everything or if the normal parser
          // does not consume anything
          if i2.input_len() == 0 {
            return Ok((input.slice(input.input_len()..), input));
          } else if i2.input_len() == current_len {
            let index = input.offset(&i2);
            return Ok(input.take_split(index));
          } else {
            i = i2;
          }
        }
        Err(Outcome::Failure(_)) => {
          // unwrap() should be safe here since index < $i.input_len()
          if i.iter_elements().next().unwrap().as_char() == control_char {
            let next = control_char.len_utf8();
            if next >= i.input_len() {
              return Err(Outcome::Failure(Context::from_parser_kind(
                input,
                ParserKind::Escaped,
              )));
            } else {
              match escapable.parse(i.slice(next..)) {
                Ok((i2, _)) => {
                  if i2.input_len() == 0 {
                    return Ok((input.slice(input.input_len()..), input));
                  } else {
                    i = i2;
                  }
                }
                Err(e) => return Err(e),
              }
            }
          } else {
            let index = input.offset(&i);
            if index == 0 {
              return Err(Outcome::Failure(Context::from_parser_kind(
                input,
                ParserKind::Escaped,
              )));
            }
            return Ok(input.take_split(index));
          }
        }
        Err(e) => {
          return Err(e);
        }
      }
    }

    Ok((input.slice(input.input_len()..), input))
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
/// # use nom::{Outcome, error::ParserKind, Needed, ParseResult};
/// # use std::str::from_utf8;
/// use nom::bytes::complete::{escaped_transform, tag};
/// use nom::character::complete::alpha1;
/// use nom::branch::alt;
/// use nom::combinator::value;
///
/// fn parser(input: &str) -> ParseResult<&str, String> {
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
/// assert_eq!(parser("ab\\\"cd"), Ok(("", String::from("ab\"cd"))));
/// assert_eq!(parser("ab\\ncd"), Ok(("", String::from("ab\ncd"))));
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
pub fn escaped_transform<Input, Context, F, G, O1, O2, ExtendItem, Output>(
  mut normal: F,
  control_char: char,
  mut transform: G,
) -> impl FnMut(Input) -> ParseResult<Input, Output, Context>
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
  F: Parser<Input, O1, Context>,
  G: Parser<Input, O2, Context>,
  Context: ParseContext<Input>,
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
            return Ok((i.slice(i.input_len()..), res));
          } else if i2.input_len() == current_len {
            return Ok((remainder, res));
          } else {
            index = input.offset(&i2);
          }
        }
        Err(Outcome::Failure(_)) => {
          // unwrap() should be safe here since index < $i.input_len()
          if remainder.iter_elements().next().unwrap().as_char() == control_char {
            let next = index + control_char.len_utf8();
            let input_len = input.input_len();

            if next >= input_len {
              return Err(Outcome::Failure(Context::from_parser_kind(
                remainder,
                ParserKind::EscapedTransform,
              )));
            } else {
              match transform.parse(i.slice(next..)) {
                Ok((i2, o)) => {
                  o.extend_into(&mut res);
                  if i2.input_len() == 0 {
                    return Ok((i.slice(i.input_len()..), res));
                  } else {
                    index = input.offset(&i2);
                  }
                }
                Err(e) => return Err(e),
              }
            }
          } else {
            if index == 0 {
              return Err(Outcome::Failure(Context::from_parser_kind(
                remainder,
                ParserKind::EscapedTransform,
              )));
            }
            return Ok((remainder, res));
          }
        }
        Err(e) => return Err(e),
      }
    }
    Ok((input.slice(index..), res))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn complete_take_while_m_n_utf8_all_matching() {
    let result: ParseResult<&str, &str> =
      super::take_while_m_n(1, 4, |c: char| c.is_alphabetic())("øn");
    assert_eq!(result, Ok(("", "øn")));
  }

  #[test]
  fn complete_take_while_m_n_utf8_all_matching_substring() {
    let result: ParseResult<&str, &str> =
      super::take_while_m_n(1, 1, |c: char| c.is_alphabetic())("øn");
    assert_eq!(result, Ok(("n", "ø")));
  }

  // issue #1336 "escaped hangs if normal parser accepts empty"
  fn escaped_string(input: &str) -> ParseResult<&str, &str> {
    use crate::character::complete::{alpha0, one_of};
    escaped(alpha0, '\\', one_of("n"))(input)
  }

  // issue #1336 "escaped hangs if normal parser accepts empty"
  #[test]
  fn escaped_hang() {
    escaped_string("7").unwrap();
    escaped_string("a7").unwrap();
  }

  // issue ##1118 escaped does not work with empty string
  fn unquote<'a>(input: &'a str) -> ParseResult<&'a str, &'a str> {
    use crate::bytes::complete::*;
    use crate::character::complete::*;
    use crate::combinator::opt;
    use crate::sequence::delimited;

    delimited(
      char('"'),
      escaped(opt(none_of(r#"\""#)), '\\', one_of(r#"\"rnt"#)),
      char('"'),
    )(input)
  }

  #[test]
  fn escaped_hang_1118() {
    assert_eq!(unquote(r#""""#), Ok(("", "")));
  }
}
