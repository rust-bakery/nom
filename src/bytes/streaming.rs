//! Parsers recognizing bytes streams, streaming version

use crate::error::ParseContext;
use crate::error::ParserKind;
use crate::internal::{Needed, Outcome, ParseResult, Parser};
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
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::streaming::tag;
///
/// fn parser(s: &str) -> ParseResult<&str, &str> {
///   tag("Hello")(s)
/// }
///
/// assert_eq!(parser("Hello, World!"), Ok((", World!", "Hello")));
/// assert_eq!(parser("Something"), Err(Outcome::Failure(Context::new("Something", ParserKind::Tag))));
/// assert_eq!(parser("S"), Err(Outcome::Failure(Context::new("S", ParserKind::Tag))));
/// assert_eq!(parser("H"), Err(Outcome::Incomplete(Needed::new(4))));
/// ```
pub fn tag<T, Input, Context: ParseContext<Input>>(
  tag: T,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTake + InputLength + Compare<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let tag_len = tag.input_len();
    let t = tag.clone();

    let res: ParseResult<_, _, Context> = match i.compare(t) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      CompareResult::Incomplete => Err(Outcome::Incomplete(Needed::new(tag_len - i.input_len()))),
      CompareResult::Error => {
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
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::streaming::tag_no_case;
///
/// fn parser(s: &str) -> ParseResult<&str, &str> {
///   tag_no_case("hello")(s)
/// }
///
/// assert_eq!(parser("Hello, World!"), Ok((", World!", "Hello")));
/// assert_eq!(parser("hello, World!"), Ok((", World!", "hello")));
/// assert_eq!(parser("HeLlO, World!"), Ok((", World!", "HeLlO")));
/// assert_eq!(parser("Something"), Err(Outcome::Failure(Context::new("Something", ParserKind::Tag))));
/// assert_eq!(parser(""), Err(Outcome::Incomplete(Needed::new(5))));
/// ```
pub fn tag_no_case<T, Input, Context: ParseContext<Input>>(
  tag: T,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTake + InputLength + Compare<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let tag_len = tag.input_len();
    let t = tag.clone();

    let res: ParseResult<_, _, Context> = match (i).compare_no_case(t) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      CompareResult::Incomplete => Err(Outcome::Incomplete(Needed::new(tag_len - i.input_len()))),
      CompareResult::Error => {
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
/// It will return a `Outcome::Incomplete(Needed::new(1))` if the pattern wasn't met.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::ParserKind, Needed, ParseResult};
/// use nom::bytes::streaming::is_not;
///
/// fn not_space(s: &str) -> ParseResult<&str, &str> {
///   is_not(" \t\r\n")(s)
/// }
///
/// assert_eq!(not_space("Hello, World!"), Ok((" World!", "Hello,")));
/// assert_eq!(not_space("Sometimes\t"), Ok(("\t", "Sometimes")));
/// assert_eq!(not_space("Nospace"), Err(Outcome::Incomplete(Needed::new(1))));
/// assert_eq!(not_space(""), Err(Outcome::Incomplete(Needed::new(1))));
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
    i.split_at_position1(|c| arr.find_token(c), e)
  }
}

/// Returns the longest slice of the matches the pattern.
///
/// The parser will return the longest slice consisting of the characters in provided in the
/// combinator's argument.
///
/// # Streaming specific
/// *Streaming version* will return a `Outcome::Incomplete(Needed::new(1))` if the pattern wasn't met
/// or if the pattern reaches the end of the input.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::ParserKind, Needed, ParseResult};
/// use nom::bytes::streaming::is_a;
///
/// fn hex(s: &str) -> ParseResult<&str, &str> {
///   is_a("1234567890ABCDEF")(s)
/// }
///
/// assert_eq!(hex("123 and voila"), Ok((" and voila", "123")));
/// assert_eq!(hex("DEADBEEF and others"), Ok((" and others", "DEADBEEF")));
/// assert_eq!(hex("BADBABEsomething"), Ok(("something", "BADBABE")));
/// assert_eq!(hex("D15EA5E"), Err(Outcome::Incomplete(Needed::new(1))));
/// assert_eq!(hex(""), Err(Outcome::Incomplete(Needed::new(1))));
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
    i.split_at_position1(|c| !arr.find_token(c), e)
  }
}

/// Returns the longest input slice (if any) that matches the predicate.
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// # Streaming Specific
/// *Streaming version* will return a `Outcome::Incomplete(Needed::new(1))` if the pattern reaches the end of the input.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::ParserKind, Needed, ParseResult};
/// use nom::bytes::streaming::take_while;
/// use nom::character::is_alphabetic;
///
/// fn alpha(s: &[u8]) -> ParseResult<&[u8], &[u8]> {
///   take_while(is_alphabetic)(s)
/// }
///
/// assert_eq!(alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(alpha(b"12345"), Ok((&b"12345"[..], &b""[..])));
/// assert_eq!(alpha(b"latin"), Err(Outcome::Incomplete(Needed::new(1))));
/// assert_eq!(alpha(b""), Err(Outcome::Incomplete(Needed::new(1))));
/// ```
pub fn take_while<F, Input, Context: ParseContext<Input>>(
  cond: F,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
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
/// It will return an `Err(Outcome::Failure((_, ParserKind::TakeWhile1)))` if the pattern wasn't met.
///
/// # Streaming Specific
/// *Streaming version* will return a `Outcome::Incomplete(Needed::new(1))` or if the pattern reaches the end of the input.
///
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::streaming::take_while1;
/// use nom::character::is_alphabetic;
///
/// fn alpha(s: &[u8]) -> ParseResult<&[u8], &[u8]> {
///   take_while1(is_alphabetic)(s)
/// }
///
/// assert_eq!(alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(alpha(b"latin"), Err(Outcome::Incomplete(Needed::new(1))));
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
    i.split_at_position1(|c| !cond(c), e)
  }
}

/// Returns the longest (m <= len <= n) input slice  that matches the predicate.
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// It will return an `Outcome::Failure((_, ParserKind::TakeWhileMN))` if the pattern wasn't met.
/// # Streaming Specific
/// *Streaming version* will return a `Outcome::Incomplete(Needed::new(1))`  if the pattern reaches the end of the input or is too short.
///
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::streaming::take_while_m_n;
/// use nom::character::is_alphabetic;
///
/// fn short_alpha(s: &[u8]) -> ParseResult<&[u8], &[u8]> {
///   take_while_m_n(3, 6, is_alphabetic)(s)
/// }
///
/// assert_eq!(short_alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(short_alpha(b"lengthy"), Ok((&b"y"[..], &b"length"[..])));
/// assert_eq!(short_alpha(b"latin"), Err(Outcome::Incomplete(Needed::new(1))));
/// assert_eq!(short_alpha(b"ed"), Err(Outcome::Incomplete(Needed::new(1))));
/// assert_eq!(short_alpha(b"12345"), Err(Outcome::Failure(Context::new(&b"12345"[..], ParserKind::TakeWhileMN))));
/// ```
pub fn take_while_m_n<F, Input, Context: ParseContext<Input>>(
  m: usize,
  n: usize,
  cond: F,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
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
        } else {
          let needed = if m > len { m - len } else { 1 };
          Err(Outcome::Incomplete(Needed::new(needed)))
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
/// *Streaming version* will return a `Outcome::Incomplete(Needed::new(1))` if the match reaches the
/// end of input or if there was not match.
///
/// # Example
/// ```rust
/// # use nom::{Outcome, error::ParserKind, Needed, ParseResult};
/// use nom::bytes::streaming::take_till;
///
/// fn till_colon(s: &str) -> ParseResult<&str, &str> {
///   take_till(|c| c == ':')(s)
/// }
///
/// assert_eq!(till_colon("latin:123"), Ok((":123", "latin")));
/// assert_eq!(till_colon(":empty matched"), Ok((":empty matched", ""))); //allowed
/// assert_eq!(till_colon("12345"), Err(Outcome::Incomplete(Needed::new(1))));
/// assert_eq!(till_colon(""), Err(Outcome::Incomplete(Needed::new(1))));
/// ```
pub fn take_till<F, Input, Context: ParseContext<Input>>(
  cond: F,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
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
/// *Streaming version* will return a `Outcome::Incomplete(Needed::new(1))` if the match reaches the
/// end of input or if there was not match.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::streaming::take_till1;
///
/// fn till_colon(s: &str) -> ParseResult<&str, &str> {
///   take_till1(|c| c == ':')(s)
/// }
///
/// assert_eq!(till_colon("latin:123"), Ok((":123", "latin")));
/// assert_eq!(till_colon(":empty matched"), Err(Outcome::Failure(Context::new(":empty matched", ParserKind::TakeTill1))));
/// assert_eq!(till_colon("12345"), Err(Outcome::Incomplete(Needed::new(1))));
/// assert_eq!(till_colon(""), Err(Outcome::Incomplete(Needed::new(1))));
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
    i.split_at_position1(|c| cond(c), e)
  }
}

/// Returns an input slice containing the first N input elements (Input[..N]).
///
/// # Streaming Specific
/// *Streaming version* if the input has less than N elements, `take` will
/// return a `Outcome::Incomplete(Needed::new(M))` where M is the number of
/// additional bytes the parser would need to succeed.
/// It is well defined for `&[u8]` as the number of elements is the byte size,
/// but for types like `&str`, we cannot know how many bytes correspond for
/// the next few chars, so the result will be `Outcome::Incomplete(Needed::Unknown)`
///
/// # Example
/// ```rust
/// # use nom::{Outcome, error::ParserKind, Needed, ParseResult};
/// use nom::bytes::streaming::take;
///
/// fn take6(s: &str) -> ParseResult<&str, &str> {
///   take(6usize)(s)
/// }
///
/// assert_eq!(take6("1234567"), Ok(("7", "123456")));
/// assert_eq!(take6("things"), Ok(("", "things")));
/// assert_eq!(take6("short"), Err(Outcome::Incomplete(Needed::Unknown)));
/// ```
pub fn take<C, Input, Context: ParseContext<Input>>(
  count: C,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputIter + InputTake + InputLength,
  C: ToUsize,
{
  let c = count.to_usize();
  move |i: Input| match i.slice_index(c) {
    Err(i) => Err(Outcome::Incomplete(i)),
    Ok(index) => Ok(i.take_split(index)),
  }
}

/// Returns the input slice up to the first occurrence of the pattern.
///
/// It doesn't consume the pattern.
///
/// # Streaming Specific
/// *Streaming version* will return a `Outcome::Incomplete(Needed::new(N))` if the input doesn't
/// contain the pattern or if the input is smaller than the pattern.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::ParserKind, Needed, ParseResult};
/// use nom::bytes::streaming::take_until;
///
/// fn until_eof(s: &str) -> ParseResult<&str, &str> {
///   take_until("eof")(s)
/// }
///
/// assert_eq!(until_eof("hello, worldeof"), Ok(("eof", "hello, world")));
/// assert_eq!(until_eof("hello, world"), Err(Outcome::Incomplete(Needed::Unknown)));
/// assert_eq!(until_eof("hello, worldeo"), Err(Outcome::Incomplete(Needed::Unknown)));
/// assert_eq!(until_eof("1eof2eof"), Ok(("eof2eof", "1")));
/// ```
pub fn take_until<T, Input, Context: ParseContext<Input>>(
  tag: T,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTake + InputLength + FindSubstring<T>,
  T: Clone,
{
  move |i: Input| {
    let t = tag.clone();

    let res: ParseResult<_, _, Context> = match i.find_substring(t) {
      None => Err(Outcome::Incomplete(Needed::Unknown)),
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
/// *Streaming version* will return a `Outcome::Incomplete(Needed::new(N))` if the input doesn't
/// contain the pattern or if the input is smaller than the pattern.
/// # Example
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, Needed, ParseResult};
/// use nom::bytes::streaming::take_until1;
///
/// fn until_eof(s: &str) -> ParseResult<&str, &str> {
///   take_until1("eof")(s)
/// }
///
/// assert_eq!(until_eof("hello, worldeof"), Ok(("eof", "hello, world")));
/// assert_eq!(until_eof("hello, world"), Err(Outcome::Incomplete(Needed::Unknown)));
/// assert_eq!(until_eof("hello, worldeo"), Err(Outcome::Incomplete(Needed::Unknown)));
/// assert_eq!(until_eof("1eof2eof"), Ok(("eof2eof", "1")));
/// assert_eq!(until_eof("eof"),  Err(Outcome::Failure(Context::new("eof", ParserKind::TakeUntil))));
/// ```
pub fn take_until1<T, Input, Context: ParseContext<Input>>(
  tag: T,
) -> impl Fn(Input) -> ParseResult<Input, Input, Context>
where
  Input: InputTake + InputLength + FindSubstring<T>,
  T: Clone,
{
  move |i: Input| {
    let t = tag.clone();

    let res: ParseResult<_, _, Context> = match i.find_substring(t) {
      None => Err(Outcome::Incomplete(Needed::Unknown)),
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
/// use nom::bytes::streaming::escaped;
/// use nom::character::streaming::one_of;
///
/// fn esc(s: &str) -> ParseResult<&str, &str> {
///   escaped(digit1, '\\', one_of("\"n\\"))(s)
/// }
///
/// assert_eq!(esc("123;"), Ok((";", "123")));
/// assert_eq!(esc("12\\\"34;"), Ok((";", "12\\\"34")));
/// ```
///
pub fn escaped<Input, Context, F, G, O1, O2>(
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
          if i2.input_len() == 0 {
            return Err(Outcome::Incomplete(Needed::Unknown));
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
              return Err(Outcome::Incomplete(Needed::new(1)));
            } else {
              match escapable.parse(i.slice(next..)) {
                Ok((i2, _)) => {
                  if i2.input_len() == 0 {
                    return Err(Outcome::Incomplete(Needed::Unknown));
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

    Err(Outcome::Incomplete(Needed::Unknown))
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
/// use nom::bytes::streaming::{escaped_transform, tag};
/// use nom::character::streaming::alpha1;
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
/// assert_eq!(parser("ab\\\"cd\""), Ok(("\"", String::from("ab\"cd"))));
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
            return Err(Outcome::Incomplete(Needed::Unknown));
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
              return Err(Outcome::Incomplete(Needed::Unknown));
            } else {
              match transform.parse(i.slice(next..)) {
                Ok((i2, o)) => {
                  o.extend_into(&mut res);
                  if i2.input_len() == 0 {
                    return Err(Outcome::Incomplete(Needed::Unknown));
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
    Err(Outcome::Incomplete(Needed::Unknown))
  }
}
