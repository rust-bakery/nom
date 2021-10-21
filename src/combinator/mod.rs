//! General purpose combinators

#![allow(unused_imports)]

#[cfg(feature = "alloc")]
use crate::lib::std::boxed::Box;

use crate::error::{FromExternalError, ParseContext, ParserKind};
use crate::internal::*;
use crate::lib::std::borrow::Borrow;
use crate::lib::std::convert::Into;
#[cfg(feature = "std")]
use crate::lib::std::fmt::Debug;
use crate::lib::std::mem::transmute;
use crate::lib::std::ops::{Range, RangeFrom, RangeTo};
use crate::traits::{AsChar, InputIter, InputLength, InputTakeAtPosition, ParseTo};
use crate::traits::{Compare, CompareResult, Offset, Slice};

#[cfg(test)]
mod tests;

/// Return the remaining input.
///
/// ```rust
/// # use nom::error::ParserKind;
/// use nom::combinator::rest;
/// assert_eq!(rest::<_,(_, ParserKind)>("abc"), Ok(("", "abc")));
/// assert_eq!(rest::<_,(_, ParserKind)>(""), Ok(("", "")));
/// ```
#[inline]
pub fn rest<T, E: ParseContext<T>>(input: T) -> ParseResult<T, T, E>
where
  T: Slice<RangeFrom<usize>>,
  T: InputLength,
{
  Ok((input.slice(input.input_len()..), input))
}

/// Return the length of the remaining input.
///
/// ```rust
/// # use nom::error::ParserKind;
/// use nom::combinator::rest_len;
/// assert_eq!(rest_len::<_,(_, ParserKind)>("abc"), Ok(("abc", 3)));
/// assert_eq!(rest_len::<_,(_, ParserKind)>(""), Ok(("", 0)));
/// ```
#[inline]
pub fn rest_len<T, E: ParseContext<T>>(input: T) -> ParseResult<T, usize, E>
where
  T: InputLength,
{
  let len = input.input_len();
  Ok((input, len))
}

/// Maps a function on the result of a parser.
///
/// ```rust
/// use nom::{Outcome,error::ParserKind, ParseResult,Parser};
/// use nom::character::complete::digit1;
/// use nom::combinator::map;
/// # fn main() {
///
/// let mut parser = map(digit1, |s: &str| s.len());
///
/// // the parser will count how many characters were returned by digit1
/// assert_eq!(parser.parse("123456"), Ok(("", 6)));
///
/// // this will fail if digit1 fails
/// assert_eq!(parser.parse("abc"), Err(Outcome::Failure(("abc", ParserKind::Digit))));
/// # }
/// ```
pub fn map<I, O1, O2, E, F, G>(mut parser: F, mut f: G) -> impl FnMut(I) -> ParseResult<I, O2, E>
where
  F: Parser<I, O1, E>,
  G: FnMut(O1) -> O2,
{
  move |input: I| {
    let (input, o1) = parser.parse(input)?;
    Ok((input, f(o1)))
  }
}

/// Applies a function returning a `Result` over the result of a parser.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::character::complete::digit1;
/// use nom::combinator::map_res;
/// # fn main() {
///
/// let mut parse = map_res(digit1, |s: &str| s.parse::<u8>());
///
/// // the parser will convert the result of digit1 to a number
/// assert_eq!(parse("123"), Ok(("", 123)));
///
/// // this will fail if digit1 fails
/// assert_eq!(parse("abc"), Err(Outcome::Failure(("abc", ParserKind::Digit))));
///
/// // this will fail if the mapped function fails (a `u8` is too small to hold `123456`)
/// assert_eq!(parse("123456"), Err(Outcome::Failure(("123456", ParserKind::MapRes))));
/// # }
/// ```
pub fn map_res<I: Clone, O1, O2, E: FromExternalError<I, E2>, E2, F, G>(
  mut parser: F,
  mut f: G,
) -> impl FnMut(I) -> ParseResult<I, O2, E>
where
  F: Parser<I, O1, E>,
  G: FnMut(O1) -> Result<O2, E2>,
{
  move |input: I| {
    let i = input.clone();
    let (input, o1) = parser.parse(input)?;
    match f(o1) {
      Ok(o2) => Ok((input, o2)),
      Err(e) => Err(Outcome::Failure(E::from_external_error(
        i,
        ParserKind::MapRes,
        e,
      ))),
    }
  }
}

/// Applies a function returning an `Option` over the result of a parser.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::character::complete::digit1;
/// use nom::combinator::map_opt;
/// # fn main() {
///
/// let mut parse = map_opt(digit1, |s: &str| s.parse::<u8>().ok());
///
/// // the parser will convert the result of digit1 to a number
/// assert_eq!(parse("123"), Ok(("", 123)));
///
/// // this will fail if digit1 fails
/// assert_eq!(parse("abc"), Err(Outcome::Failure(("abc", ParserKind::Digit))));
///
/// // this will fail if the mapped function fails (a `u8` is too small to hold `123456`)
/// assert_eq!(parse("123456"), Err(Outcome::Failure(("123456", ParserKind::MapOpt))));
/// # }
/// ```
pub fn map_opt<I: Clone, O1, O2, E: ParseContext<I>, F, G>(
  mut parser: F,
  mut f: G,
) -> impl FnMut(I) -> ParseResult<I, O2, E>
where
  F: Parser<I, O1, E>,
  G: FnMut(O1) -> Option<O2>,
{
  move |input: I| {
    let i = input.clone();
    let (input, o1) = parser.parse(input)?;
    match f(o1) {
      Some(o2) => Ok((input, o2)),
      None => Err(Outcome::Failure(E::from_parser_kind(i, ParserKind::MapOpt))),
    }
  }
}

/// Applies a parser over the result of another one.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::character::complete::digit1;
/// use nom::bytes::complete::take;
/// use nom::combinator::map_parser;
/// # fn main() {
///
/// let mut parse = map_parser(take(5u8), digit1);
///
/// assert_eq!(parse("12345"), Ok(("", "12345")));
/// assert_eq!(parse("123ab"), Ok(("", "123")));
/// assert_eq!(parse("123"), Err(Outcome::Failure(("123", ParserKind::Eof))));
/// # }
/// ```
pub fn map_parser<I, O1, O2, E: ParseContext<I>, F, G>(
  mut parser: F,
  mut applied_parser: G,
) -> impl FnMut(I) -> ParseResult<I, O2, E>
where
  F: Parser<I, O1, E>,
  G: Parser<O1, O2, E>,
{
  move |input: I| {
    let (input, o1) = parser.parse(input)?;
    let (_, o2) = applied_parser.parse(o1)?;
    Ok((input, o2))
  }
}

/// Creates a new parser from the output of the first parser, then apply that parser over the rest of the input.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::bytes::complete::take;
/// use nom::number::complete::u8;
/// use nom::combinator::flat_map;
/// # fn main() {
///
/// let mut parse = flat_map(u8, take);
///
/// assert_eq!(parse(&[2, 0, 1, 2][..]), Ok((&[2][..], &[0, 1][..])));
/// assert_eq!(parse(&[4, 0, 1, 2][..]), Err(Outcome::Failure((&[0, 1, 2][..], ParserKind::Eof))));
/// # }
/// ```
pub fn flat_map<I, O1, O2, E: ParseContext<I>, F, G, H>(
  mut parser: F,
  applied_parser: G,
) -> impl FnMut(I) -> ParseResult<I, O2, E>
where
  F: Parser<I, O1, E>,
  G: Fn(O1) -> H,
  H: Parser<I, O2, E>,
{
  move |input: I| {
    let (input, o1) = parser.parse(input)?;
    applied_parser(o1).parse(input)
  }
}

/// Optional parser: Will return `None` if not successful.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::combinator::opt;
/// use nom::character::complete::alpha1;
/// # fn main() {
///
/// fn parser(i: &str) -> ParseResult<&str, Option<&str>> {
///   opt(alpha1)(i)
/// }
///
/// assert_eq!(parser("abcd;"), Ok((";", Some("abcd"))));
/// assert_eq!(parser("123;"), Ok(("123;", None)));
/// # }
/// ```
pub fn opt<I: Clone, O, E: ParseContext<I>, F>(
  mut f: F,
) -> impl FnMut(I) -> ParseResult<I, Option<O>, E>
where
  F: Parser<I, O, E>,
{
  move |input: I| {
    let i = input.clone();
    match f.parse(input) {
      Ok((i, o)) => Ok((i, Some(o))),
      Err(Outcome::Failure(_)) => Ok((i, None)),
      Err(e) => Err(e),
    }
  }
}

/// Calls the parser if the condition is met.
///
/// ```rust
/// # use nom::{Outcome, error::{Context, ParserKind}, ParseResult};
/// use nom::combinator::cond;
/// use nom::character::complete::alpha1;
/// # fn main() {
///
/// fn parser(b: bool, i: &str) -> ParseResult<&str, Option<&str>> {
///   cond(b, alpha1)(i)
/// }
///
/// assert_eq!(parser(true, "abcd;"), Ok((";", Some("abcd"))));
/// assert_eq!(parser(false, "abcd;"), Ok(("abcd;", None)));
/// assert_eq!(parser(true, "123;"), Err(Outcome::Failure(Context::new("123;", ParserKind::Alpha))));
/// assert_eq!(parser(false, "123;"), Ok(("123;", None)));
/// # }
/// ```
pub fn cond<I, O, E: ParseContext<I>, F>(
  b: bool,
  mut f: F,
) -> impl FnMut(I) -> ParseResult<I, Option<O>, E>
where
  F: Parser<I, O, E>,
{
  move |input: I| {
    if b {
      match f.parse(input) {
        Ok((i, o)) => Ok((i, Some(o))),
        Err(e) => Err(e),
      }
    } else {
      Ok((input, None))
    }
  }
}

/// Tries to apply its parser without consuming the input.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::combinator::peek;
/// use nom::character::complete::alpha1;
/// # fn main() {
///
/// let mut parser = peek(alpha1);
///
/// assert_eq!(parser("abcd;"), Ok(("abcd;", "abcd")));
/// assert_eq!(parser("123;"), Err(Outcome::Failure(("123;", ParserKind::Alpha))));
/// # }
/// ```
pub fn peek<I: Clone, O, E: ParseContext<I>, F>(mut f: F) -> impl FnMut(I) -> ParseResult<I, O, E>
where
  F: Parser<I, O, E>,
{
  move |input: I| {
    let i = input.clone();
    match f.parse(input) {
      Ok((_, o)) => Ok((i, o)),
      Err(e) => Err(e),
    }
  }
}

/// returns its input if it is at the end of input data
///
/// When we're at the end of the data, this combinator
/// will succeed
///
/// ```
/// # use std::str;
/// # use nom::{Outcome, error::ParserKind, ParseResult};
/// # use nom::combinator::eof;
///
/// # fn main() {
/// let parser = eof;
/// assert_eq!(parser("abc"), Err(Outcome::Failure(("abc", ParserKind::Eof))));
/// assert_eq!(parser(""), Ok(("", "")));
/// # }
/// ```
pub fn eof<I: InputLength + Clone, E: ParseContext<I>>(input: I) -> ParseResult<I, I, E> {
  if input.input_len() == 0 {
    let clone = input.clone();
    Ok((input, clone))
  } else {
    Err(Outcome::Failure(E::from_parser_kind(
      input,
      ParserKind::Eof,
    )))
  }
}

/// Transforms Incomplete into `Error`.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::bytes::streaming::take;
/// use nom::combinator::complete;
/// # fn main() {
///
/// let mut parser = complete(take(5u8));
///
/// assert_eq!(parser("abcdefg"), Ok(("fg", "abcde")));
/// assert_eq!(parser("abcd"), Err(Outcome::Failure(("abcd", ParserKind::Complete))));
/// # }
/// ```
pub fn complete<I: Clone, O, E: ParseContext<I>, F>(
  mut f: F,
) -> impl FnMut(I) -> ParseResult<I, O, E>
where
  F: Parser<I, O, E>,
{
  move |input: I| {
    let i = input.clone();
    match f.parse(input) {
      Err(Outcome::Incomplete(_)) => Err(Outcome::Failure(E::from_parser_kind(
        i,
        ParserKind::Complete,
      ))),
      rest => rest,
    }
  }
}

/// Succeeds if all the input has been consumed by its child parser.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::combinator::all_consuming;
/// use nom::character::complete::alpha1;
/// # fn main() {
///
/// let mut parser = all_consuming(alpha1);
///
/// assert_eq!(parser("abcd"), Ok(("", "abcd")));
/// assert_eq!(parser("abcd;"),Err(Outcome::Failure((";", ParserKind::Eof))));
/// assert_eq!(parser("123abcd;"),Err(Outcome::Failure(("123abcd;", ParserKind::Alpha))));
/// # }
/// ```
pub fn all_consuming<I, O, E: ParseContext<I>, F>(mut f: F) -> impl FnMut(I) -> ParseResult<I, O, E>
where
  I: InputLength,
  F: Parser<I, O, E>,
{
  move |input: I| {
    let (input, res) = f.parse(input)?;
    if input.input_len() == 0 {
      Ok((input, res))
    } else {
      Err(Outcome::Failure(E::from_parser_kind(
        input,
        ParserKind::Eof,
      )))
    }
  }
}

/// Returns the result of the child parser if it satisfies a verification function.
///
/// The verification function takes as argument a reference to the output of the
/// parser.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::combinator::verify;
/// use nom::character::complete::alpha1;
/// # fn main() {
///
/// let mut parser = verify(alpha1, |s: &str| s.len() == 4);
///
/// assert_eq!(parser("abcd"), Ok(("", "abcd")));
/// assert_eq!(parser("abcde"), Err(Outcome::Failure(("abcde", ParserKind::Verify))));
/// assert_eq!(parser("123abcd;"),Err(Outcome::Failure(("123abcd;", ParserKind::Alpha))));
/// # }
/// ```
pub fn verify<I: Clone, O1, O2, E: ParseContext<I>, F, G>(
  mut first: F,
  second: G,
) -> impl FnMut(I) -> ParseResult<I, O1, E>
where
  F: Parser<I, O1, E>,
  G: Fn(&O2) -> bool,
  O1: Borrow<O2>,
  O2: ?Sized,
{
  move |input: I| {
    let i = input.clone();
    let (input, o) = first.parse(input)?;

    if second(o.borrow()) {
      Ok((input, o))
    } else {
      Err(Outcome::Failure(E::from_parser_kind(i, ParserKind::Verify)))
    }
  }
}

/// Returns the provided value if the child parser succeeds.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::combinator::value;
/// use nom::character::complete::alpha1;
/// # fn main() {
///
/// let mut parser = value(1234, alpha1);
///
/// assert_eq!(parser("abcd"), Ok(("", 1234)));
/// assert_eq!(parser("123abcd;"), Err(Outcome::Failure(("123abcd;", ParserKind::Alpha))));
/// # }
/// ```
pub fn value<I, O1: Clone, O2, E: ParseContext<I>, F>(
  val: O1,
  mut parser: F,
) -> impl FnMut(I) -> ParseResult<I, O1, E>
where
  F: Parser<I, O2, E>,
{
  move |input: I| parser.parse(input).map(|(i, _)| (i, val.clone()))
}

/// Succeeds if the child parser returns an error.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::combinator::not;
/// use nom::character::complete::alpha1;
/// # fn main() {
///
/// let mut parser = not(alpha1);
///
/// assert_eq!(parser("123"), Ok(("123", ())));
/// assert_eq!(parser("abcd"), Err(Outcome::Failure(("abcd", ParserKind::Not))));
/// # }
/// ```
pub fn not<I: Clone, O, E: ParseContext<I>, F>(
  mut parser: F,
) -> impl FnMut(I) -> ParseResult<I, (), E>
where
  F: Parser<I, O, E>,
{
  move |input: I| {
    let i = input.clone();
    match parser.parse(input) {
      Ok(_) => Err(Outcome::Failure(E::from_parser_kind(i, ParserKind::Not))),
      Err(Outcome::Failure(_)) => Ok((i, ())),
      Err(e) => Err(e),
    }
  }
}

/// If the child parser was successful, return the consumed input as produced value.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::combinator::recognize;
/// use nom::character::complete::{char, alpha1};
/// use nom::sequence::separated_pair;
/// # fn main() {
///
/// let mut parser = recognize(separated_pair(alpha1, char(','), alpha1));
///
/// assert_eq!(parser("abcd,efgh"), Ok(("", "abcd,efgh")));
/// assert_eq!(parser("abcd;"),Err(Outcome::Failure((";", ParserKind::Char))));
/// # }
/// ```
pub fn recognize<I: Clone + Offset + Slice<RangeTo<usize>>, O, E: ParseContext<I>, F>(
  mut parser: F,
) -> impl FnMut(I) -> ParseResult<I, I, E>
where
  F: Parser<I, O, E>,
{
  move |input: I| {
    let i = input.clone();
    match parser.parse(i) {
      Ok((i, _)) => {
        let index = input.offset(&i);
        Ok((i, input.slice(..index)))
      }
      Err(e) => Err(e),
    }
  }
}

/// if the child parser was successful, return the consumed input with the output
/// as a tuple. Functions similarly to [recognize](fn.recognize.html) except it
/// returns the parser output as well.
///
/// This can be useful especially in cases where the output is not the same type
/// as the input, or the input is a user defined type.
///
/// Returned tuple is of the format `(consumed input, produced output)`.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::combinator::{consumed, value, recognize, map};
/// use nom::character::complete::{char, alpha1};
/// use nom::bytes::complete::tag;
/// use nom::sequence::separated_pair;
///
/// fn inner_parser(input: &str) -> ParseResult<&str, bool> {
///     value(true, tag("1234"))(input)
/// }
///
/// # fn main() {
///
/// let mut consumed_parser = consumed(value(true, separated_pair(alpha1, char(','), alpha1)));
///
/// assert_eq!(consumed_parser("abcd,efgh1"), Ok(("1", ("abcd,efgh", true))));
/// assert_eq!(consumed_parser("abcd;"),Err(Outcome::Failure((";", ParserKind::Char))));
///
///
/// // the first output (representing the consumed input)
/// // should be the same as that of the `recognize` parser.
/// let mut recognize_parser = recognize(inner_parser);
/// let mut consumed_parser = map(consumed(inner_parser), |(consumed, output)| consumed);
///
/// assert_eq!(recognize_parser("1234"), consumed_parser("1234"));
/// assert_eq!(recognize_parser("abcd"), consumed_parser("abcd"));
/// # }
/// ```
pub fn consumed<I, O, F, E>(mut parser: F) -> impl FnMut(I) -> ParseResult<I, (I, O), E>
where
  I: Clone + Offset + Slice<RangeTo<usize>>,
  E: ParseContext<I>,
  F: Parser<I, O, E>,
{
  move |input: I| {
    let i = input.clone();
    match parser.parse(i) {
      Ok((remaining, result)) => {
        let index = input.offset(&remaining);
        let consumed = input.slice(..index);
        Ok((remaining, (consumed, result)))
      }
      Err(e) => Err(e),
    }
  }
}

/// transforms an error to failure
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::combinator::cut;
/// use nom::character::complete::alpha1;
/// # fn main() {
///
/// let mut parser = cut(alpha1);
///
/// assert_eq!(parser("abcd;"), Ok((";", "abcd")));
/// assert_eq!(parser("123;"), Err(Outcome::Invalid(("123;", ParserKind::Alpha))));
/// # }
/// ```
pub fn cut<I, O, E: ParseContext<I>, F>(mut parser: F) -> impl FnMut(I) -> ParseResult<I, O, E>
where
  F: Parser<I, O, E>,
{
  move |input: I| match parser.parse(input) {
    Err(Outcome::Failure(e)) => Err(Outcome::Invalid(e)),
    rest => rest,
  }
}

/// automatically converts the child parser's result to another type
///
/// it will be able to convert the output value and the error value
/// as long as the `Into` implementations are available
///
/// ```rust
/// # use nom::ParseResult;
/// use nom::combinator::into;
/// use nom::character::complete::alpha1;
/// # fn main() {
///
///  fn parser1(i: &str) -> ParseResult<&str, &str> {
///    alpha1(i)
///  }
///
///  let mut parser2 = into(parser1);
///
/// // the parser converts the &str output of the child parser into a Vec<u8>
/// let bytes: ParseResult<&str, Vec<u8>> = parser2("abcd");
/// assert_eq!(bytes, Ok(("", vec![97, 98, 99, 100])));
/// # }
/// ```
pub fn into<I, O1, O2, E1, E2, F>(mut parser: F) -> impl FnMut(I) -> ParseResult<I, O2, E2>
where
  O1: Into<O2>,
  E1: Into<E2>,
  E1: ParseContext<I>,
  E2: ParseContext<I>,
  F: Parser<I, O1, E1>,
{
  //map(parser, Into::into)
  move |input: I| match parser.parse(input) {
    Ok((i, o)) => Ok((i, o.into())),
    Err(Outcome::Failure(e)) => Err(Outcome::Failure(e.into())),
    Err(Outcome::Invalid(e)) => Err(Outcome::Invalid(e.into())),
    Err(Outcome::Incomplete(e)) => Err(Outcome::Incomplete(e)),
  }
}

/// Creates an iterator from input data and a parser.
///
/// Call the iterator's [ParserIterator::finish] method to get the remaining input if successful,
/// or the error value if we encountered an error.
///
/// ```rust
/// use nom::{combinator::iterator, ParseResult, bytes::complete::tag, character::complete::alpha1, sequence::terminated};
/// use std::collections::HashMap;
///
/// let data = "abc|defg|hijkl|mnopqr|123";
/// let mut it = iterator(data, terminated(alpha1, tag("|")));
///
/// let parsed = it.map(|v| (v, v.len())).collect::<HashMap<_,_>>();
/// let res: ParseResult<_,_> = it.finish();
///
/// assert_eq!(parsed, [("abc", 3usize), ("defg", 4), ("hijkl", 5), ("mnopqr", 6)].iter().cloned().collect());
/// assert_eq!(res, Ok(("123", ())));
/// ```
pub fn iterator<Input, Output, Context, F>(input: Input, f: F) -> ParserIterator<Input, Context, F>
where
  F: Parser<Input, Output, Context>,
  Context: ParseContext<Input>,
{
  ParserIterator {
    iterator: f,
    input,
    state: Some(State::Running),
  }
}

/// Main structure associated to the [iterator] function.
pub struct ParserIterator<I, E, F> {
  iterator: F,
  input: I,
  state: Option<State<E>>,
}

impl<I: Clone, E, F> ParserIterator<I, E, F> {
  /// Returns the remaining input if parsing was successful, or the error if we encountered an error.
  pub fn finish(mut self) -> ParseResult<I, (), E> {
    match self.state.take().unwrap() {
      State::Running | State::Done => Ok((self.input, ())),
      State::Failure(e) => Err(Outcome::Invalid(e)),
      State::Incomplete(i) => Err(Outcome::Incomplete(i)),
    }
  }
}

impl<'a, Input, Output, Context, F> core::iter::Iterator
  for &'a mut ParserIterator<Input, Context, F>
where
  F: FnMut(Input) -> ParseResult<Input, Output, Context>,
  Input: Clone,
{
  type Item = Output;

  fn next(&mut self) -> Option<Self::Item> {
    if let State::Running = self.state.take().unwrap() {
      let input = self.input.clone();

      match (self.iterator)(input) {
        Ok((i, o)) => {
          self.input = i;
          self.state = Some(State::Running);
          Some(o)
        }
        Err(Outcome::Failure(_)) => {
          self.state = Some(State::Done);
          None
        }
        Err(Outcome::Invalid(e)) => {
          self.state = Some(State::Failure(e));
          None
        }
        Err(Outcome::Incomplete(i)) => {
          self.state = Some(State::Incomplete(i));
          None
        }
      }
    } else {
      None
    }
  }
}

enum State<E> {
  Running,
  Done,
  Failure(E),
  Incomplete(Needed),
}

/// a parser which always succeeds with given value without consuming any input.
///
/// It can be used for example as the last alternative in `alt` to
/// specify the default case.
///
/// ```rust
/// # use nom::{Outcome,error::ParserKind, ParseResult};
/// use nom::branch::alt;
/// use nom::combinator::{success, value};
/// use nom::character::complete::char;
/// # fn main() {
///
/// let mut parser = success::<_,_,(_,ParserKind)>(10);
/// assert_eq!(parser("xyz"), Ok(("xyz", 10)));
///
/// let mut sign = alt((value(-1, char('-')), value(1, char('+')), success::<_,_,(_,ParserKind)>(1)));
/// assert_eq!(sign("+10"), Ok(("10", 1)));
/// assert_eq!(sign("-10"), Ok(("10", -1)));
/// assert_eq!(sign("10"), Ok(("10", 1)));
/// # }
/// ```
pub fn success<I, O: Clone, E: ParseContext<I>>(val: O) -> impl Fn(I) -> ParseResult<I, O, E> {
  move |input: I| Ok((input, val.clone()))
}

/// A parser which always fails.
///
/// ```rust
/// # use nom::{Outcome, error::ParserKind, ParseResult};
/// use nom::combinator::fail;
///
/// let s = "string";
/// assert_eq!(fail::<_, &str, _>(s), Err(Outcome::Failure((s, ParserKind::Fail))));
/// ```
pub fn fail<I, O, E: ParseContext<I>>(i: I) -> ParseResult<I, O, E> {
  Err(Outcome::Failure(E::from_parser_kind(i, ParserKind::Fail)))
}
