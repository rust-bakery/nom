//! Combinators applying parsers in sequence

#[cfg(test)]
mod tests;

use crate::error::ParseError;
use crate::internal::{IResult, Parser};

/// Gets an object from the first parser,
/// then gets another object from the second parser.
///
/// # Arguments
/// * `first` The first parser to apply.
/// * `second` The second parser to apply.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::sequence::pair;
/// use nom::bytes::complete::tag;
///
/// let mut parser = pair(tag("abc"), tag("efg"));
///
/// assert_eq!(parser("abcefg"), Ok(("", ("abc", "efg"))));
/// assert_eq!(parser("abcefghij"), Ok(("hij", ("abc", "efg"))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("123"), Err(Err::Error(("123", ErrorKind::Tag))));
/// ```
pub fn pair<I, O1, O2, E: ParseError<I>, F, G>(
  mut first: F,
  mut second: G,
) -> impl FnMut(I) -> IResult<I, (O1, O2), E>
where
  F: Parser<I, O1, E>,
  G: Parser<I, O2, E>,
{
  move |input: I| {
    let (input, o1) = first.parse(input)?;
    second.parse(input).map(|(i, o2)| (i, (o1, o2)))
  }
}

/// Matches an object from the first parser and discards it,
/// then gets an object from the second parser.
///
/// # Arguments
/// * `first` The opening parser.
/// * `second` The second parser to get object.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::sequence::preceded;
/// use nom::bytes::complete::tag;
///
/// let mut parser = preceded(tag("abc"), tag("efg"));
///
/// assert_eq!(parser("abcefg"), Ok(("", "efg")));
/// assert_eq!(parser("abcefghij"), Ok(("hij", "efg")));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("123"), Err(Err::Error(("123", ErrorKind::Tag))));
/// ```
pub fn preceded<I, O1, O2, E: ParseError<I>, F, G>(
  mut first: F,
  mut second: G,
) -> impl FnMut(I) -> IResult<I, O2, E>
where
  F: Parser<I, O1, E>,
  G: Parser<I, O2, E>,
{
  move |input: I| {
    let (input, _) = first.parse(input)?;
    second.parse(input)
  }
}

/// Gets an object from the first parser,
/// then matches an object from the second parser and discards it.
///
/// # Arguments
/// * `first` The first parser to apply.
/// * `second` The second parser to match an object.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::sequence::terminated;
/// use nom::bytes::complete::tag;
///
/// let mut parser = terminated(tag("abc"), tag("efg"));
///
/// assert_eq!(parser("abcefg"), Ok(("", "abc")));
/// assert_eq!(parser("abcefghij"), Ok(("hij", "abc")));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("123"), Err(Err::Error(("123", ErrorKind::Tag))));
/// ```
pub fn terminated<I, O1, O2, E: ParseError<I>, F, G>(
  mut first: F,
  mut second: G,
) -> impl FnMut(I) -> IResult<I, O1, E>
where
  F: Parser<I, O1, E>,
  G: Parser<I, O2, E>,
{
  move |input: I| {
    let (input, o1) = first.parse(input)?;
    second.parse(input).map(|(i, _)| (i, o1))
  }
}

/// Gets an object from the first parser,
/// then matches an object from the sep_parser and discards it,
/// then gets another object from the second parser.
///
/// # Arguments
/// * `first` The first parser to apply.
/// * `sep` The separator parser to apply.
/// * `second` The second parser to apply.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::sequence::separated_pair;
/// use nom::bytes::complete::tag;
///
/// let mut parser = separated_pair(tag("abc"), tag("|"), tag("efg"));
///
/// assert_eq!(parser("abc|efg"), Ok(("", ("abc", "efg"))));
/// assert_eq!(parser("abc|efghij"), Ok(("hij", ("abc", "efg"))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("123"), Err(Err::Error(("123", ErrorKind::Tag))));
/// ```
pub fn separated_pair<I, O1, O2, O3, E: ParseError<I>, F, G, H>(
  mut first: F,
  mut sep: G,
  mut second: H,
) -> impl FnMut(I) -> IResult<I, (O1, O3), E>
where
  F: Parser<I, O1, E>,
  G: Parser<I, O2, E>,
  H: Parser<I, O3, E>,
{
  move |input: I| {
    let (input, o1) = first.parse(input)?;
    let (input, _) = sep.parse(input)?;
    second.parse(input).map(|(i, o2)| (i, (o1, o2)))
  }
}

/// Matches an object from the first parser and discards it,
/// then gets an object from the second parser,
/// and finally matches an object from the third parser and discards it.
///
/// # Arguments
/// * `first` The first parser to apply and discard.
/// * `second` The second parser to apply.
/// * `third` The third parser to apply and discard.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::sequence::delimited;
/// use nom::bytes::complete::tag;
///
/// let mut parser = delimited(tag("("), tag("abc"), tag(")"));
///
/// assert_eq!(parser("(abc)"), Ok(("", "abc")));
/// assert_eq!(parser("(abc)def"), Ok(("def", "abc")));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("123"), Err(Err::Error(("123", ErrorKind::Tag))));
/// ```
pub fn delimited<I, O1, O2, O3, E: ParseError<I>, F, G, H>(
  mut first: F,
  mut second: G,
  mut third: H,
) -> impl FnMut(I) -> IResult<I, O2, E>
where
  F: Parser<I, O1, E>,
  G: Parser<I, O2, E>,
  H: Parser<I, O3, E>,
{
  move |input: I| {
    let (input, _) = first.parse(input)?;
    let (input, o2) = second.parse(input)?;
    third.parse(input).map(|(i, _)| (i, o2))
  }
}


