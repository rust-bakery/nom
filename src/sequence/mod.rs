#[macro_use]
mod macros;

use internal::IResult;
use error::ParseError;

pub fn pair<I, O1, O2, E: ParseError<I>, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, (O1, O2), E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  move |input: I| {
    let (input, o1) = first(input)?;
    second(input).map(|(i, o2)| (i, (o1, o2)))
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
pub fn pairc<I, O1, O2, E: ParseError<I>, F, G>(input: I, first: F, second: G) -> IResult<I, (O1, O2), E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  pair(first, second)(input)
}

pub fn preceded<I, O1, O2, E: ParseError<I>, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  move |input: I| {
    let (input, _) = first(input)?;
    second(input)
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
pub fn precededc<I, O1, O2, E: ParseError<I>, F, G>(input: I, first: F, second: G) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  preceded(first, second)(input)
}

pub fn terminated<I, O1, O2, E: ParseError<I>, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, O1, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  move |input: I| {
    let (input, o1) = first(input)?;
    second(input).map(|(i, _)| (i, o1))
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
pub fn terminatedc<I, O1, O2, E: ParseError<I>, F, G>(input: I, first: F, second: G) -> IResult<I, O1, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  terminated(first, second)(input)
}

pub fn separated_pair<I, O1, O2, O3, E: ParseError<I>, F, G, H>(first: F, sep: G, second: H) -> impl Fn(I) -> IResult<I, (O1, O3), E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  H: Fn(I) -> IResult<I, O3, E>,
{
  move |input: I| {
    let (input, o1) = first(input)?;
    let (input, _) = sep(input)?;
    second(input).map(|(i, o2)| (i, (o1, o2)))
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
pub fn separated_pairc<I, O1, O2, O3, E: ParseError<I>, F, G, H>(input: I, first: F, sep: G, second: H) -> IResult<I, (O1, O3), E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  H: Fn(I) -> IResult<I, O3, E>,
{
  separated_pair(first, sep, second)(input)
}

pub fn delimited<I, O1, O2, O3, E: ParseError<I>, F, G, H>(first: F, sep: G, second: H) -> impl Fn(I) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  H: Fn(I) -> IResult<I, O3, E>,
{
  move |input: I| {
    let (input, _) = first(input)?;
    let (input, o2) = sep(input)?;
    second(input).map(|(i, _)| (i, o2))
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
pub fn delimitedc<I, O1, O2, O3, E: ParseError<I>, F, G, H>(input: I, first: F, sep: G, second: H) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  H: Fn(I) -> IResult<I, O3, E>,
{
  delimited(first, sep, second)(input)
}
