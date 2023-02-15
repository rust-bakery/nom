//! Parsers recognizing numbers

use core::marker::PhantomData;

use crate::{
  branch::alt,
  character::{char, digit1},
  combinator::{cut, map, opt, recognize},
  error::{ErrorKind, ParseError},
  sequence::pair,
  AsBytes, AsChar, Compare, Emit, Input, Mode, Offset, OutputM, Parser,
};

pub mod complete;
pub mod streaming;

/// Configurable endianness
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Endianness {
  /// Big endian
  Big,
  /// Little endian
  Little,
  /// Will match the host's endianness
  Native,
}

/// Recognizes a floating point number in text format and returns the corresponding part of the input.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if it reaches the end of input.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::recognize_float;
///
/// let parser = |s| {
///   recognize_float(s)
/// };
///
/// assert_eq!(parser("11e-1;"), Ok((";", "11e-1")));
/// assert_eq!(parser("123E-02;"), Ok((";", "123E-02")));
/// assert_eq!(parser("123K-01"), Ok(("K-01", "123")));
/// assert_eq!(parser("abc"), Err(Err::Error(("abc", ErrorKind::Char))));
/// ```
#[rustfmt::skip]
pub fn recognize_float<T, E:ParseError<T>>() -> impl Parser<T, Output=T,Error= E>
where
  T: Clone + Offset,
  T: Input,
  <T as Input>::Item: AsChar,
{
  recognize((
      opt(alt((char('+'), char('-')))),
      alt((
        map((digit1(), opt(pair(char('.'), opt(digit1())))), |_| ()),
        map((char('.'), digit1()), |_| ())
      )),
      opt((
        alt((char('e'), char('E'))),
        opt(alt((char('+'), char('-')))),
        cut(digit1())
      ))
  ))
}

///todo
pub fn recognize_float_or_exceptions<T, E: ParseError<T>>() -> impl Parser<T, Output = T, Error = E>
where
  T: Clone + Offset,
  T: Input + Compare<&'static str>,
  <T as Input>::Item: AsChar,
{
  alt((
    recognize_float::<_, E>(),
    |i: T| {
      crate::bytes::streaming::tag_no_case::<_, _, E>("nan")(i.clone())
        .map_err(|_| crate::Err::Error(E::from_error_kind(i, ErrorKind::Float)))
    },
    |i: T| {
      crate::bytes::streaming::tag_no_case::<_, _, E>("inf")(i.clone())
        .map_err(|_| crate::Err::Error(E::from_error_kind(i, ErrorKind::Float)))
    },
    |i: T| {
      crate::bytes::streaming::tag_no_case::<_, _, E>("infinity")(i.clone())
        .map_err(|_| crate::Err::Error(E::from_error_kind(i, ErrorKind::Float)))
    },
  ))
}

/// TODO
pub fn double<T, E: ParseError<T>>() -> impl Parser<T, Output = f64, Error = E>
where
  T: Clone + Offset,
  T: Input + crate::traits::ParseTo<f64> + Compare<&'static str>,
  <T as Input>::Item: AsChar + Clone,
  T: AsBytes,
  T: for<'a> Compare<&'a [u8]>,
{
  Double { e: PhantomData }
}

/// TODO
pub struct Double<E> {
  e: PhantomData<E>,
}

impl<I, E: ParseError<I>> Parser<I> for Double<E>
where
  I: Clone + Offset,
  I: Input + crate::traits::ParseTo<f64> + Compare<&'static str>,
  <I as Input>::Item: AsChar + Clone,
  I: AsBytes,
  I: for<'a> Compare<&'a [u8]>,
{
  type Output = f64;
  type Error = E;

  fn process<OM: crate::OutputMode>(
    &mut self,
    input: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    let (i, s) =
      recognize_float_or_exceptions().process::<OutputM<Emit, OM::Error, OM::Incomplete>>(input)?;

    match s.parse_to() {
      Some(f) => Ok((i, OM::Output::bind(|| f))),
      None => Err(crate::Err::Error(OM::Error::bind(|| {
        E::from_error_kind(i, crate::error::ErrorKind::Float)
      }))),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::error::ErrorKind;
  use crate::internal::Err;
  use proptest::prelude::*;

  macro_rules! assert_parse(
    ($left: expr, $right: expr) => {
      let res: $crate::IResult<_, _, (_, ErrorKind)> = $left;
      assert_eq!(res, $right);
    };
  );

  #[test]
  #[cfg(feature = "std")]
  fn float_test() {
    let mut test_cases = vec![
      "+3.14",
      "3.14",
      "-3.14",
      "0",
      "0.0",
      "1.",
      ".789",
      "-.5",
      "1e7",
      "-1E-7",
      ".3e-2",
      "1.e4",
      "1.2e4",
      "12.34",
      "-1.234E-12",
      "-1.234e-12",
      "0.00000000000000000087",
    ];

    for test in test_cases.drain(..) {
      let expected32 = str::parse::<f32>(test).unwrap();
      let expected64 = str::parse::<f64>(test).unwrap();

      println!("now parsing: {} -> {}", test, expected32);

      assert_parse!(recognize_float().parse_complete(test), Ok(("", test)));

      /*assert_parse!(float(test.as_bytes()), Ok((&b""[..], expected32)));
      assert_parse!(float(test), Ok(("", expected32)));
      */

      assert_parse!(
        double().parse_complete(test.as_bytes()),
        Ok((&b""[..], expected64))
      );
      assert_parse!(double().parse_complete(test), Ok(("", expected64)));
    }

    let remaining_exponent = "-1.234E-";
    assert_parse!(
      recognize_float().parse_complete(remaining_exponent),
      Err(Err::Failure(("", ErrorKind::Digit)))
    );

    /*let (_i, nan) = float::<_, ()>("NaN").unwrap();
    assert!(nan.is_nan());

    let (_i, inf) = float::<_, ()>("inf").unwrap();
    assert!(inf.is_infinite());
    let (_i, inf) = float::<_, ()>("infinite").unwrap();
    assert!(inf.is_infinite());*/
  }
}
