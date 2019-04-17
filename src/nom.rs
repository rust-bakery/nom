//! Useful parser combinators
//!
//! A number of useful parser combinators have already been implemented.
//! Some of them use macros, other are implemented through functions.
//! Hopefully, the syntax will converge to onely one way in the future,
//! but the macros system makes no promises.
//!
#![allow(unused_imports)]

#[cfg(feature = "alloc")]
use lib::std::boxed::Box;

#[cfg(feature = "std")]
use lib::std::fmt::Debug;
use internal::*;
use error::ParseError;
use traits::{AsChar, InputIter, InputLength, InputTakeAtPosition};
use traits::{need_more, need_more_err, AtEof, ParseTo};
use lib::std::ops::{Range, RangeFrom, RangeTo};
use traits::{Compare, CompareResult, Offset, Slice};
use error::ErrorKind;
use lib::std::mem::transmute;

#[cfg(feature = "alloc")]
#[inline]
pub fn tag_cl<'a, 'b>(rec: &'a [u8]) -> Box<Fn(&'b [u8]) -> IResult<&'b [u8], &'b [u8]> + 'a> {
  Box::new(move |i: &'b [u8]| -> IResult<&'b [u8], &'b [u8]> {
    if i.len() >= rec.len() && &i[0..rec.len()] == rec {
      Ok((&i[rec.len()..], &i[0..rec.len()]))
    } else {
      let e: ErrorKind = ErrorKind::TagClosure;
      Err(Err::Error(error_position!(i, e)))
    }
  })
}

#[cfg(feature = "std")]
#[inline]
pub fn print<T: Debug>(input: T) -> IResult<T, ()> {
  println!("{:?}", input);
  Ok((input, ()))
}

#[inline]
pub fn begin(input: &[u8]) -> IResult<(), &[u8]> {
  Ok(((), input))
}

pub fn sized_buffer<'a, E: ParseError<&'a[u8]>>(input: &'a[u8]) -> IResult<&'a[u8], &'a[u8], E> {
  if input.is_empty() {
    return need_more(input, Needed::Unknown);
  }

  let len = input[0] as usize;

  if input.len() >= len + 1 {
    Ok((&input[len + 1..], &input[1..len + 1]))
  } else {
    need_more(input, Needed::Size(1 + len))
  }
}


/// Recognizes non empty buffers
#[inline]
pub fn non_empty<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputLength + AtEof,
{
  if input.input_len() == 0 {
    return need_more_err(input, Needed::Unknown, ErrorKind::NonEmpty);
  } else {
    Ok((input.slice(input.input_len()..), input))
  }
}

/// Return the remaining input.
#[inline]
pub fn rest<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputLength,
{
  Ok((input.slice(input.input_len()..), input))
}

/// Return the length of the remaining input.
#[inline]
pub fn rest_len<T, E: ParseError<T>>(input: T) -> IResult<T, usize, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputLength,
{
  let len = input.input_len();
  Ok((input, len))
}

/// Return the remaining input, for strings.
#[inline]
pub fn rest_s<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
  Ok((&input[input.len()..], input))
}

pub fn map<I, O1, O2, E: ParseError<I>, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(O1) -> O2,
{
  move |input: I| {
    let (input, o1) = first(input)?;
    Ok((input, second(o1)))
  }
}

pub fn map_res<I: Clone, O1, O2, E: ParseError<I>, E2, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(O1) -> Result<O2, E2>,
{
  move |input: I| {
    let i = input.clone();
    let (input, o1) = first(input)?;
    match second(o1) {
      Ok(o2) => Ok((input, o2)),
      Err(_) => Err(Err::Error(E::from_error_kind(i, ErrorKind::MapRes))),
    }
  }
}

pub fn opt<I:Clone, O, E: ParseError<I>, F>(f: F) -> impl Fn(I) -> IResult<I, Option<O>, E>
where
  F: Fn(I) -> IResult<I, O, E>,
{
  move |input: I| {
    let i = input.clone();
    match f(input) {
      Ok((i, o)) => Ok((i, Some(o))),
      Err(Err::Error(_)) => Ok((i, None)),
      Err(e) => Err(e),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Err, IResult, Needed};
  use error::ParseError;

  macro_rules! assert_parse(
    ($left: expr, $right: expr) => {
      let res: $crate::IResult<_, _, (_, ErrorKind)> = $left;
      assert_eq!(res, $right);
    };
  );

  #[test]
  #[cfg(feature = "alloc")]
  fn tag_closure() {
    let x = tag_cl(&b"abcd"[..]);
    let r = x(&b"abcdabcdefgh"[..]);
    assert_eq!(r, Ok((&b"abcdefgh"[..], &b"abcd"[..])));

    let r2 = x(&b"abcefgh"[..]);
    assert_eq!(
      r2,
      Err(Err::Error(error_position!(
        &b"abcefgh"[..],
        ErrorKind::TagClosure
      ),))
    );
  }

  #[test]
  #[cfg(feature = "alloc")]
  fn buffer_with_size() {
    use lib::std::vec::Vec;
    let i: Vec<u8> = vec![7, 8];
    let o: Vec<u8> = vec![4, 5, 6];
    //let arr:[u8; 6usize] = [3, 4, 5, 6, 7, 8];
    let arr: [u8; 6usize] = [3, 4, 5, 6, 7, 8];
    let res = sized_buffer::<(_, ErrorKind)>(&arr[..]);
    assert_eq!(res, Ok((&i[..], &o[..])))
  }

  /*#[test]
  fn t1() {
    let v1:Vec<u8> = vec![1,2,3];
    let v2:Vec<u8> = vec![4,5,6];
    let d = Ok((&v1[..], &v2[..]));
    let res = d.flat_map(print);
    assert_eq!(res, Ok((&v2[..], ())));
  }*/


  /*
    #[test]
    fn end_of_input() {
        let not_over = &b"Hello, world!"[..];
        let is_over = &b""[..];
        named!(eof_test, eof!());

        let res_not_over = eof_test(not_over);
        assert_eq!(res_not_over, Err(Err::Error(error_position!(not_over, ErrorKind::Eof))));

        let res_over = eof_test(is_over);
        assert_eq!(res_over, Ok((is_over, is_over)));
    }
    */

  #[test]
  fn rest_on_slices() {
    let input: &[u8] = &b"Hello, world!"[..];
    let empty: &[u8] = &b""[..];
    assert_parse!(rest(input), Ok((empty, input)));
  }

  #[test]
  fn rest_on_strs() {
    let input: &str = "Hello, world!";
    let empty: &str = "";
    assert_parse!(rest(input), Ok((empty, input)));
  }

  #[test]
  fn rest_len_on_slices() {
    let input: &[u8] = &b"Hello, world!"[..];
    assert_parse!(rest_len(input), Ok((input, input.len())));
  }

  use lib::std::convert::From;
  impl From<u32> for CustomError {
    fn from(_: u32) -> Self {
      CustomError
    }
  }

  impl<I> ParseError<I> for CustomError {
    fn from_error_kind(_: I, _: ErrorKind) -> Self {
      CustomError
    }

    fn append(_: I, _: ErrorKind, _: CustomError) -> Self {
      CustomError
    }
  }

  struct CustomError;
  #[allow(dead_code)]
  fn custom_error(input: &[u8]) -> IResult<&[u8], &[u8], CustomError> {
    //fix_error!(input, CustomError, alphanumeric)
    ::character::streaming::alphanumeric(input)
  }

  
}
