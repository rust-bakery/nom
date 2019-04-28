//! general purpose combinators

#![allow(unused_imports)]

#[cfg(feature = "alloc")]
use lib::std::boxed::Box;

#[cfg(feature = "std")]
use lib::std::fmt::Debug;
use internal::*;
use error::ParseError;
use traits::{AsChar, InputIter, InputLength, InputTakeAtPosition};
use traits::{need_more, need_more_err, ParseTo};
use lib::std::ops::{Range, RangeFrom, RangeTo};
use traits::{Compare, CompareResult, Offset, Slice};
use error::ErrorKind;
use lib::std::mem::transmute;

#[macro_use]
mod macros;

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
  T: InputLength,
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

#[doc(hidden)]
pub fn mapc<I, O1, O2, E: ParseError<I>, F, G>(input: I, first: F, second: G) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(O1) -> O2,
{
  map(first, second)(input)
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

#[doc(hidden)]
pub fn map_resc<I: Clone, O1, O2, E: ParseError<I>, E2, F, G>(input: I, first: F, second: G) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(O1) -> Result<O2, E2>,
{
  map_res(first, second)(input)
}

pub fn map_opt<I: Clone, O1, O2, E: ParseError<I>, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(O1) -> Option<O2>,
{
  move |input: I| {
    let i = input.clone();
    let (input, o1) = first(input)?;
    match second(o1) {
      Some(o2) => Ok((input, o2)),
      None => Err(Err::Error(E::from_error_kind(i, ErrorKind::MapOpt))),
    }
  }
}

#[doc(hidden)]
pub fn map_optc<I: Clone, O1, O2, E: ParseError<I>, F, G>(input: I, first: F, second: G) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(O1) -> Option<O2>,
{
  map_opt(first, second)(input)
}

pub fn map_parser<I: Clone, O1, O2, E: ParseError<I>, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(O1) -> IResult<O1, O2, E>,
  O1: InputLength,
{
  move |input: I| {
    let (input, o1) = first(input)?;
    let (_, o2) = second(o1)?;
    Ok((input, o2))
  }
}

#[doc(hidden)]
pub fn map_parserc<I: Clone, O1, O2, E: ParseError<I>, F, G>(input: I, first: F, second: G) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(O1) -> IResult<O1, O2, E>,
  O1: InputLength,
{
  map_parser(first, second)(input)
}

pub fn flat_map<I, O1, O2, E: ParseError<I>, F, G, H>(first: F, second: G) -> impl Fn(I) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(O1) -> H,
  H: Fn(I) -> IResult<I, O2, E>
{
  move |input: I| {
    let (input, o1) = first(input)?;
    second(o1)(input)
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

pub fn complete<I: Clone, O, E: ParseError<I>, F>(f: F) -> impl Fn(I) -> IResult<I, O, E>
where
  F: Fn(I) -> IResult<I, O, E>,
{
  move |input: I| {
    let i = input.clone();
    match f(input) {
      Err(Err::Incomplete(_)) => {
        Err(Err::Error(E::from_error_kind(i, ErrorKind::Complete)))
      },
      rest => rest
    }
  }
}

#[doc(hidden)]
pub fn completec<I: Clone, O, E: ParseError<I>, F>(input: I, f: F) -> IResult<I, O, E>
where
  F: Fn(I) -> IResult<I, O, E>,
{
    complete(f)(input)
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Err, IResult, Needed};
  use error::ParseError;
  use bytes::complete::take;
  use number::complete::be_u8;

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
    ::character::streaming::alphanumeric1(input)
  }

  #[test]
  fn test_flat_map() {
      let input: &[u8] = &[3, 100, 101, 102, 103, 104][..];
      assert_parse!(flat_map(be_u8, take)(input), Ok((&[103, 104][..], &[100, 101, 102][..])));
  }
  
  #[test]
  fn test_map_opt() {
      let input: &[u8] = &[50][..];
      assert_parse!(map_opt(be_u8, |u| if u < 20 {Some(u)} else {None})(input), Err(Err::Error((&[50][..], ErrorKind::MapOpt))));
      assert_parse!(map_opt(be_u8, |u| if u > 20 {Some(u)} else {None})(input), Ok((&[][..], 50)));
  }

  #[test]
  fn test_map_parser() {
      let input: &[u8] = &[100, 101, 102, 103, 104][..];
      assert_parse!(map_parser(take(4usize), take(2usize))(input), Ok((&[104][..], &[100, 101][..])));
  }
}
