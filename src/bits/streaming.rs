//! parsers recognizing bit streams, streaming input version

use error::{ErrorKind, ParseError};
use internal::{Err, IResult, Needed};
use lib::std::ops::{AddAssign, RangeFrom, Shl, Shr};
use take_bits_impl;
use traits::{InputIter, Slice, ToUsize};

/// Consumes the specified number of bits and trys to coerce them to `O`.
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, error::ErrorKind, Needed, IResult};
/// use nom::sequence::pair;
/// use nom::bits::bits;
/// use nom::bits::streaming::take_bits;
///
/// fn take_pair(input: &[u8]) -> IResult<&[u8], (u8, u8)> {
///   bits( pair( take_bits(4u8), take_bits(4u8) ) )(input)
/// }
///
/// let input = vec![0xAB, 0xCD, 0xEF];
/// let sl    = &input[..];
///
/// assert_eq!(take_pair( sl ),       Ok((&sl[1..], (0xA, 0xB))) );
/// assert_eq!(take_pair( &sl[1..] ), Ok((&sl[2..], (0xC, 0xD))) );
/// ```
pub fn take_bits<I, O, C, E: ParseError<(I, usize)>>(count: C) -> impl Fn((I, usize)) -> IResult<(I, usize), O, E>
where
  I: Slice<RangeFrom<usize>> + InputIter<Item = u8>,
  C: ToUsize,
  O: From<u8> + AddAssign + Shl<usize, Output = O> + Shr<usize, Output = O>,
{
  let c = count.to_usize();
  move |input: (I, usize)| {
    if c == 0 {
      Ok((input, 0u8.into()))
    } else {
      match take_bits_impl::<I, O>(input, c) {
        (rest, Some(b)) => Ok((rest, b)),
        (_, None) => Err(Err::Incomplete(Needed::Size(c))),
      }
    }
  }
}

/// Matches the given bit pattern.
///
/// The caller must specify the number of bits to consume. The matched value is included in the
/// result on success.
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult;
/// use nom::bits::bits;
/// use nom::bits::streaming::tag_bits;
///
/// fn take_a(input: &[u8]) -> IResult<&[u8], u8> {
///   bits( tag_bits(4u8, 0xA) )(input)
/// }
///
/// let input = vec![0xAB, 0xCD, 0xEF];
/// let sl    = &input[..];
///
/// assert_eq!(take_a( sl ), Ok((&sl[1..], 0xA)));
/// ```
pub fn tag_bits<I, O, C, E: ParseError<(I, usize)>>(count: C, tag: O) -> impl Fn((I, usize)) -> IResult<(I, usize), O, E>
where
  I: Slice<RangeFrom<usize>> + InputIter<Item = u8>,
  C: ToUsize,
  O: From<u8> + AddAssign + Shl<usize, Output = O> + Shr<usize, Output = O> + PartialEq,
{
  let c = count.to_usize();
  move |input: (I, usize)| match take_bits_impl::<I, O>(input, c) {
    (rest, Some(o)) => {
      if o.eq(&tag) {
        return Ok((rest, o));
      } else {
        return Err(Err::Error(E::from_error_kind(rest, ErrorKind::TagBits)));
      }
    }
    (_, None) => Err(Err::Incomplete(Needed::Size(c))),
  }
}
