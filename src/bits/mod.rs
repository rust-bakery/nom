//! Bit level parsers and combinators
//!
//! In byte level parsing, the input is generally a `&[u8]` passed from combinator
//! to combinator as the slices are manipulated.
//!
//! Bit parsers take a `(I, usize)` as input. This type is a helper for doing bit manipulation
//! that wraps the input type. Use the `bits` function wrap a bit-level parser to take a byte-level
//! input.
//!
//! By passing a pair like this, we can leverage most of the existing combinators, and avoid
//! transforming the whole slice to a vector of booleans. This should make it easy
//! to see a byte slice as a bit stream, and parse code points of arbitrary bit length.

use error::{ErrorKind, ParseError};
use internal::{Err, IResult};
use lib::std::ops::{AddAssign, RangeFrom, Shl, Shr};
use traits::{InputIter, Slice};

#[macro_use]
mod macros;

pub mod complete;
pub mod streaming;

/// Takes `count` bits from the input and returns it as a specified type `Some(O)`.
/// `None` is returned if there is not enough bytes in the input to satisfy the
/// required bits.
pub(crate) fn take_bits_impl<I, O>((input, o): (I, usize), count: usize) -> ((I, usize), Option<O>)
where
  I: InputIter<Item = u8> + Slice<RangeFrom<usize>>,
  O: From<u8> + AddAssign + Shl<usize, Output = O> + Shr<usize, Output = O>,
{
  let required = (count + o) as f32 / 8.0;

  if let Some(_) = input.slice_index(required.ceil() as usize) {
    let mut acc: O = 0u8.into();
    let mut offset: usize = o;
    let mut remaining: usize = count;
    let mut end_offset: usize = 0;

    for byte in input.iter_elements().take(required.ceil() as usize + 1) {
      if remaining == 0 {
        break;
      }

      let val: O = ((byte << offset) as u8 >> offset as u8).into();

      if remaining < 8 - offset {
        acc += val >> (8 - offset - remaining);
        end_offset = remaining + offset;
        break;
      } else {
        acc += val << (remaining - (8 - offset));
        remaining -= 8 - offset;
        offset = 0;
      }
    }

    ((input.slice((required.floor() as usize)..), end_offset), Some(acc))
  } else {
    ((input, o), None)
  }
}

impl<I> ParseError<(I, usize)> for (I, ErrorKind) {
  fn from_error_kind((input, _): (I, usize), kind: ErrorKind) -> (I, ErrorKind) {
    (input, kind)
  }

  fn append(_: (I, usize), _: ErrorKind, other: (I, ErrorKind)) -> (I, ErrorKind) {
    other
  }
}

impl<I> ParseError<I> for ((I, usize), ErrorKind) {
  fn from_error_kind(input: I, kind: ErrorKind) -> ((I, usize), ErrorKind) {
    ((input, 0), kind)
  }

  fn append(_: I, _: ErrorKind, other: ((I, usize), ErrorKind)) -> ((I, usize), ErrorKind) {
    other
  }
}

/// Converts a byte-level input to a bit-level input, for consumption by a parser that uses bits.
///
/// Afterwards, the input is converted back to a byte-level parser, with any remaining bits thrown
/// away.
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult;
/// use nom::bits::bits;
/// use nom::bits::complete::take_bits;
///
/// fn take_4_bits(input: &[u8]) -> IResult<&[u8], u64> {
///   bits( take_bits(4usize) )(input)
/// }
///
/// let input = vec![0xAB, 0xCD, 0xEF, 0x12];
/// let sl    = &input[..];
///
/// assert_eq!(take_4_bits( sl ), Ok( (&sl[1..], 0xA) ));
/// ```
pub fn bits<I, O, E: ParseError<(I, usize)>, P>(parser: P) -> impl Fn(I) -> IResult<I, O, E>
where
  I: InputIter<Item = u8> + Slice<RangeFrom<usize>>,
  P: Fn((I, usize)) -> IResult<(I, usize), O, E>,
{
  move |input: I| match parser((input, 0)) {
    Ok(((rest, offset), res)) => {
      let byte_index = offset / 8 + if offset % 8 == 0 { 0 } else { 1 };
      Ok((rest.slice(byte_index..), res))
    }
    Err(Err::Incomplete(n)) => Err(Err::Incomplete(n.map(|u| u / 8 + 1))),
    Err(Err::Error(e)) => Err(Err::Error(e)),
    Err(Err::Failure(e)) => Err(Err::Failure(e)),
  }
}

#[doc(hidden)]
pub fn bitsc<I, O, E: ParseError<(I, usize)>, P>(input: I, parser: P) -> IResult<I, O, E>
where
  I: InputIter<Item = u8> + Slice<RangeFrom<usize>>,
  P: Fn((I, usize)) -> IResult<(I, usize), O, E>,
{
  bits(parser)(input)
}

/// Counterpart to bits, bytes transforms its bit stream input into a byte slice for the underlying
/// parser, allowing byte-slice parsers to work on bit streams.
///
/// A partial byte remaining in the input will be ignored and the given parser will start parsing
/// at the next full byte.
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult;
/// # use nom::combinator::rest;
/// # use nom::sequence::tuple;
/// use nom::bits::{bits, bytes, streaming::take_bits};
///
/// fn parse(input: &[u8]) -> IResult<&[u8], (u8, u8, &[u8])> {
///   bits(tuple((
///     take_bits(4usize),
///     take_bits(8usize),
///     bytes(rest)
///   )))(input)
/// }
///
/// let input = &[0xde, 0xad, 0xbe, 0xaf];
///
/// assert_eq!(parse( input ), Ok(( &[][..], (0xd, 0xea, &[0xbe, 0xaf][..]) )));
/// ```
pub fn bytes<I, O, E: ParseError<I>, P>(parser: P) -> impl Fn((I, usize)) -> IResult<(I, usize), O, E>
where
  I: InputIter<Item = u8> + Slice<RangeFrom<usize>>,
  P: Fn(I) -> IResult<I, O, E>,
{
  move |(input, offset): (I, usize)| {
    let inner = if offset % 8 != 0 {
      input.slice((1 + offset / 8)..)
    } else {
      input.slice((offset / 8)..)
    };
    let (rest, res) = parser(inner)?;
    Ok(((rest, 0), res))
  }
}

#[doc(hidden)]
pub fn bytesc<I, O, E: ParseError<I>, P>(input: (I, usize), parser: P) -> IResult<(I, usize), O, E>
where
  I: InputIter<Item = u8> + Slice<RangeFrom<usize>>,
  P: Fn(I) -> IResult<I, O, E>,
{
  bytes(parser)(input)
}
