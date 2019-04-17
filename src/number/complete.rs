use internal::*;
use error::ParseError;
use traits::{AsChar, InputIter, InputLength, InputTakeAtPosition};
use traits::{AtEof, ParseTo};
use lib::std::ops::{Range, RangeFrom, RangeTo};
use traits::{Offset, Slice};
use error::{ErrorKind, make_error};
use character::complete::{digit, digit1};

/// Recognizes an unsigned 1 byte integer (equivalent to take!(1)
#[inline]
pub fn be_u8<'a, E: ParseError<&'a[u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u8, E> {
  if i.len() < 1 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    Ok((&i[1..], i[0]))
  }
}

/// Recognizes big endian unsigned 2 bytes integer
#[inline]
pub fn be_u16<'a, E: ParseError<&'a[u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u16, E> {
  if i.len() < 2 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    let res = ((i[0] as u16) << 8) + i[1] as u16;
    Ok((&i[2..], res))
  }
}

/// Recognizes big endian unsigned 3 byte integer
#[inline]
pub fn be_u24<'a, E: ParseError<&'a[u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u32, E> {
  if i.len() < 3 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    let res = ((i[0] as u32) << 16) + ((i[1] as u32) << 8) + (i[2] as u32);
    Ok((&i[3..], res))
  }
}

/// Recognizes big endian unsigned 4 bytes integer
#[inline]
pub fn be_u32<'a, E: ParseError<&'a[u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u32, E> {
  if i.len() < 4 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    let res = ((i[0] as u32) << 24) + ((i[1] as u32) << 16) + ((i[2] as u32) << 8) + i[3] as u32;
    Ok((&i[4..], res))
  }
}

/// Recognizes big endian unsigned 8 bytes integer
#[inline]
pub fn be_u64<'a, E: ParseError<&'a[u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u64, E> {
  if i.len() < 8 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    let res = ((i[0] as u64) << 56) + ((i[1] as u64) << 48) + ((i[2] as u64) << 40) + ((i[3] as u64) << 32) + ((i[4] as u64) << 24)
      + ((i[5] as u64) << 16) + ((i[6] as u64) << 8) + i[7] as u64;
    Ok((&i[8..], res))
  }
}

/// Recognizes big endian unsigned 16 bytes integer
#[inline]
#[cfg(stable_i128)]
pub fn be_u128<'a, E: ParseError<&'a[u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u128, E> {
  if i.len() < 16 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    let res = ((i[0] as u128) << 120)
      + ((i[1] as u128) << 112)
      + ((i[2] as u128) << 104)
      + ((i[3] as u128) << 96)
      + ((i[4] as u128) << 88)
      + ((i[5] as u128) << 80)
      + ((i[6] as u128) << 72)
      + ((i[7] as u128) << 64)
      + ((i[8] as u128) << 56)
      + ((i[9] as u128) << 48)
      + ((i[10] as u128) << 40)
      + ((i[11] as u128) << 32)
      + ((i[12] as u128) << 24)
      + ((i[13] as u128) << 16)
      + ((i[14] as u128) << 8)
      + i[15] as u128;
    Ok((&i[16..], res))
  }
}

/// Recognizes a signed 1 byte integer (equivalent to take!(1)
#[inline]
pub fn be_i8<'a, E: ParseError<&'a[u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i8, E> {
  map!(i, be_u8, |x| x as i8)
}

/// Recognizes big endian signed 2 bytes integer
#[inline]
pub fn be_i16<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i16, E> {
  map!(i, be_u16, |x| x as i16)
}

/// Recognizes big endian signed 3 bytes integer
#[inline]
pub fn be_i24<'a, E: ParseError<&'a[u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i32, E> {
  // Same as the unsigned version but we need to sign-extend manually here
  map!(i, be_u24, |x| if x & 0x80_00_00 != 0 {
    (x | 0xff_00_00_00) as i32
  } else {
    x as i32
  })
}

/// Recognizes big endian signed 4 bytes integer
#[inline]
pub fn be_i32<'a, E: ParseError<&'a[u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i32, E> {
  map!(i, be_u32, |x| x as i32)
}

/// Recognizes big endian signed 8 bytes integer
#[inline]
pub fn be_i64<'a, E: ParseError<&'a[u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i64, E> {
  map!(i, be_u64, |x| x as i64)
}

/// Recognizes big endian signed 16 bytes integer
#[inline]
#[cfg(stable_i128)]
pub fn be_i128<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i128, E> {
  map!(i, be_u128, |x| x as i128)
}

/// Recognizes an unsigned 1 byte integer (equivalent to take!(1)
#[inline]
pub fn le_u8<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u8, E> {
  if i.len() < 1 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    Ok((&i[1..], i[0]))
  }
}

/// Recognizes little endian unsigned 2 bytes integer
#[inline]
pub fn le_u16<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u16, E> {
  if i.len() < 2 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    let res = ((i[1] as u16) << 8) + i[0] as u16;
    Ok((&i[2..], res))
  }
}

/// Recognizes little endian unsigned 3 byte integer
#[inline]
pub fn le_u24<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u32, E> {
  if i.len() < 3 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    let res = (i[0] as u32) + ((i[1] as u32) << 8) + ((i[2] as u32) << 16);
    Ok((&i[3..], res))
  }
}

/// Recognizes little endian unsigned 4 bytes integer
#[inline]
pub fn le_u32<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u32, E> {
  if i.len() < 4 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    let res = ((i[3] as u32) << 24) + ((i[2] as u32) << 16) + ((i[1] as u32) << 8) + i[0] as u32;
    Ok((&i[4..], res))
  }
}

/// Recognizes little endian unsigned 8 bytes integer
#[inline]
pub fn le_u64<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u64, E> {
  if i.len() < 8 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    let res = ((i[7] as u64) << 56) + ((i[6] as u64) << 48) + ((i[5] as u64) << 40) + ((i[4] as u64) << 32) + ((i[3] as u64) << 24)
      + ((i[2] as u64) << 16) + ((i[1] as u64) << 8) + i[0] as u64;
    Ok((&i[8..], res))
  }
}

/// Recognizes little endian unsigned 16 bytes integer
#[inline]
#[cfg(stable_i128)]
pub fn le_u128<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], u128, E> {
  if i.len() < 16 {
    Err(Err::Error(make_error(i, ErrorKind::Eof)))
  } else {
    let res = ((i[15] as u128) << 120)
      + ((i[14] as u128) << 112)
      + ((i[13] as u128) << 104)
      + ((i[12] as u128) << 96)
      + ((i[11] as u128) << 88)
      + ((i[10] as u128) << 80)
      + ((i[9] as u128) << 72)
      + ((i[8] as u128) << 64)
      + ((i[7] as u128) << 56)
      + ((i[6] as u128) << 48)
      + ((i[5] as u128) << 40)
      + ((i[4] as u128) << 32)
      + ((i[3] as u128) << 24)
      + ((i[2] as u128) << 16)
      + ((i[1] as u128) << 8)
      + i[0] as u128;
    Ok((&i[16..], res))
  }
}

/// Recognizes a signed 1 byte integer (equivalent to take!(1)
#[inline]
pub fn le_i8<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i8, E> {
  map!(i, le_u8, |x| x as i8)
}

/// Recognizes little endian signed 2 bytes integer
#[inline]
pub fn le_i16<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i16, E> {
  map!(i, le_u16, |x| x as i16)
}

/// Recognizes little endian signed 3 bytes integer
#[inline]
pub fn le_i24<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i32, E> {
  // Same as the unsigned version but we need to sign-extend manually here
  map!(i, le_u24, |x| if x & 0x80_00_00 != 0 {
    (x | 0xff_00_00_00) as i32
  } else {
    x as i32
  })
}

/// Recognizes little endian signed 4 bytes integer
#[inline]
pub fn le_i32<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i32, E> {
  map!(i, le_u32, |x| x as i32)
}

/// Recognizes little endian signed 8 bytes integer
#[inline]
pub fn le_i64<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i64, E> {
  map!(i, le_u64, |x| x as i64)
}

/// Recognizes little endian signed 16 bytes integer
#[inline]
#[cfg(stable_i128)]
pub fn le_i128<'a, E: ParseError<&'a [u8]>>(i: &'a[u8]) -> IResult<&'a[u8], i128, E> {
  map!(i, le_u128, |x| x as i128)
}

/// Recognizes big endian 4 bytes floating point number
#[inline]
pub fn be_f32<'a, E: ParseError<&'a [u8]>>(input: &'a[u8]) -> IResult<&'a[u8], f32, E> {
  match be_u32(input) {
    Err(e) => Err(e),
    Ok((i, o)) => Ok((i, f32::from_bits(o))),
  }
}

/// Recognizes big endian 8 bytes floating point number
#[inline]
pub fn be_f64<'a, E: ParseError<&'a [u8]>>(input: &'a[u8]) -> IResult<&'a[u8], f64, E> {
  match be_u64(input) {
    Err(e) => Err(e),
    Ok((i, o)) => Ok((i, f64::from_bits(o))),
  }
}

/// Recognizes little endian 4 bytes floating point number
#[inline]
pub fn le_f32<'a, E: ParseError<&'a [u8]>>(input: &'a[u8]) -> IResult<&'a[u8], f32, E> {
  match le_u32(input) {
    Err(e) => Err(e),
    Ok((i, o)) => Ok((i, f32::from_bits(o))),
  }
}

/// Recognizes little endian 8 bytes floating point number
#[inline]
pub fn le_f64<'a, E: ParseError<&'a [u8]>>(input: &'a[u8]) -> IResult<&'a[u8], f64, E> {
  match le_u64(input) {
    Err(e) => Err(e),
    Ok((i, o)) => Ok((i, f64::from_bits(o))),
  }
}

/// Recognizes a hex-encoded integer
#[inline]
pub fn hex_u32<'a, E: ParseError<&'a [u8]>>(input: &'a[u8]) -> IResult<&'a[u8], u32, E> {
  let (i, o) = ::bytes::complete::is_a(&b"0123456789abcdefABCDEF"[..])(input)?;
  // Do not parse more than 8 characters for a u32
  let (parsed, remaining) = if o.len() <= 8 {
    (o, i)
  } else {
    (&input[..8], &input[8..])
  };

  let res = parsed
    .iter()
    .rev()
    .enumerate()
    .map(|(k, &v)| {
      let digit = v as char;
      digit.to_digit(16).unwrap_or(0) << (k * 4)
    })
    .sum();

  Ok((remaining, res))
}

#[allow(unused_imports)]
#[cfg_attr(rustfmt, rustfmt_skip)]
pub fn recognize_float<T, E:ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: Clone + Offset,
  T: InputIter + AtEof,
  <T as InputIter>::Item: AsChar+Copy,
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar
{
  recognize!(input,
    tuple!(
      opt!(alt!(char!('+') | char!('-'))),
      alt!(
        value!((), tuple!(digit, opt!(pair!(char!('.'), opt!(digit)))))
      | value!((), tuple!(char!('.'), digit))
      ),
      opt!(tuple!(
        alt!(char!('e') | char!('E')),
        opt!(alt!(char!('+') | char!('-'))),
        // fixme: convert errors to failure here, since parsing a e or E indicates we should
        // have an exponent
        return_error!(ErrorKind::Digit, digit1)
        )
      )
    )
  )
}

/// Recognizes floating point number in a byte string and returns a f32
#[cfg(feature = "alloc")]
pub fn float<T, E:ParseError<T>>(input: T) -> IResult<T, f32, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: Clone + Offset,
  T: InputIter + InputLength + ParseTo<f32> + AtEof,
  <T as InputIter>::Item: AsChar+Copy,
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar
{
  match recognize_float(input) {
    Err(e) => Err(e),
    Ok((i, s)) => match s.parse_to() {
      Some(n) => Ok((i, n)),
      None =>  Err(Err::Error(E::from_error_kind(i, ErrorKind::ParseTo)))
    }
  }
}

/// Recognizes floating point number in a byte string and returns a f64
#[cfg(feature = "alloc")]
pub fn double<T, E:ParseError<T>>(input: T) -> IResult<T, f64, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: Clone + Offset,
  T: InputIter + InputLength + ParseTo<f64> + AtEof,
  <T as InputIter>::Item: AsChar+Copy,
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar
{
  match recognize_float(input) {
    Err(e) => Err(e),
    Ok((i, s)) => match s.parse_to() {
      Some(n) => Ok((i, n)),
      None =>  Err(Err::Error(E::from_error_kind(i, ErrorKind::ParseTo)))
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::Err;
  use error::ErrorKind;

  macro_rules! assert_parse(
    ($left: expr, $right: expr) => {
      let res: $crate::IResult<_, _, (_, ErrorKind)> = $left;
      assert_eq!(res, $right);
    };
  );

  #[test]
  fn i8_tests() {
    assert_parse!(be_i8(&[0x00]), Ok((&b""[..], 0)));
    assert_parse!(be_i8(&[0x7f]), Ok((&b""[..], 127)));
    assert_parse!(be_i8(&[0xff]), Ok((&b""[..], -1)));
    assert_parse!(be_i8(&[0x80]), Ok((&b""[..], -128)));
  }

  #[test]
  fn i16_tests() {
    assert_parse!(be_i16(&[0x00, 0x00]), Ok((&b""[..], 0)));
    assert_parse!(be_i16(&[0x7f, 0xff]), Ok((&b""[..], 32_767_i16)));
    assert_parse!(be_i16(&[0xff, 0xff]), Ok((&b""[..], -1)));
    assert_parse!(be_i16(&[0x80, 0x00]), Ok((&b""[..], -32_768_i16)));
  }

  #[test]
  fn u24_tests() {
    assert_parse!(be_u24(&[0x00, 0x00, 0x00]), Ok((&b""[..], 0)));
    assert_parse!(be_u24(&[0x00, 0xFF, 0xFF]), Ok((&b""[..], 65_535_u32)));
    assert_parse!(be_u24(&[0x12, 0x34, 0x56]), Ok((&b""[..], 1_193_046_u32)));
  }

  #[test]
  fn i24_tests() {
    assert_parse!(be_i24(&[0xFF, 0xFF, 0xFF]), Ok((&b""[..], -1_i32)));
    assert_parse!(be_i24(&[0xFF, 0x00, 0x00]), Ok((&b""[..], -65_536_i32)));
    assert_parse!(be_i24(&[0xED, 0xCB, 0xAA]), Ok((&b""[..], -1_193_046_i32)));
  }

  #[test]
  fn i32_tests() {
    assert_parse!(be_i32(&[0x00, 0x00, 0x00, 0x00]), Ok((&b""[..], 0)));
    assert_parse!(
      be_i32(&[0x7f, 0xff, 0xff, 0xff]),
      Ok((&b""[..], 2_147_483_647_i32))
    );
    assert_parse!(be_i32(&[0xff, 0xff, 0xff, 0xff]), Ok((&b""[..], -1)));
    assert_parse!(
      be_i32(&[0x80, 0x00, 0x00, 0x00]),
      Ok((&b""[..], -2_147_483_648_i32))
    );
  }

  #[test]
  fn i64_tests() {
    assert_parse!(
      be_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0))
    );
    assert_parse!(
      be_i64(&[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], 9_223_372_036_854_775_807_i64))
    );
    assert_parse!(
      be_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], -1))
    );
    assert_parse!(
      be_i64(&[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], -9_223_372_036_854_775_808_i64))
    );
  }

  #[test]
  #[cfg(stable_i128)]
  fn i128_tests() {
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0))
    );
    assert_parse!(
      be_i128(&[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], 170_141_183_460_469_231_731_687_303_715_884_105_727_i128))
    );
    assert_parse!(
      be_i128(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], -1))
    );
    assert_parse!(
      be_i128(&[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], -170_141_183_460_469_231_731_687_303_715_884_105_728_i128))
    );
  }

  #[test]
  fn le_i8_tests() {
    assert_parse!(le_i8(&[0x00]), Ok((&b""[..], 0)));
    assert_parse!(le_i8(&[0x7f]), Ok((&b""[..], 127)));
    assert_parse!(le_i8(&[0xff]), Ok((&b""[..], -1)));
    assert_parse!(le_i8(&[0x80]), Ok((&b""[..], -128)));
  }

  #[test]
  fn le_i16_tests() {
    assert_parse!(le_i16(&[0x00, 0x00]), Ok((&b""[..], 0)));
    assert_parse!(le_i16(&[0xff, 0x7f]), Ok((&b""[..], 32_767_i16)));
    assert_parse!(le_i16(&[0xff, 0xff]), Ok((&b""[..], -1)));
    assert_parse!(le_i16(&[0x00, 0x80]), Ok((&b""[..], -32_768_i16)));
  }

  #[test]
  fn le_u24_tests() {
    assert_parse!(le_u24(&[0x00, 0x00, 0x00]), Ok((&b""[..], 0)));
    assert_parse!(le_u24(&[0xFF, 0xFF, 0x00]), Ok((&b""[..], 65_535_u32)));
    assert_parse!(le_u24(&[0x56, 0x34, 0x12]), Ok((&b""[..], 1_193_046_u32)));
  }

  #[test]
  fn le_i24_tests() {
    assert_parse!(le_i24(&[0xFF, 0xFF, 0xFF]), Ok((&b""[..], -1_i32)));
    assert_parse!(le_i24(&[0x00, 0x00, 0xFF]), Ok((&b""[..], -65_536_i32)));
    assert_parse!(le_i24(&[0xAA, 0xCB, 0xED]), Ok((&b""[..], -1_193_046_i32)));
  }

  #[test]
  fn le_i32_tests() {
    assert_parse!(le_i32(&[0x00, 0x00, 0x00, 0x00]), Ok((&b""[..], 0)));
    assert_parse!(
      le_i32(&[0xff, 0xff, 0xff, 0x7f]),
      Ok((&b""[..], 2_147_483_647_i32))
    );
    assert_parse!(le_i32(&[0xff, 0xff, 0xff, 0xff]), Ok((&b""[..], -1)));
    assert_parse!(
      le_i32(&[0x00, 0x00, 0x00, 0x80]),
      Ok((&b""[..], -2_147_483_648_i32))
    );
  }

  #[test]
  fn le_i64_tests() {
    assert_parse!(
      le_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0))
    );
    assert_parse!(
      le_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]),
      Ok((&b""[..], 9_223_372_036_854_775_807_i64))
    );
    assert_parse!(
      le_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], -1))
    );
    assert_parse!(
      le_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80]),
      Ok((&b""[..], -9_223_372_036_854_775_808_i64))
    );
  }

  #[test]
  #[cfg(stable_i128)]
  fn le_i128_tests() {
    assert_parse!(
      le_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0))
    );
    assert_parse!(
      le_i128(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]),
      Ok((&b""[..], 170_141_183_460_469_231_731_687_303_715_884_105_727_i128))
    );
    assert_parse!(
      le_i128(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], -1))
    );
    assert_parse!(
      le_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80]),
      Ok((&b""[..], -170_141_183_460_469_231_731_687_303_715_884_105_728_i128))
    );
  }

  #[test]
  fn be_f32_tests() {
    assert_parse!(be_f32(&[0x00, 0x00, 0x00, 0x00]), Ok((&b""[..], 0_f32)));
    assert_parse!(
      be_f32(&[0x4d, 0x31, 0x1f, 0xd8]),
      Ok((&b""[..], 185_728_392_f32))
    );
  }

  #[test]
  fn be_f64_tests() {
    assert_parse!(
      be_f64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0_f64))
    );
    assert_parse!(
      be_f64(&[0x41, 0xa6, 0x23, 0xfb, 0x10, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 185_728_392_f64))
    );
  }

  #[test]
  fn le_f32_tests() {
    assert_parse!(le_f32(&[0x00, 0x00, 0x00, 0x00]), Ok((&b""[..], 0_f32)));
    assert_parse!(
      le_f32(&[0xd8, 0x1f, 0x31, 0x4d]),
      Ok((&b""[..], 185_728_392_f32))
    );
  }

  #[test]
  fn le_f64_tests() {
    assert_parse!(
      le_f64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0_f64))
    );
    assert_parse!(
      le_f64(&[0x00, 0x00, 0x00, 0x10, 0xfb, 0x23, 0xa6, 0x41]),
      Ok((&b""[..], 185_728_392_f64))
    );
  }

  #[test]
  fn hex_u32_tests() {
    assert_parse!(
      hex_u32(&b";"[..]),
      Err(Err::Error(error_position!(&b";"[..], ErrorKind::IsA)))
    );
    assert_parse!(hex_u32(&b"ff;"[..]), Ok((&b";"[..], 255)));
    assert_parse!(hex_u32(&b"1be2;"[..]), Ok((&b";"[..], 7138)));
    assert_parse!(hex_u32(&b"c5a31be2;"[..]), Ok((&b";"[..], 3_315_801_058)));
    assert_parse!(hex_u32(&b"C5A31be2;"[..]), Ok((&b";"[..], 3_315_801_058)));
    assert_parse!(hex_u32(&b"00c5a31be2;"[..]), Ok((&b"e2;"[..], 12_952_347)));
    assert_parse!(
      hex_u32(&b"c5a31be201;"[..]),
      Ok((&b"01;"[..], 3_315_801_058))
    );
    assert_parse!(hex_u32(&b"ffffffff;"[..]), Ok((&b";"[..], 4_294_967_295)));
    assert_parse!(hex_u32(&b"0x1be2;"[..]), Ok((&b"x1be2;"[..], 0)));
    assert_parse!(hex_u32(&b"12af"[..]), Ok((&b""[..], 0x12af)));
  }

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
      "-1.234E-12",
      "-1.234e-12",
    ];

    for test in test_cases.drain(..) {
      let expected32 = str::parse::<f32>(test).unwrap();
      let expected64 = str::parse::<f64>(test).unwrap();

      println!("now parsing: {} -> {}", test, expected32);

      let larger = format!("{};", test);
      assert_parse!(recognize_float(&larger[..]), Ok((";", test)));

      assert_parse!(float(larger.as_bytes()), Ok((&b";"[..], expected32)));
      assert_parse!(float(&larger[..]), Ok((";", expected32)));

      assert_parse!(double(larger.as_bytes()), Ok((&b";"[..], expected64)));
      assert_parse!(double(&larger[..]), Ok((";", expected64)));
    }

    let remaining_exponent = "-1.234E-";
    assert_parse!(
      recognize_float(remaining_exponent),
      Err(Err::Failure(("", ErrorKind::Digit)))
    );
  }

}
