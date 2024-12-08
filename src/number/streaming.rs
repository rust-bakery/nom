//! Parsers recognizing numbers, streaming version

use crate::branch::alt;
use crate::bytes::streaming::tag;
use crate::character::streaming::{char, digit1, sign};
use crate::combinator::{cut, map, opt, recognize};
use crate::error::{ErrorKind, ParseError};
use crate::lib::std::ops::{Add, Shl};
use crate::sequence::pair;
use crate::traits::{AsBytes, AsChar, Compare, Offset};
use crate::{internal::*, Input};

/// Recognizes an unsigned 1 byte integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_u8;
///
/// let parser = |s| {
///   be_u8::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"\x01abcd"[..], 0x00)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn be_u8<I, E: ParseError<I>>(input: I) -> IResult<I, u8, E>
where
  I: Input<Item = u8>,
{
  be_uint(input, 1)
}

/// Recognizes a big endian unsigned 2 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_u16;
///
/// let parser = |s| {
///   be_u16::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"abcd"[..], 0x0001)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn be_u16<I, E: ParseError<I>>(input: I) -> IResult<I, u16, E>
where
  I: Input<Item = u8>,
{
  be_uint(input, 2)
}

/// Recognizes a big endian unsigned 3 byte integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_u24;
///
/// let parser = |s| {
///   be_u24::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02abcd"[..]), Ok((&b"abcd"[..], 0x000102)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn be_u24<I, E: ParseError<I>>(input: I) -> IResult<I, u32, E>
where
  I: Input<Item = u8>,
{
  be_uint(input, 3)
}

/// Recognizes a big endian unsigned 4 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_u32;
///
/// let parser = |s| {
///   be_u32::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03abcd"[..]), Ok((&b"abcd"[..], 0x00010203)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn be_u32<I, E: ParseError<I>>(input: I) -> IResult<I, u32, E>
where
  I: Input<Item = u8>,
{
  be_uint(input, 4)
}

/// Recognizes a big endian unsigned 8 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_u64;
///
/// let parser = |s| {
///   be_u64::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcd"[..]), Ok((&b"abcd"[..], 0x0001020304050607)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn be_u64<I, E: ParseError<I>>(input: I) -> IResult<I, u64, E>
where
  I: Input<Item = u8>,
{
  be_uint(input, 8)
}

/// Recognizes a big endian unsigned 16 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_u128;
///
/// let parser = |s| {
///   be_u128::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15abcd"[..]), Ok((&b"abcd"[..], 0x00010203040506070809101112131415)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn be_u128<I, E: ParseError<I>>(input: I) -> IResult<I, u128, E>
where
  I: Input<Item = u8>,
{
  be_uint(input, 16)
}

#[inline]
fn be_uint<I, Uint, E: ParseError<I>>(input: I, bound: usize) -> IResult<I, Uint, E>
where
  I: Input<Item = u8>,
  Uint: Default + Shl<u8, Output = Uint> + Add<Uint, Output = Uint> + From<u8>,
{
  super::be_uint(bound).parse(input)
}

/// Recognizes a signed 1 byte integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_i8;
///
/// let parser = be_i8::<_, (_, ErrorKind)>;
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"\x01abcd"[..], 0x00)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn be_i8<I, E: ParseError<I>>(input: I) -> IResult<I, i8, E>
where
  I: Input<Item = u8>,
{
  be_u8.map(|x| x as i8).parse(input)
}

/// Recognizes a big endian signed 2 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_i16;
///
/// let parser = be_i16::<_, (_, ErrorKind)>;
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"abcd"[..], 0x0001)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn be_i16<I, E: ParseError<I>>(input: I) -> IResult<I, i16, E>
where
  I: Input<Item = u8>,
{
  be_u16.map(|x| x as i16).parse(input)
}

/// Recognizes a big endian signed 3 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_i24;
///
/// let parser = be_i24::<_, (_, ErrorKind)>;
///
/// assert_eq!(parser(&b"\x00\x01\x02abcd"[..]), Ok((&b"abcd"[..], 0x000102)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn be_i24<I, E: ParseError<I>>(input: I) -> IResult<I, i32, E>
where
  I: Input<Item = u8>,
{
  // Same as the unsigned version but we need to sign-extend manually here
  be_u24
    .map(|x| {
      if x & 0x80_00_00 != 0 {
        (x | 0xff_00_00_00) as i32
      } else {
        x as i32
      }
    })
    .parse(input)
}

/// Recognizes a big endian signed 4 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_i32;
///
/// let parser = be_i32::<_, (_, ErrorKind)>;
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03abcd"[..]), Ok((&b"abcd"[..], 0x00010203)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(4))));
/// ```
#[inline]
pub fn be_i32<I, E: ParseError<I>>(input: I) -> IResult<I, i32, E>
where
  I: Input<Item = u8>,
{
  be_u32.map(|x| x as i32).parse(input)
}

/// Recognizes a big endian signed 8 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_i64;
///
/// let parser = be_i64::<_, (_, ErrorKind)>;
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcd"[..]), Ok((&b"abcd"[..], 0x0001020304050607)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn be_i64<I, E: ParseError<I>>(input: I) -> IResult<I, i64, E>
where
  I: Input<Item = u8>,
{
  be_u64.map(|x| x as i64).parse(input)
}

/// Recognizes a big endian signed 16 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_i128;
///
/// let parser = be_i128::<_, (_, ErrorKind)>;
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15abcd"[..]), Ok((&b"abcd"[..], 0x00010203040506070809101112131415)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn be_i128<I, E: ParseError<I>>(input: I) -> IResult<I, i128, E>
where
  I: Input<Item = u8>,
{
  be_u128.map(|x| x as i128).parse(input)
}

/// Recognizes an unsigned 1 byte integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_u8;
///
/// let parser = le_u8::<_, (_, ErrorKind)>;
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"\x01abcd"[..], 0x00)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn le_u8<I, E: ParseError<I>>(input: I) -> IResult<I, u8, E>
where
  I: Input<Item = u8>,
{
  le_uint(input, 1)
}

/// Recognizes a little endian unsigned 2 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_u16;
///
/// let parser = |s| {
///   le_u16::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"abcd"[..], 0x0100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn le_u16<I, E: ParseError<I>>(input: I) -> IResult<I, u16, E>
where
  I: Input<Item = u8>,
{
  le_uint(input, 2)
}

/// Recognizes a little endian unsigned 3 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_u24;
///
/// let parser = |s| {
///   le_u24::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02abcd"[..]), Ok((&b"abcd"[..], 0x020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn le_u24<I, E: ParseError<I>>(input: I) -> IResult<I, u32, E>
where
  I: Input<Item = u8>,
{
  le_uint(input, 3)
}

/// Recognizes a little endian unsigned 4 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_u32;
///
/// let parser = |s| {
///   le_u32::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03abcd"[..]), Ok((&b"abcd"[..], 0x03020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn le_u32<I, E: ParseError<I>>(input: I) -> IResult<I, u32, E>
where
  I: Input<Item = u8>,
{
  le_uint(input, 4)
}

/// Recognizes a little endian unsigned 8 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_u64;
///
/// let parser = |s| {
///   le_u64::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcd"[..]), Ok((&b"abcd"[..], 0x0706050403020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn le_u64<I, E: ParseError<I>>(input: I) -> IResult<I, u64, E>
where
  I: Input<Item = u8>,
{
  le_uint(input, 8)
}

/// Recognizes a little endian unsigned 16 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_u128;
///
/// let parser = |s| {
///   le_u128::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15abcd"[..]), Ok((&b"abcd"[..], 0x15141312111009080706050403020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn le_u128<I, E: ParseError<I>>(input: I) -> IResult<I, u128, E>
where
  I: Input<Item = u8>,
{
  le_uint(input, 16)
}

#[inline]
fn le_uint<I, Uint, E: ParseError<I>>(input: I, bound: usize) -> IResult<I, Uint, E>
where
  I: Input<Item = u8>,
  Uint: Default + Shl<u8, Output = Uint> + Add<Uint, Output = Uint> + From<u8>,
{
  super::le_uint(bound).parse(input)
}

/// Recognizes a signed 1 byte integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_i8;
///
/// let parser = le_i8::<_, (_, ErrorKind)>;
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"\x01abcd"[..], 0x00)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn le_i8<I, E: ParseError<I>>(input: I) -> IResult<I, i8, E>
where
  I: Input<Item = u8>,
{
  le_u8.map(|x| x as i8).parse(input)
}

/// Recognizes a little endian signed 2 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_i16;
///
/// let parser = |s| {
///   le_i16::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"abcd"[..], 0x0100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn le_i16<I, E: ParseError<I>>(input: I) -> IResult<I, i16, E>
where
  I: Input<Item = u8>,
{
  le_u16.map(|x| x as i16).parse(input)
}

/// Recognizes a little endian signed 3 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_i24;
///
/// let parser = |s| {
///   le_i24::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02abcd"[..]), Ok((&b"abcd"[..], 0x020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn le_i24<I, E: ParseError<I>>(input: I) -> IResult<I, i32, E>
where
  I: Input<Item = u8>,
{
  // Same as the unsigned version but we need to sign-extend manually here
  le_u24
    .map(|x| {
      if x & 0x80_00_00 != 0 {
        (x | 0xff_00_00_00) as i32
      } else {
        x as i32
      }
    })
    .parse(input)
}

/// Recognizes a little endian signed 4 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_i32;
///
/// let parser = |s| {
///   le_i32::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03abcd"[..]), Ok((&b"abcd"[..], 0x03020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn le_i32<I, E: ParseError<I>>(input: I) -> IResult<I, i32, E>
where
  I: Input<Item = u8>,
{
  le_u32.map(|x| x as i32).parse(input)
}

/// Recognizes a little endian signed 8 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_i64;
///
/// let parser = |s| {
///   le_i64::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcd"[..]), Ok((&b"abcd"[..], 0x0706050403020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn le_i64<I, E: ParseError<I>>(input: I) -> IResult<I, i64, E>
where
  I: Input<Item = u8>,
{
  le_u64.map(|x| x as i64).parse(input)
}

/// Recognizes a little endian signed 16 bytes integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_i128;
///
/// let parser = |s| {
///   le_i128::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15abcd"[..]), Ok((&b"abcd"[..], 0x15141312111009080706050403020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn le_i128<I, E: ParseError<I>>(input: I) -> IResult<I, i128, E>
where
  I: Input<Item = u8>,
{
  le_u128.map(|x| x as i128).parse(input)
}

/// Recognizes an unsigned 1 byte integer
///
/// Note that endianness does not apply to 1 byte numbers.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::u8;
///
/// let parser = |s| {
///   u8::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x03abcefg"[..]), Ok((&b"\x03abcefg"[..], 0x00)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn u8<I, E: ParseError<I>>(input: I) -> IResult<I, u8, E>
where
  I: Input<Item = u8>,
{
  super::u8().parse(input)
}

/// Recognizes an unsigned 2 bytes integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian u16 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian u16 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::u16;
///
/// let be_u16 = |s| {
///   u16::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_u16(&b"\x00\x03abcefg"[..]), Ok((&b"abcefg"[..], 0x0003)));
/// assert_eq!(be_u16(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
///
/// let le_u16 = |s| {
///   u16::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_u16(&b"\x00\x03abcefg"[..]), Ok((&b"abcefg"[..], 0x0300)));
/// assert_eq!(le_u16(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn u16<I, E: ParseError<I>>(
  endian: crate::number::Endianness,
) -> impl Fn(I) -> IResult<I, u16, E>
where
  I: Input<Item = u8>,
{
  move |input| super::u16(endian).parse(input)
}

/// Recognizes an unsigned 3 byte integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian u24 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian u24 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::u24;
///
/// let be_u24 = |s| {
///   u24::<_,(_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_u24(&b"\x00\x03\x05abcefg"[..]), Ok((&b"abcefg"[..], 0x000305)));
/// assert_eq!(be_u24(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
///
/// let le_u24 = |s| {
///   u24::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_u24(&b"\x00\x03\x05abcefg"[..]), Ok((&b"abcefg"[..], 0x050300)));
/// assert_eq!(le_u24(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn u24<I, E: ParseError<I>>(
  endian: crate::number::Endianness,
) -> impl Fn(I) -> IResult<I, u32, E>
where
  I: Input<Item = u8>,
{
  move |input| super::u24(endian).parse(input)
}

/// Recognizes an unsigned 4 byte integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian u32 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian u32 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::u32;
///
/// let be_u32 = |s| {
///   u32::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_u32(&b"\x00\x03\x05\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x00030507)));
/// assert_eq!(be_u32(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
///
/// let le_u32 = |s| {
///   u32::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_u32(&b"\x00\x03\x05\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x07050300)));
/// assert_eq!(le_u32(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn u32<I, E: ParseError<I>>(
  endian: crate::number::Endianness,
) -> impl Fn(I) -> IResult<I, u32, E>
where
  I: Input<Item = u8>,
{
  move |input| super::u32(endian).parse(input)
}

/// Recognizes an unsigned 8 byte integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian u64 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian u64 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::u64;
///
/// let be_u64 = |s| {
///   u64::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_u64(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x0001020304050607)));
/// assert_eq!(be_u64(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
///
/// let le_u64 = |s| {
///   u64::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_u64(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x0706050403020100)));
/// assert_eq!(le_u64(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn u64<I, E: ParseError<I>>(
  endian: crate::number::Endianness,
) -> impl Fn(I) -> IResult<I, u64, E>
where
  I: Input<Item = u8>,
{
  move |input| super::u64(endian).parse(input)
}

/// Recognizes an unsigned 16 byte integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian u128 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian u128 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::u128;
///
/// let be_u128 = |s| {
///   u128::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_u128(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x00010203040506070001020304050607)));
/// assert_eq!(be_u128(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
///
/// let le_u128 = |s| {
///   u128::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_u128(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x07060504030201000706050403020100)));
/// assert_eq!(le_u128(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn u128<I, E: ParseError<I>>(
  endian: crate::number::Endianness,
) -> impl Fn(I) -> IResult<I, u128, E>
where
  I: Input<Item = u8>,
{
  move |input| super::u128(endian).parse(input)
}

/// Recognizes a signed 1 byte integer
///
/// Note that endianness does not apply to 1 byte numbers.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::i8;
///
/// let parser = |s| {
///   i8::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x03abcefg"[..]), Ok((&b"\x03abcefg"[..], 0x00)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn i8<I, E: ParseError<I>>(i: I) -> IResult<I, i8, E>
where
  I: Input<Item = u8>,
{
  super::u8().map(|x| x as i8).parse(i)
}

/// Recognizes a signed 2 byte integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian i16 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian i16 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::i16;
///
/// let be_i16 = |s| {
///   i16::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_i16(&b"\x00\x03abcefg"[..]), Ok((&b"abcefg"[..], 0x0003)));
/// assert_eq!(be_i16(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
///
/// let le_i16 = |s| {
///   i16::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_i16(&b"\x00\x03abcefg"[..]), Ok((&b"abcefg"[..], 0x0300)));
/// assert_eq!(le_i16(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn i16<I, E: ParseError<I>>(
  endian: crate::number::Endianness,
) -> impl Fn(I) -> IResult<I, i16, E>
where
  I: Input<Item = u8>,
{
  move |input| super::i16(endian).parse(input)
}

/// Recognizes a signed 3 byte integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian i24 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian i24 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::i24;
///
/// let be_i24 = |s| {
///   i24::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_i24(&b"\x00\x03\x05abcefg"[..]), Ok((&b"abcefg"[..], 0x000305)));
/// assert_eq!(be_i24(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
///
/// let le_i24 = |s| {
///   i24::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_i24(&b"\x00\x03\x05abcefg"[..]), Ok((&b"abcefg"[..], 0x050300)));
/// assert_eq!(le_i24(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn i24<I, E: ParseError<I>>(
  endian: crate::number::Endianness,
) -> impl Fn(I) -> IResult<I, i32, E>
where
  I: Input<Item = u8>,
{
  move |input| super::i24(endian).parse(input)
}

/// Recognizes a signed 4 byte integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian i32 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian i32 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::i32;
///
/// let be_i32 = |s| {
///   i32::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_i32(&b"\x00\x03\x05\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x00030507)));
/// assert_eq!(be_i32(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
///
/// let le_i32 = |s| {
///   i32::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_i32(&b"\x00\x03\x05\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x07050300)));
/// assert_eq!(le_i32(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn i32<I, E: ParseError<I>>(
  endian: crate::number::Endianness,
) -> impl Fn(I) -> IResult<I, i32, E>
where
  I: Input<Item = u8>,
{
  move |input| super::i32(endian).parse(input)
}

/// Recognizes a signed 8 byte integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian i64 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian i64 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::i64;
///
/// let be_i64 = |s| {
///   i64::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_i64(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x0001020304050607)));
/// assert_eq!(be_i64(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
///
/// let le_i64 = |s| {
///   i64::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_i64(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x0706050403020100)));
/// assert_eq!(le_i64(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn i64<I, E: ParseError<I>>(
  endian: crate::number::Endianness,
) -> impl Fn(I) -> IResult<I, i64, E>
where
  I: Input<Item = u8>,
{
  move |input| super::i64(endian).parse(input)
}

/// Recognizes a signed 16 byte integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian i128 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian i128 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::i128;
///
/// let be_i128 = |s| {
///   i128::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_i128(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x00010203040506070001020304050607)));
/// assert_eq!(be_i128(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
///
/// let le_i128 = |s| {
///   i128::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_i128(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x07060504030201000706050403020100)));
/// assert_eq!(le_i128(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn i128<I, E: ParseError<I>>(
  endian: crate::number::Endianness,
) -> impl Fn(I) -> IResult<I, i128, E>
where
  I: Input<Item = u8>,
{
  move |input| super::i128(endian).parse(input)
}

/// Recognizes a big endian 4 bytes floating point number.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_f32;
///
/// let parser = |s| {
///   be_f32::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&[0x40, 0x29, 0x00, 0x00][..]), Ok((&b""[..], 2.640625)));
/// assert_eq!(parser(&[0x01][..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn be_f32<I, E: ParseError<I>>(input: I) -> IResult<I, f32, E>
where
  I: Input<Item = u8>,
{
  match be_u32(input) {
    Err(e) => Err(e),
    Ok((i, o)) => Ok((i, f32::from_bits(o))),
  }
}

/// Recognizes a big endian 8 bytes floating point number.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::be_f64;
///
/// let parser = |s| {
///   be_f64::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&[0x40, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(parser(&[0x01][..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn be_f64<I, E: ParseError<I>>(input: I) -> IResult<I, f64, E>
where
  I: Input<Item = u8>,
{
  match be_u64(input) {
    Err(e) => Err(e),
    Ok((i, o)) => Ok((i, f64::from_bits(o))),
  }
}

/// Recognizes a little endian 4 bytes floating point number.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_f32;
///
/// let parser = |s| {
///   le_f32::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&[0x00, 0x00, 0x48, 0x41][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(parser(&[0x01][..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn le_f32<I, E: ParseError<I>>(input: I) -> IResult<I, f32, E>
where
  I: Input<Item = u8>,
{
  match le_u32(input) {
    Err(e) => Err(e),
    Ok((i, o)) => Ok((i, f32::from_bits(o))),
  }
}

/// Recognizes a little endian 8 bytes floating point number.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::le_f64;
///
/// let parser = |s| {
///   le_f64::<_, (_, ErrorKind)>(s)
/// };
///
/// assert_eq!(parser(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x41][..]), Ok((&b""[..], 3145728.0)));
/// assert_eq!(parser(&[0x01][..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn le_f64<I, E: ParseError<I>>(input: I) -> IResult<I, f64, E>
where
  I: Input<Item = u8>,
{
  match le_u64(input) {
    Err(e) => Err(e),
    Ok((i, o)) => Ok((i, f64::from_bits(o))),
  }
}

/// Recognizes a 4 byte floating point number
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian f32 float,
/// otherwise if `nom::number::Endianness::Little` parse a little endian f32 float.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::f32;
///
/// let be_f32 = |s| {
///   f32::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_f32(&[0x41, 0x48, 0x00, 0x00][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(be_f32(&b"abc"[..]), Err(Err::Incomplete(Needed::new(1))));
///
/// let le_f32 = |s| {
///   f32::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_f32(&[0x00, 0x00, 0x48, 0x41][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(le_f32(&b"abc"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn f32<I, E: ParseError<I>>(endian: crate::number::Endianness) -> fn(I) -> IResult<I, f32, E>
where
  I: Input<Item = u8>,
{
  match endian {
    crate::number::Endianness::Big => be_f32,
    crate::number::Endianness::Little => le_f32,
    #[cfg(target_endian = "big")]
    crate::number::Endianness::Native => be_f32,
    #[cfg(target_endian = "little")]
    crate::number::Endianness::Native => le_f32,
  }
}

/// Recognizes an 8 byte floating point number
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian f64 float,
/// otherwise if `nom::number::Endianness::Little` parse a little endian f64 float.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::streaming::f64;
///
/// let be_f64 = |s| {
///   f64::<_, (_, ErrorKind)>(nom::number::Endianness::Big)(s)
/// };
///
/// assert_eq!(be_f64(&[0x40, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(be_f64(&b"abc"[..]), Err(Err::Incomplete(Needed::new(5))));
///
/// let le_f64 = |s| {
///   f64::<_, (_, ErrorKind)>(nom::number::Endianness::Little)(s)
/// };
///
/// assert_eq!(le_f64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x29, 0x40][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(le_f64(&b"abc"[..]), Err(Err::Incomplete(Needed::new(5))));
/// ```
#[inline]
pub fn f64<I, E: ParseError<I>>(endian: crate::number::Endianness) -> fn(I) -> IResult<I, f64, E>
where
  I: Input<Item = u8>,
{
  match endian {
    crate::number::Endianness::Big => be_f64,
    crate::number::Endianness::Little => le_f64,
    #[cfg(target_endian = "big")]
    crate::number::Endianness::Native => be_f64,
    #[cfg(target_endian = "little")]
    crate::number::Endianness::Native => le_f64,
  }
}

/// Recognizes a hex-encoded integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::number::streaming::hex_u32;
///
/// let parser = |s| {
///   hex_u32(s)
/// };
///
/// assert_eq!(parser(&b"01AE;"[..]), Ok((&b";"[..], 0x01AE)));
/// assert_eq!(parser(&b"abc"[..]), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(parser(&b"ggg"[..]), Err(Err::Error((&b"ggg"[..], ErrorKind::IsA))));
/// ```
#[inline]
pub fn hex_u32<I, E: ParseError<I>>(input: I) -> IResult<I, u32, E>
where
  I: Input + AsBytes,
  <I as Input>::Item: AsChar,
{
  let e: ErrorKind = ErrorKind::IsA;
  let (i, o) = input.split_at_position1(
    |c| {
      let c = c.as_char();
      !"0123456789abcdefABCDEF".contains(c)
    },
    e,
  )?;

  // Do not parse more than 8 characters for a u32
  let (remaining, parsed) = if o.input_len() <= 8 {
    (i, o)
  } else {
    input.take_split(8)
  };

  let res = parsed
    .as_bytes()
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
pub fn recognize_float<T, E:ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Clone + Offset,
  T: Input,
  <T as Input>::Item: AsChar,
{
  recognize((
      opt(alt((char('+'), char('-')))),
      alt((
        map((digit1, opt(pair(char('.'), opt(digit1)))), |_| ()),
        map((char('.'), digit1), |_| ())
      )),
      opt((
        alt((char('e'), char('E'))),
        opt(alt((char('+'), char('-')))),
        cut(digit1)
      ))
  )).parse(input)
}

// workaround until issues with minimal-lexical are fixed
#[doc(hidden)]
pub fn recognize_float_or_exceptions<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Clone + Offset,
  T: Input + Compare<&'static str>,
  <T as Input>::Item: AsChar,
{
  alt((
    |i: T| {
      recognize_float::<_, E>(i.clone()).map_err(|e| match e {
        crate::Err::Error(_) => crate::Err::Error(E::from_error_kind(i, ErrorKind::Float)),
        crate::Err::Failure(_) => crate::Err::Failure(E::from_error_kind(i, ErrorKind::Float)),
        crate::Err::Incomplete(needed) => crate::Err::Incomplete(needed),
      })
    },
    |i: T| {
      crate::bytes::streaming::tag_no_case::<_, _, E>("nan")(i.clone())
        .map_err(|_| crate::Err::Error(E::from_error_kind(i, ErrorKind::Float)))
    },
    |i: T| {
      crate::bytes::streaming::tag_no_case::<_, _, E>("infinity")(i.clone())
        .map_err(|_| crate::Err::Error(E::from_error_kind(i, ErrorKind::Float)))
    },
    |i: T| {
      crate::bytes::streaming::tag_no_case::<_, _, E>("inf")(i.clone())
        .map_err(|_| crate::Err::Error(E::from_error_kind(i, ErrorKind::Float)))
    },
  ))
  .parse(input)
}

/// Recognizes a floating point number in text format
///
/// It returns a tuple of (`sign`, `integer part`, `fraction part` and `exponent`) of the input
/// data.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
pub fn recognize_float_parts<T, E: ParseError<T>>(input: T) -> IResult<T, (bool, T, T, i32), E>
where
  T: Clone + Offset,
  T: Input,
  <T as Input>::Item: AsChar,
  T: for<'a> Compare<&'a [u8]>,
  T: AsBytes,
{
  let (i, sign) = sign(input.clone())?;

  //let (i, zeroes) = take_while(|c: <T as InputTakeAtPosition>::Item| c.as_char() == '0')(i)?;
  let (i, zeroes) = match i.as_bytes().iter().position(|c| *c != b'0') {
    Some(index) => i.take_split(index),
    None => i.take_split(i.input_len()),
  };

  //let (i, mut integer) = digit0(i)?;
  let (i, mut integer) = match i
    .as_bytes()
    .iter()
    .position(|c| !(*c >= b'0' && *c <= b'9'))
  {
    Some(index) => i.take_split(index),
    None => i.take_split(i.input_len()),
  };

  if integer.input_len() == 0 && zeroes.input_len() > 0 {
    // keep the last zero if integer is empty
    integer = zeroes.take_from(zeroes.input_len() - 1);
  }

  let (i, opt_dot) = opt(tag(&b"."[..])).parse(i)?;
  let (i, fraction) = if opt_dot.is_none() {
    let i2 = i.clone();
    (i2, i.take(0))
  } else {
    // match number, trim right zeroes
    let mut zero_count = 0usize;
    let mut position = None;
    for (pos, c) in i.as_bytes().iter().enumerate() {
      if *c >= b'0' && *c <= b'9' {
        if *c == b'0' {
          zero_count += 1;
        } else {
          zero_count = 0;
        }
      } else {
        position = Some(pos);
        break;
      }
    }

    let position = match position {
      Some(p) => p,
      None => return Err(Err::Incomplete(Needed::new(1))),
    };

    let index = if zero_count == 0 {
      position
    } else if zero_count == position {
      position - zero_count + 1
    } else {
      position - zero_count
    };

    (i.take_from(position), i.take(index))
  };

  if integer.input_len() == 0 && fraction.input_len() == 0 {
    return Err(Err::Error(E::from_error_kind(input, ErrorKind::Float)));
  }

  let i2 = i.clone();
  let (i, e) = match i.as_bytes().iter().next() {
    Some(b'e') => (i.take_from(1), true),
    Some(b'E') => (i.take_from(1), true),
    _ => (i, false),
  };

  let (i, exp) = if e {
    cut(crate::character::streaming::i32).parse(i)?
  } else {
    (i2, 0)
  };

  Ok((i, (sign, integer, fraction, exp)))
}

/// Recognizes floating point number in text format and returns a f32.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::complete::float;
///
/// let parser = |s| {
///   float(s)
/// };
///
/// assert_eq!(parser("11e-1"), Ok(("", 1.1)));
/// assert_eq!(parser("123E-02"), Ok(("", 1.23)));
/// assert_eq!(parser("123K-01"), Ok(("K-01", 123.0)));
/// assert_eq!(parser("abc"), Err(Err::Error(("abc", ErrorKind::Float))));
/// ```
pub fn float<T, E: ParseError<T>>(input: T) -> IResult<T, f32, E>
where
  T: Clone + Offset,
  T: Input + crate::traits::ParseTo<f32> + Compare<&'static str>,
  <T as Input>::Item: AsChar + Clone,
  T: AsBytes,
  T: for<'a> Compare<&'a [u8]>,
{
  /*
  let (i, (sign, integer, fraction, exponent)) = recognize_float_parts(input)?;

  let mut float: f32 = minimal_lexical::parse_float(
    integer.as_bytes().iter(),
    fraction.as_bytes().iter(),
    exponent,
  );
  if !sign {
    float = -float;
  }

  Ok((i, float))
  */
  let (i, s) = recognize_float_or_exceptions(input)?;
  match s.parse_to() {
    Some(f) => Ok((i, f)),
    None => Err(crate::Err::Error(E::from_error_kind(
      i,
      crate::error::ErrorKind::Float,
    ))),
  }
}

/// Recognizes floating point number in text format and returns a f64.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed};
/// # use nom::Needed::Size;
/// use nom::number::complete::double;
///
/// let parser = |s| {
///   double(s)
/// };
///
/// assert_eq!(parser("11e-1"), Ok(("", 1.1)));
/// assert_eq!(parser("123E-02"), Ok(("", 1.23)));
/// assert_eq!(parser("123K-01"), Ok(("K-01", 123.0)));
/// assert_eq!(parser("abc"), Err(Err::Error(("abc", ErrorKind::Float))));
/// ```
pub fn double<T, E: ParseError<T>>(input: T) -> IResult<T, f64, E>
where
  T: Clone + Offset,
  T: Input + crate::traits::ParseTo<f64> + Compare<&'static str>,
  <T as Input>::Item: AsChar + Clone,
  T: AsBytes,
  T: for<'a> Compare<&'a [u8]>,
{
  /*
  let (i, (sign, integer, fraction, exponent)) = recognize_float_parts(input)?;

  let mut float: f64 = minimal_lexical::parse_float(
    integer.as_bytes().iter(),
    fraction.as_bytes().iter(),
    exponent,
  );
  if !sign {
    float = -float;
  }

  Ok((i, float))
  */
  let (i, s) = recognize_float_or_exceptions(input)?;
  match s.parse_to() {
    Some(f) => Ok((i, f)),
    None => Err(crate::Err::Error(E::from_error_kind(
      i,
      crate::error::ErrorKind::Float,
    ))),
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::error::ErrorKind;
  use crate::internal::{Err, Needed};
  use proptest::prelude::*;

  macro_rules! assert_parse(
    ($left: expr, $right: expr) => {
      let res: $crate::IResult<_, _, (_, ErrorKind)> = $left;
      assert_eq!(res, $right);
    };
  );

  #[test]
  fn i8_tests() {
    assert_parse!(be_i8(&[0x00][..]), Ok((&b""[..], 0)));
    assert_parse!(be_i8(&[0x7f][..]), Ok((&b""[..], 127)));
    assert_parse!(be_i8(&[0xff][..]), Ok((&b""[..], -1)));
    assert_parse!(be_i8(&[0x80][..]), Ok((&b""[..], -128)));
    assert_parse!(be_i8(&[][..]), Err(Err::Incomplete(Needed::new(1))));
  }

  #[test]
  fn i16_tests() {
    assert_parse!(be_i16(&[0x00, 0x00][..]), Ok((&b""[..], 0)));
    assert_parse!(be_i16(&[0x7f, 0xff][..]), Ok((&b""[..], 32_767_i16)));
    assert_parse!(be_i16(&[0xff, 0xff][..]), Ok((&b""[..], -1)));
    assert_parse!(be_i16(&[0x80, 0x00][..]), Ok((&b""[..], -32_768_i16)));
    assert_parse!(be_i16(&[][..]), Err(Err::Incomplete(Needed::new(2))));
    assert_parse!(be_i16(&[0x00][..]), Err(Err::Incomplete(Needed::new(1))));
  }

  #[test]
  fn u24_tests() {
    assert_parse!(be_u24(&[0x00, 0x00, 0x00][..]), Ok((&b""[..], 0)));
    assert_parse!(be_u24(&[0x00, 0xFF, 0xFF][..]), Ok((&b""[..], 65_535_u32)));
    assert_parse!(
      be_u24(&[0x12, 0x34, 0x56][..]),
      Ok((&b""[..], 1_193_046_u32))
    );
    assert_parse!(be_u24(&[][..]), Err(Err::Incomplete(Needed::new(3))));
    assert_parse!(be_u24(&[0x00][..]), Err(Err::Incomplete(Needed::new(2))));
    assert_parse!(
      be_u24(&[0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(1)))
    );
  }

  #[test]
  fn i24_tests() {
    assert_parse!(be_i24(&[0xFF, 0xFF, 0xFF][..]), Ok((&b""[..], -1_i32)));
    assert_parse!(be_i24(&[0xFF, 0x00, 0x00][..]), Ok((&b""[..], -65_536_i32)));
    assert_parse!(
      be_i24(&[0xED, 0xCB, 0xAA][..]),
      Ok((&b""[..], -1_193_046_i32))
    );
    assert_parse!(be_i24(&[][..]), Err(Err::Incomplete(Needed::new(3))));
    assert_parse!(be_i24(&[0x00][..]), Err(Err::Incomplete(Needed::new(2))));
    assert_parse!(
      be_i24(&[0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(1)))
    );
  }

  #[test]
  fn i32_tests() {
    assert_parse!(be_i32(&[0x00, 0x00, 0x00, 0x00][..]), Ok((&b""[..], 0)));
    assert_parse!(
      be_i32(&[0x7f, 0xff, 0xff, 0xff][..]),
      Ok((&b""[..], 2_147_483_647_i32))
    );
    assert_parse!(be_i32(&[0xff, 0xff, 0xff, 0xff][..]), Ok((&b""[..], -1)));
    assert_parse!(
      be_i32(&[0x80, 0x00, 0x00, 0x00][..]),
      Ok((&b""[..], -2_147_483_648_i32))
    );
    assert_parse!(be_i32(&[][..]), Err(Err::Incomplete(Needed::new(4))));
    assert_parse!(be_i32(&[0x00][..]), Err(Err::Incomplete(Needed::new(3))));
    assert_parse!(
      be_i32(&[0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(2)))
    );
    assert_parse!(
      be_i32(&[0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(1)))
    );
  }

  #[test]
  fn i64_tests() {
    assert_parse!(
      be_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Ok((&b""[..], 0))
    );
    assert_parse!(
      be_i64(&[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff][..]),
      Ok((&b""[..], 9_223_372_036_854_775_807_i64))
    );
    assert_parse!(
      be_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff][..]),
      Ok((&b""[..], -1))
    );
    assert_parse!(
      be_i64(&[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Ok((&b""[..], -9_223_372_036_854_775_808_i64))
    );
    assert_parse!(be_i64(&[][..]), Err(Err::Incomplete(Needed::new(8))));
    assert_parse!(be_i64(&[0x00][..]), Err(Err::Incomplete(Needed::new(7))));
    assert_parse!(
      be_i64(&[0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(6)))
    );
    assert_parse!(
      be_i64(&[0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(5)))
    );
    assert_parse!(
      be_i64(&[0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(4)))
    );
    assert_parse!(
      be_i64(&[0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(3)))
    );
    assert_parse!(
      be_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(2)))
    );
    assert_parse!(
      be_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(1)))
    );
  }

  #[test]
  fn i128_tests() {
    assert_parse!(
      be_i128(
        &[
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00
        ][..]
      ),
      Ok((&b""[..], 0))
    );
    assert_parse!(
      be_i128(
        &[
          0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff
        ][..]
      ),
      Ok((
        &b""[..],
        170_141_183_460_469_231_731_687_303_715_884_105_727_i128
      ))
    );
    assert_parse!(
      be_i128(
        &[
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff
        ][..]
      ),
      Ok((&b""[..], -1))
    );
    assert_parse!(
      be_i128(
        &[
          0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00
        ][..]
      ),
      Ok((
        &b""[..],
        -170_141_183_460_469_231_731_687_303_715_884_105_728_i128
      ))
    );
    assert_parse!(be_i128(&[][..]), Err(Err::Incomplete(Needed::new(16))));
    assert_parse!(be_i128(&[0x00][..]), Err(Err::Incomplete(Needed::new(15))));
    assert_parse!(
      be_i128(&[0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(14)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(13)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(12)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(11)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(10)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(9)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(8)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(7)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(6)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(5)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(4)))
    );
    assert_parse!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Err(Err::Incomplete(Needed::new(3)))
    );
    assert_parse!(
      be_i128(
        &[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]
      ),
      Err(Err::Incomplete(Needed::new(2)))
    );
    assert_parse!(
      be_i128(
        &[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
          [..]
      ),
      Err(Err::Incomplete(Needed::new(1)))
    );
  }

  #[test]
  fn le_i8_tests() {
    assert_parse!(le_i8(&[0x00][..]), Ok((&b""[..], 0)));
    assert_parse!(le_i8(&[0x7f][..]), Ok((&b""[..], 127)));
    assert_parse!(le_i8(&[0xff][..]), Ok((&b""[..], -1)));
    assert_parse!(le_i8(&[0x80][..]), Ok((&b""[..], -128)));
  }

  #[test]
  fn le_i16_tests() {
    assert_parse!(le_i16(&[0x00, 0x00][..]), Ok((&b""[..], 0)));
    assert_parse!(le_i16(&[0xff, 0x7f][..]), Ok((&b""[..], 32_767_i16)));
    assert_parse!(le_i16(&[0xff, 0xff][..]), Ok((&b""[..], -1)));
    assert_parse!(le_i16(&[0x00, 0x80][..]), Ok((&b""[..], -32_768_i16)));
  }

  #[test]
  fn le_u16_test() {
    assert_parse!(le_u16(&[0x00, 0x03][..]), Ok((&b""[..], 0x0300)));
    assert_parse!(le_u16(&[b'a', b'b'][..]), Ok((&b""[..], 0x6261)));
    assert_parse!(le_u16(&[0x01][..]), Err(Err::Incomplete(Needed::new(1))));
  }

  #[test]
  fn le_u24_tests() {
    assert_parse!(le_u24(&[0x00, 0x00, 0x00][..]), Ok((&b""[..], 0)));
    assert_parse!(le_u24(&[0xFF, 0xFF, 0x00][..]), Ok((&b""[..], 65_535_u32)));
    assert_parse!(
      le_u24(&[0x56, 0x34, 0x12][..]),
      Ok((&b""[..], 1_193_046_u32))
    );
  }

  #[test]
  fn le_i24_tests() {
    assert_parse!(le_i24(&[0xFF, 0xFF, 0xFF][..]), Ok((&b""[..], -1_i32)));
    assert_parse!(le_i24(&[0x00, 0x00, 0xFF][..]), Ok((&b""[..], -65_536_i32)));
    assert_parse!(
      le_i24(&[0xAA, 0xCB, 0xED][..]),
      Ok((&b""[..], -1_193_046_i32))
    );
  }

  #[test]
  fn le_i32_tests() {
    assert_parse!(le_i32(&[0x00, 0x00, 0x00, 0x00][..]), Ok((&b""[..], 0)));
    assert_parse!(
      le_i32(&[0xff, 0xff, 0xff, 0x7f][..]),
      Ok((&b""[..], 2_147_483_647_i32))
    );
    assert_parse!(le_i32(&[0xff, 0xff, 0xff, 0xff][..]), Ok((&b""[..], -1)));
    assert_parse!(
      le_i32(&[0x00, 0x00, 0x00, 0x80][..]),
      Ok((&b""[..], -2_147_483_648_i32))
    );
  }

  #[test]
  fn le_u32_test() {
    assert_parse!(
      le_u32(&[0x00, 0x03, 0x05, 0x07][..]),
      Ok((&b""[..], 0x07050300))
    );
    assert_parse!(
      le_u32(&[b'a', b'b', b'c', b'd'][..]),
      Ok((&b""[..], 0x64636261))
    );
    assert_parse!(le_u32(&[0x01][..]), Err(Err::Incomplete(Needed::new(3))));
  }

  #[test]
  fn le_i64_tests() {
    assert_parse!(
      le_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Ok((&b""[..], 0))
    );
    assert_parse!(
      le_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f][..]),
      Ok((&b""[..], 9_223_372_036_854_775_807_i64))
    );
    assert_parse!(
      le_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff][..]),
      Ok((&b""[..], -1))
    );
    assert_parse!(
      le_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80][..]),
      Ok((&b""[..], -9_223_372_036_854_775_808_i64))
    );
  }

  #[test]
  fn le_i128_tests() {
    assert_parse!(
      le_i128(
        &[
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00
        ][..]
      ),
      Ok((&b""[..], 0))
    );
    assert_parse!(
      le_i128(
        &[
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0x7f
        ][..]
      ),
      Ok((
        &b""[..],
        170_141_183_460_469_231_731_687_303_715_884_105_727_i128
      ))
    );
    assert_parse!(
      le_i128(
        &[
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff
        ][..]
      ),
      Ok((&b""[..], -1))
    );
    assert_parse!(
      le_i128(
        &[
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x80
        ][..]
      ),
      Ok((
        &b""[..],
        -170_141_183_460_469_231_731_687_303_715_884_105_728_i128
      ))
    );
  }

  #[test]
  fn be_f32_tests() {
    assert_parse!(be_f32(&[0x00, 0x00, 0x00, 0x00][..]), Ok((&b""[..], 0_f32)));
    assert_parse!(
      be_f32(&[0x4d, 0x31, 0x1f, 0xd8][..]),
      Ok((&b""[..], 185_728_392_f32))
    );
  }

  #[test]
  fn be_f64_tests() {
    assert_parse!(
      be_f64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Ok((&b""[..], 0_f64))
    );
    assert_parse!(
      be_f64(&[0x41, 0xa6, 0x23, 0xfb, 0x10, 0x00, 0x00, 0x00][..]),
      Ok((&b""[..], 185_728_392_f64))
    );
  }

  #[test]
  fn le_f32_tests() {
    assert_parse!(le_f32(&[0x00, 0x00, 0x00, 0x00][..]), Ok((&b""[..], 0_f32)));
    assert_parse!(
      le_f32(&[0xd8, 0x1f, 0x31, 0x4d][..]),
      Ok((&b""[..], 185_728_392_f32))
    );
  }

  #[test]
  fn le_f64_tests() {
    assert_parse!(
      le_f64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]),
      Ok((&b""[..], 0_f64))
    );
    assert_parse!(
      le_f64(&[0x00, 0x00, 0x00, 0x10, 0xfb, 0x23, 0xa6, 0x41][..]),
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
    assert_parse!(hex_u32(&b"12af"[..]), Err(Err::Incomplete(Needed::new(1))));
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
      "12.34",
      "-1.234E-12",
      "-1.234e-12",
      "0.00000000000000000087",
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
      Err(Err::Incomplete(Needed::new(1)))
    );

    let (_i, nan) = float::<_, ()>("NaN").unwrap();
    assert!(nan.is_nan());

    let (_i, inf) = float::<_, ()>("inf").unwrap();
    assert!(inf.is_infinite());
    let (i, inf) = float::<_, ()>("infinity").unwrap();
    assert!(inf.is_infinite());
    assert!(i.is_empty());
  }

  #[test]
  fn configurable_endianness() {
    use crate::number::Endianness;

    fn be_tst16(i: &[u8]) -> IResult<&[u8], u16> {
      u16(Endianness::Big)(i)
    }
    fn le_tst16(i: &[u8]) -> IResult<&[u8], u16> {
      u16(Endianness::Little)(i)
    }
    assert_eq!(be_tst16(&[0x80, 0x00]), Ok((&b""[..], 32_768_u16)));
    assert_eq!(le_tst16(&[0x80, 0x00]), Ok((&b""[..], 128_u16)));

    fn be_tst32(i: &[u8]) -> IResult<&[u8], u32> {
      u32(Endianness::Big)(i)
    }
    fn le_tst32(i: &[u8]) -> IResult<&[u8], u32> {
      u32(Endianness::Little)(i)
    }
    assert_eq!(
      be_tst32(&[0x12, 0x00, 0x60, 0x00]),
      Ok((&b""[..], 302_014_464_u32))
    );
    assert_eq!(
      le_tst32(&[0x12, 0x00, 0x60, 0x00]),
      Ok((&b""[..], 6_291_474_u32))
    );

    fn be_tst64(i: &[u8]) -> IResult<&[u8], u64> {
      u64(Endianness::Big)(i)
    }
    fn le_tst64(i: &[u8]) -> IResult<&[u8], u64> {
      u64(Endianness::Little)(i)
    }
    assert_eq!(
      be_tst64(&[0x12, 0x00, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 1_297_142_246_100_992_000_u64))
    );
    assert_eq!(
      le_tst64(&[0x12, 0x00, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 36_028_874_334_666_770_u64))
    );

    fn be_tsti16(i: &[u8]) -> IResult<&[u8], i16> {
      i16(Endianness::Big)(i)
    }
    fn le_tsti16(i: &[u8]) -> IResult<&[u8], i16> {
      i16(Endianness::Little)(i)
    }
    assert_eq!(be_tsti16(&[0x00, 0x80]), Ok((&b""[..], 128_i16)));
    assert_eq!(le_tsti16(&[0x00, 0x80]), Ok((&b""[..], -32_768_i16)));

    fn be_tsti32(i: &[u8]) -> IResult<&[u8], i32> {
      i32(Endianness::Big)(i)
    }
    fn le_tsti32(i: &[u8]) -> IResult<&[u8], i32> {
      i32(Endianness::Little)(i)
    }
    assert_eq!(
      be_tsti32(&[0x00, 0x12, 0x60, 0x00]),
      Ok((&b""[..], 1_204_224_i32))
    );
    assert_eq!(
      le_tsti32(&[0x00, 0x12, 0x60, 0x00]),
      Ok((&b""[..], 6_296_064_i32))
    );

    fn be_tsti64(i: &[u8]) -> IResult<&[u8], i64> {
      i64(Endianness::Big)(i)
    }
    fn le_tsti64(i: &[u8]) -> IResult<&[u8], i64> {
      i64(Endianness::Little)(i)
    }
    assert_eq!(
      be_tsti64(&[0x00, 0xFF, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 71_881_672_479_506_432_i64))
    );
    assert_eq!(
      le_tsti64(&[0x00, 0xFF, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 36_028_874_334_732_032_i64))
    );
  }

  #[cfg(feature = "std")]
  fn parse_f64(i: &str) -> IResult<&str, f64, ()> {
    use crate::traits::ParseTo;
    match recognize_float_or_exceptions(i) {
      Err(e) => Err(e),
      Ok((i, s)) => {
        if s.is_empty() {
          return Err(Err::Error(()));
        }
        match s.parse_to() {
          Some(n) => Ok((i, n)),
          None => Err(Err::Error(())),
        }
      }
    }
  }

  proptest! {
    #[test]
    #[cfg(feature = "std")]
    fn floats(s in "\\PC*") {
        println!("testing {}", s);
        let res1 = parse_f64(&s);
        let res2 = double::<_, ()>(s.as_str());
        assert_eq!(res1, res2);
    }
  }
}
