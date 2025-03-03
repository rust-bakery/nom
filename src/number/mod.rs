//! Parsers recognizing numbers

use core::{
  marker::PhantomData,
  ops::{Add, BitAnd, BitOrAssign, Not, Shl},
};

use crate::branch::Choice;
use crate::bytes::streaming::tag_no_case;
use crate::character::{Char, Digit1};
use crate::combinator::{Cut, Opt, Recognize};
use crate::{
  branch::alt,
  character::{char, digit1},
  combinator::{cut, map, opt, recognize},
  error::{make_error, ErrorKind, ParseError},
  sequence::pair,
  And, AsBytes, AsChar, Compare, Either, Emit, Err, FloatBits, HasUintCounterpart, IResult, Input,
  IsStreaming, Map, Mode, Needed, Offset, OutputM, OutputMode, PResult, Parser,
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

/// creates a big endian unsigned integer parser
///
/// * `bound`: the number of bytes that will be read
/// * `Uint`: the output type
#[inline]
fn be_uint<I, Uint, E: ParseError<I>>(bound: usize) -> BeUint<Uint, E>
where
  I: Input<Item = u8>,
  Uint: Default + Shl<u8, Output = Uint> + Add<Uint, Output = Uint> + From<u8>,
{
  BeUint {
    bound,
    e: PhantomData,
    u: PhantomData,
  }
}

/// Big endian unsigned integer parser
///
/// See also: [`be_uint`]
pub struct BeUint<Uint, E> {
  bound: usize,
  e: PhantomData<E>,
  u: PhantomData<Uint>,
}

impl<I, Uint, E: ParseError<I>> Parser<I> for BeUint<Uint, E>
where
  I: Input<Item = u8>,
  Uint: Default + Shl<u8, Output = Uint> + Add<Uint, Output = Uint> + From<u8>,
{
  type Output = Uint;
  type Error = E;

  #[inline(always)]
  fn process<OM: OutputMode>(&mut self, input: I) -> PResult<OM, I, Self::Output, Self::Error> {
    if input.input_len() < self.bound {
      if OM::Incomplete::is_streaming() {
        Err(Err::Incomplete(Needed::new(self.bound - input.input_len())))
      } else {
        Err(Err::Error(OM::Error::bind(|| {
          make_error(input, ErrorKind::Eof)
        })))
      }
    } else {
      let res = OM::Output::bind(|| {
        let mut res = Uint::default();

        // special case to avoid shift a byte with overflow
        if self.bound > 1 {
          for byte in input.iter_elements().take(self.bound) {
            res = (res << 8) + byte.into();
          }
        } else {
          for byte in input.iter_elements().take(self.bound) {
            res = byte.into();
          }
        }

        res
      });

      Ok((input.take_from(self.bound), res))
    }
  }
}

/// creates a big endian signed integer parser
///
/// * `bound`: the number of bytes that will be read
/// * `Int`: the output type
#[inline]
pub fn be_int<I, E: ParseError<I>, Int>(bound: usize) -> BeInt<Int, E>
where
  I: Input<Item = u8>,
  Int: HasUintCounterpart,
  Int::Uint: Default
    + Shl<u8, Output = Int::Uint>
    + Add<Output = Int::Uint>
    + BitAnd<Output = Int::Uint>
    + BitOrAssign
    + Not<Output = Int::Uint>
    + PartialEq
    + From<u8>
    + Clone,
{
  BeInt {
    bound,
    e: PhantomData,
    u: PhantomData,
  }
}

/// Big endian signed integer parser
///
/// See also: [`be_int`]
pub struct BeInt<Int, E> {
  bound: usize,
  e: PhantomData<E>,
  u: PhantomData<Int>,
}

impl<I, Int, E: ParseError<I>> Parser<I> for BeInt<Int, E>
where
  I: Input<Item = u8>,
  Int: HasUintCounterpart,
  Int::Uint: Default
    + Shl<u8, Output = Int::Uint>
    + Add<Output = Int::Uint>
    + BitAnd<Output = Int::Uint>
    + BitOrAssign
    + Not<Output = Int::Uint>
    + PartialEq
    + From<u8>
    + Clone,
{
  type Output = Int;
  type Error = E;

  #[inline(always)]
  fn process<OM: crate::OutputMode>(
    &mut self,
    input: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    if input.input_len() < self.bound {
      if OM::Incomplete::is_streaming() {
        Err(Err::Incomplete(Needed::new(self.bound - input.input_len())))
      } else {
        Err(Err::Error(OM::Error::bind(|| {
          make_error(input, ErrorKind::Eof)
        })))
      }
    } else {
      let res = OM::Output::bind(|| {
        let zero = <Int::Uint as Default>::default();

        let mut res = zero.clone();

        // special case to avoid shift a byte with overflow
        if self.bound > 1 {
          for byte in input.iter_elements().take(self.bound) {
            res = (res << 8) + byte.into();
          }
        } else {
          for byte in input.iter_elements().take(self.bound) {
            res = byte.into();
          }
        }

        // Manual sign extension
        if self.bound < size_of::<Int>() {
          let one: Int::Uint = 1.into();

          let bits_width = (self.bound * 8) as u8;
          let sign_bit: Int::Uint = one << (bits_width - 1);

          if res.clone() & sign_bit != zero {
            let sign_extension_mask: Int::Uint = !zero << bits_width;
            res |= sign_extension_mask;
          }
        }

        Int::from_uint(res)
      });

      Ok((input.take_from(self.bound), res))
    }
  }
}

/// Recognizes an unsigned 1-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_u8;
///
/// let parser = |s| {
///   be_u8::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"\x01abcd"[..], 0x00)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn be_u8<I, E: ParseError<I>>() -> BeUint<u8, E>
where
  I: Input<Item = u8>,
{
  be_uint(1)
}

/// Recognizes a big endian unsigned 2-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_u16;
///
/// let parser = |s| {
///   be_u16::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"abcd"[..], 0x0001)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn be_u16<I, E: ParseError<I>>() -> BeUint<u16, E>
where
  I: Input<Item = u8>,
{
  be_uint(2)
}

/// Recognizes a big endian unsigned 3-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_u24;
///
/// let parser = |s| {
///   be_u24::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02abcd"[..]), Ok((&b"abcd"[..], 0x000102)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn be_u24<I, E: ParseError<I>>() -> BeUint<u32, E>
where
  I: Input<Item = u8>,
{
  be_uint(3)
}

/// Recognizes a big endian unsigned 4-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_u32;
///
/// let parser = |s| {
///   be_u32::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03abcd"[..]), Ok((&b"abcd"[..], 0x00010203)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn be_u32<I, E: ParseError<I>>() -> BeUint<u32, E>
where
  I: Input<Item = u8>,
{
  be_uint(4)
}

/// Recognizes a big endian unsigned 8-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_u64;
///
/// let parser = |s| {
///   be_u64::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcd"[..]), Ok((&b"abcd"[..], 0x0001020304050607)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn be_u64<I, E: ParseError<I>>() -> BeUint<u64, E>
where
  I: Input<Item = u8>,
{
  be_uint(8)
}

/// Recognizes a big endian unsigned 16-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_u128;
///
/// let parser = |s| {
///   be_u128::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15abcd"[..]), Ok((&b"abcd"[..], 0x00010203040506070809101112131415)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn be_u128<I, E: ParseError<I>>() -> BeUint<u128, E>
where
  I: Input<Item = u8>,
{
  be_uint(16)
}

/// Recognizes a signed 1-byte integer.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_i8;
///
/// let mut parser = be_i8::<_, (_, ErrorKind)>();
///
/// assert_eq!(parser.parse(&b"\x00\x01abcd"[..]), Ok((&b"\x01abcd"[..], 0x00)));
/// assert_eq!(parser.parse(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn be_i8<I, E: ParseError<I>>() -> BeInt<i8, E>
where
  I: Input<Item = u8>,
{
  be_int(1)
}

/// Recognizes a big endian signed 2-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_i16;
///
/// let mut parser = be_i16::<_, (_, ErrorKind)>();
///
/// assert_eq!(parser.parse(&b"\x00\x01abcd"[..]), Ok((&b"abcd"[..], 0x0001)));
/// assert_eq!(parser.parse(&b""[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn be_i16<I, E: ParseError<I>>() -> BeInt<i16, E>
where
  I: Input<Item = u8>,
{
  be_int(2)
}

/// Recognizes a big endian signed 3-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_i24;
///
/// let mut parser = be_i24::<_, (_, ErrorKind)>();
///
/// assert_eq!(parser.parse(&b"\x00\x01\x02abcd"[..]), Ok((&b"abcd"[..], 0x000102)));
/// assert_eq!(parser.parse(&b"\x80\x01\x02abcd"[..]), Ok((&b"abcd"[..], 0xFF800102_u32 as i32)));
/// assert_eq!(parser.parse(&b""[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn be_i24<I, E: ParseError<I>>() -> BeInt<i32, E>
where
  I: Input<Item = u8>,
{
  be_int(3)

  // // Same as the unsigned version but we need to sign-extend manually here
  // be_u24().map(|x| {
  //   if x & 0x80_00_00 != 0 {
  //     (x | 0xff_00_00_00) as i32
  //   } else {
  //     x as i32
  //   }
  // })
}

/// Recognizes a big endian signed 4-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_i32;
///
/// let mut parser = be_i32::<_, (_, ErrorKind)>();
///
/// assert_eq!(parser.parse(&b"\x00\x01\x02\x03abcd"[..]), Ok((&b"abcd"[..], 0x00010203)));
/// assert_eq!(parser.parse(&b""[..]), Err(Err::Incomplete(Needed::new(4))));
/// ```
#[inline]
pub fn be_i32<I, E: ParseError<I>>() -> BeInt<i32, E>
where
  I: Input<Item = u8>,
{
  be_int(4)
}

/// Recognizes a big endian signed 8-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_i64;
///
/// let mut parser = be_i64::<_, (_, ErrorKind)>();
///
/// assert_eq!(parser.parse(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcd"[..]), Ok((&b"abcd"[..], 0x0001020304050607)));
/// assert_eq!(parser.parse(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn be_i64<I, E: ParseError<I>>() -> BeInt<i64, E>
where
  I: Input<Item = u8>,
{
  be_int(8)
}

/// Recognizes a big endian signed 16-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_i128;
///
/// let mut parser = be_i128::<_, (_, ErrorKind)>();
///
/// assert_eq!(parser.parse(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15abcd"[..]), Ok((&b"abcd"[..], 0x00010203040506070809101112131415)));
/// assert_eq!(parser.parse(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn be_i128<I, E: ParseError<I>>() -> BeInt<i128, E>
where
  I: Input<Item = u8>,
{
  be_int(16)
}

/// creates a little endian unsigned integer parser
///
/// * `bound`: the number of bytes that will be read
/// * `Uint`: the output type
#[inline]
fn le_uint<I, Uint, E: ParseError<I>>(bound: usize) -> LeUint<Uint, E>
where
  I: Input<Item = u8>,
  Uint: Default + Shl<u8, Output = Uint> + Add<Uint, Output = Uint> + From<u8>,
{
  LeUint {
    bound,
    e: PhantomData,
    u: PhantomData,
  }
}

/// Little endian unsigned integer parser
///
/// See also: [`le_uint`]
pub struct LeUint<Uint, E> {
  bound: usize,
  e: PhantomData<E>,
  u: PhantomData<Uint>,
}

impl<I, Uint, E: ParseError<I>> Parser<I> for LeUint<Uint, E>
where
  I: Input<Item = u8>,
  Uint: Default + Shl<u8, Output = Uint> + Add<Uint, Output = Uint> + From<u8>,
{
  type Output = Uint;
  type Error = E;

  #[inline(always)]
  fn process<OM: crate::OutputMode>(
    &mut self,
    input: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    if input.input_len() < self.bound {
      if OM::Incomplete::is_streaming() {
        Err(Err::Incomplete(Needed::new(self.bound - input.input_len())))
      } else {
        Err(Err::Error(OM::Error::bind(|| {
          make_error(input, ErrorKind::Eof)
        })))
      }
    } else {
      let res = OM::Output::bind(|| {
        let mut res = Uint::default();
        for (index, byte) in input.iter_elements().take(self.bound).enumerate() {
          res = res + (Uint::from(byte) << (8 * index as u8));
        }

        res
      });

      Ok((input.take_from(self.bound), res))
    }
  }
}

/// creates a little endian unsigned integer parser
///
/// * `bound`: the number of bytes that will be read
/// * `Uint`: the output type
#[inline]
fn le_int<I, Int, E: ParseError<I>>(bound: usize) -> LeInt<Int, E>
where
  I: Input<Item = u8>,
  Int: HasUintCounterpart,
  Int::Uint: Default
    + Shl<u8, Output = Int::Uint>
    + Add<Output = Int::Uint>
    + Not<Output = Int::Uint>
    + BitAnd<Output = Int::Uint>
    + BitOrAssign
    + PartialEq
    + From<u8>
    + Clone,
{
  LeInt {
    bound,
    e: PhantomData,
    u: PhantomData,
  }
}

/// Little endian signed integer parser
///
/// See also: [`le_int`]
pub struct LeInt<Int, E> {
  bound: usize,
  e: PhantomData<E>,
  u: PhantomData<Int>,
}

impl<I, Int, E: ParseError<I>> Parser<I> for LeInt<Int, E>
where
  I: Input<Item = u8>,
  Int: HasUintCounterpart,
  Int::Uint: Default
    + Shl<u8, Output = Int::Uint>
    + Add<Output = Int::Uint>
    + Not<Output = Int::Uint>
    + BitAnd<Output = Int::Uint>
    + BitOrAssign
    + PartialEq
    + From<u8>
    + Clone,
{
  type Output = Int;
  type Error = E;

  #[inline(always)]
  fn process<OM: crate::OutputMode>(
    &mut self,
    input: I,
  ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
    if input.input_len() < self.bound {
      if OM::Incomplete::is_streaming() {
        Err(Err::Incomplete(Needed::new(self.bound - input.input_len())))
      } else {
        Err(Err::Error(OM::Error::bind(|| {
          make_error(input, ErrorKind::Eof)
        })))
      }
    } else {
      let res = OM::Output::bind(|| {
        let zero: Int::Uint = <Int::Uint as Default>::default();

        let mut res = zero.clone();
        for (index, byte) in input.iter_elements().take(self.bound).enumerate() {
          res = res + (<Int::Uint as From<u8>>::from(byte) << (8 * index as u8));
        }

        if self.bound < size_of::<Int>() {
          let one: Int::Uint = 1.into();

          let bits_width = (self.bound * 8) as u8;
          let sign_bit: Int::Uint = one << (bits_width - 1);

          if res.clone() & sign_bit != zero {
            let sign_extension_mask: Int::Uint = !zero << bits_width;
            res |= sign_extension_mask;
          }
        }

        Int::from_uint(res)
      });

      Ok((input.take_from(self.bound), res))
    }
  }
}

/// Recognizes an unsigned 1-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_u8;
///
/// let mut parser = le_u8::<_, (_, ErrorKind)>();
///
/// assert_eq!(parser.parse(&b"\x00\x01abcd"[..]), Ok((&b"\x01abcd"[..], 0x00)));
/// assert_eq!(parser.parse(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn le_u8<I, E: ParseError<I>>() -> LeUint<u8, E>
where
  I: Input<Item = u8>,
{
  le_uint(1)
}

/// Recognizes a little endian unsigned 2-byte integer.
///
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_u16;
///
/// let parser = |s| {
///   le_u16::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"abcd"[..], 0x0100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn le_u16<I, E: ParseError<I>>() -> LeUint<u16, E>
where
  I: Input<Item = u8>,
{
  le_uint(2)
}

/// Recognizes a little endian unsigned 3-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_u24;
///
/// let parser = |s| {
///   le_u24::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02abcd"[..]), Ok((&b"abcd"[..], 0x020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn le_u24<I, E: ParseError<I>>() -> LeUint<u32, E>
where
  I: Input<Item = u8>,
{
  le_uint(3)
}

/// Recognizes a little endian unsigned 4-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_u32;
///
/// let parser = |s| {
///   le_u32::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03abcd"[..]), Ok((&b"abcd"[..], 0x03020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn le_u32<I, E: ParseError<I>>() -> LeUint<u32, E>
where
  I: Input<Item = u8>,
{
  le_uint(4)
}

/// Recognizes a little endian unsigned 8-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_u64;
///
/// let parser = |s| {
///   le_u64::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcd"[..]), Ok((&b"abcd"[..], 0x0706050403020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn le_u64<I, E: ParseError<I>>() -> LeUint<u64, E>
where
  I: Input<Item = u8>,
{
  le_uint(8)
}

/// Recognizes a little endian unsigned 16-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_u128;
///
/// let mut parser = |s| {
///   le_u128::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15abcd"[..]), Ok((&b"abcd"[..], 0x15141312111009080706050403020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn le_u128<I, E: ParseError<I>>() -> LeUint<u128, E>
where
  I: Input<Item = u8>,
{
  le_uint(16)
}

/// Recognizes a signed 1-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_i8;
///
/// let mut parser = le_i8::<_, (_, ErrorKind)>();
///
/// assert_eq!(parser.parse(&b"\x00\x01abcd"[..]), Ok((&b"\x01abcd"[..], 0x00)));
/// assert_eq!(parser.parse(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn le_i8<I, E: ParseError<I>>() -> LeInt<i8, E>
where
  I: Input<Item = u8>,
{
  le_int(1)
}

/// Recognizes a little endian signed 2-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_i16;
///
/// let parser = |s| {
///   le_i16::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01abcd"[..]), Ok((&b"abcd"[..], 0x0100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn le_i16<I, E: ParseError<I>>() -> LeInt<i16, E>
where
  I: Input<Item = u8>,
{
  le_int(2)
}

/// Recognizes a little endian signed 3-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_i24;
///
/// let parser = |s| {
///   le_i24::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02abcd"[..]), Ok((&b"abcd"[..], 0x020100)));
/// assert_eq!(parser(&b"\x01\x02\x80abcd"[..]), Ok((&b"abcd"[..], 0xFF800201_u32 as i32)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn le_i24<I, E: ParseError<I>>() -> LeInt<i32, E>
where
  I: Input<Item = u8>,
{
  le_int(3)
}

/// Recognizes a little endian signed 4-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_i32;
///
/// let parser = |s| {
///   le_i32::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03abcd"[..]), Ok((&b"abcd"[..], 0x03020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn le_i32<I, E: ParseError<I>>() -> LeInt<i32, E>
where
  I: Input<Item = u8>,
{
  le_int(4)
}

/// Recognizes a little endian signed 8-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_i64;
///
/// let parser = |s| {
///   le_i64::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcd"[..]), Ok((&b"abcd"[..], 0x0706050403020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn le_i64<I, E: ParseError<I>>() -> LeInt<i64, E>
where
  I: Input<Item = u8>,
{
  le_int(8)
}

/// Recognizes a little endian signed 16-byte integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_i128;
///
/// let parser = |s| {
///   le_i128::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15abcd"[..]), Ok((&b"abcd"[..], 0x15141312111009080706050403020100)));
/// assert_eq!(parser(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn le_i128<I, E: ParseError<I>>() -> LeInt<i128, E>
where
  I: Input<Item = u8>,
{
  le_int(16)
}

/// Recognizes an unsigned 1-byte integer
///
/// Note that endianness does not apply to 1-byte numbers.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::u8;
///
/// let parser = |s| {
///   u8::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x03abcefg"[..]), Ok((&b"\x03abcefg"[..], 0x00)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn u8<I, E: ParseError<I>>() -> BeUint<u8, E>
where
  I: Input<Item = u8>,
{
  be_u8()
}

/// Recognizes an unsigned 2-byte integer
///
/// If the parameter is [`Endianness::Big`], parse a big endian u16 integer,
/// otherwise if [`Endianness::Little`] parse a little endian u16 integer.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::u16;
///
/// let be_u16 = |s| {
///   u16::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_u16(&b"\x00\x03abcefg"[..]), Ok((&b"abcefg"[..], 0x0003)));
/// assert_eq!(be_u16(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
///
/// let le_u16 = |s| {
///   u16::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_u16(&b"\x00\x03abcefg"[..]), Ok((&b"abcefg"[..], 0x0300)));
/// assert_eq!(le_u16(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn u16<I, E: ParseError<I>>(endian: Endianness) -> Either<BeUint<u16, E>, LeUint<u16, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_u16()),
    Endianness::Little => Either::Right(le_u16()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_u16()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_u16()),
  }
}

/// Recognizes an unsigned 3-byte integer
///
/// If the parameter is [`Endianness::Big`], parse a big endian u24 integer,
/// otherwise if [`Endianness::Little`] parse a little endian u24 integer.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::u24;
///
/// let be_u24 = |s| {
///   u24::<_,(_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_u24(&b"\x00\x03\x05abcefg"[..]), Ok((&b"abcefg"[..], 0x000305)));
/// assert_eq!(be_u24(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
///
/// let le_u24 = |s| {
///   u24::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_u24(&b"\x00\x03\x05abcefg"[..]), Ok((&b"abcefg"[..], 0x050300)));
/// assert_eq!(le_u24(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn u24<I, E: ParseError<I>>(endian: Endianness) -> Either<BeUint<u32, E>, LeUint<u32, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_u24()),
    Endianness::Little => Either::Right(le_u24()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_u24()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_u24()),
  }
}

/// Recognizes an unsigned 4-byte integer
///
/// If the parameter is [`Endianness::Big`], parse a big endian u32 integer,
/// otherwise if [`Endianness::Little`] parse a little endian u32 integer.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::u32;
///
/// let be_u32 = |s| {
///   u32::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_u32(&b"\x00\x03\x05\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x00030507)));
/// assert_eq!(be_u32(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
///
/// let le_u32 = |s| {
///   u32::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_u32(&b"\x00\x03\x05\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x07050300)));
/// assert_eq!(le_u32(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn u32<I, E: ParseError<I>>(endian: Endianness) -> Either<BeUint<u32, E>, LeUint<u32, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_u32()),
    Endianness::Little => Either::Right(le_u32()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_u32()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_u32()),
  }
}

/// Recognizes an unsigned 8-byte integer
///
/// If the parameter is [`Endianness::Big`], parse a big endian u64 integer,
/// otherwise if [`Endianness::Little`] parse a little endian u64 integer.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::u64;
///
/// let be_u64 = |s| {
///   u64::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_u64(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x0001020304050607)));
/// assert_eq!(be_u64(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
///
/// let le_u64 = |s| {
///   u64::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_u64(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x0706050403020100)));
/// assert_eq!(le_u64(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn u64<I, E: ParseError<I>>(endian: Endianness) -> Either<BeUint<u64, E>, LeUint<u64, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_u64()),
    Endianness::Little => Either::Right(le_u64()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_u64()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_u64()),
  }
}

/// Recognizes an unsigned 16-byte integer
///
/// If the parameter is [`Endianness::Big`], parse a big endian u128 integer,
/// otherwise if [`Endianness::Little`] parse a little endian u128 integer.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::u128;
///
/// let be_u128 = |s| {
///   u128::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_u128(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x00010203040506070001020304050607)));
/// assert_eq!(be_u128(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
///
/// let le_u128 = |s| {
///   u128::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_u128(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x07060504030201000706050403020100)));
/// assert_eq!(le_u128(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn u128<I, E: ParseError<I>>(endian: Endianness) -> Either<BeUint<u128, E>, LeUint<u128, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_u128()),
    Endianness::Little => Either::Right(le_u128()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_u128()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_u128()),
  }
}

/// Recognizes a signed 1-byte integer
///
/// Note that endianness does not apply to 1-byte numbers.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::i8;
///
/// let parser = |s| {
///   i8::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&b"\x00\x03abcefg"[..]), Ok((&b"\x03abcefg"[..], 0x00)));
/// assert_eq!(parser(&b""[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn i8<I, E: ParseError<I>>() -> BeInt<i8, E>
where
  I: Input<Item = u8>,
{
  be_i8()
}

/// Recognizes a signed 2-byte integer
///
/// If the parameter is [`Endianness::Big`], parse a big endian i16 integer,
/// otherwise if [`Endianness::Little`] parse a little endian i16 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::i16;
///
/// let be_i16 = |s| {
///   i16::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_i16(&b"\x00\x03abcefg"[..]), Ok((&b"abcefg"[..], 0x0003)));
/// assert_eq!(be_i16(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
///
/// let le_i16 = |s| {
///   i16::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_i16(&b"\x00\x03abcefg"[..]), Ok((&b"abcefg"[..], 0x0300)));
/// assert_eq!(le_i16(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn i16<I, E: ParseError<I>>(endian: Endianness) -> Either<BeInt<i16, E>, LeInt<i16, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_i16()),
    Endianness::Little => Either::Right(le_i16()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_i16()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_i16()),
  }
}

/// Recognizes a signed 3-byte integer
///
/// If the parameter is `nom::number::Endianness::Big`, parse a big endian i24 integer,
/// otherwise if `nom::number::Endianness::Little` parse a little endian i24 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::i24;
///
/// let be_i24 = |s| {
///   i24::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_i24(&b"\x00\x03\x05abcefg"[..]), Ok((&b"abcefg"[..], 0x000305)));
/// assert_eq!(be_i24(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
///
/// let le_i24 = |s| {
///   i24::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_i24(&b"\x00\x03\x05abcefg"[..]), Ok((&b"abcefg"[..], 0x050300)));
/// assert_eq!(le_i24(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(2))));
/// ```
#[inline]
pub fn i24<I, E: ParseError<I>>(endian: Endianness) -> Either<BeInt<i32, E>, LeInt<i32, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_i24()),
    Endianness::Little => Either::Right(le_i24()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_i24()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_i24()),
  }
}

/// Recognizes a signed 4-byte integer
///
/// If the parameter is [`Endianness::Big`], parse a big endian i32 integer,
/// otherwise if [`Endianness::Little`] parse a little endian i32 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::i32;
///
/// let be_i32 = |s| {
///   i32::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_i32(&b"\x00\x03\x05\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x00030507)));
/// assert_eq!(be_i32(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
///
/// let le_i32 = |s| {
///   i32::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_i32(&b"\x00\x03\x05\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x07050300)));
/// assert_eq!(le_i32(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn i32<I, E: ParseError<I>>(endian: Endianness) -> Either<BeInt<i32, E>, LeInt<i32, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_i32()),
    Endianness::Little => Either::Right(le_i32()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_i32()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_i32()),
  }
}

/// Recognizes a signed 8-byte integer
///
/// If the parameter is [`Endianness::Big`], parse a big endian i64 integer,
/// otherwise if [`Endianness::Little`] parse a little endian i64 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::i64;
///
/// let be_i64 = |s| {
///   i64::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_i64(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x0001020304050607)));
/// assert_eq!(be_i64(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
///
/// let le_i64 = |s| {
///   i64::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_i64(&b"\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x0706050403020100)));
/// assert_eq!(le_i64(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn i64<I, E: ParseError<I>>(endian: Endianness) -> Either<BeInt<i64, E>, LeInt<i64, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_i64()),
    Endianness::Little => Either::Right(le_i64()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_i64()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_i64()),
  }
}

/// Recognizes a signed 16-byte integer
///
/// If the parameter is [`Endianness::Big`], parse a big endian i128 integer,
/// otherwise if [`Endianness::Little`] parse a little endian i128 integer.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::i128;
///
/// let be_i128 = |s| {
///   i128::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_i128(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x00010203040506070001020304050607)));
/// assert_eq!(be_i128(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
///
/// let le_i128 = |s| {
///   i128::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_i128(&b"\x00\x01\x02\x03\x04\x05\x06\x07\x00\x01\x02\x03\x04\x05\x06\x07abcefg"[..]), Ok((&b"abcefg"[..], 0x07060504030201000706050403020100)));
/// assert_eq!(le_i128(&b"\x01"[..]), Err(Err::Incomplete(Needed::new(15))));
/// ```
#[inline]
pub fn i128<I, E: ParseError<I>>(endian: Endianness) -> Either<BeInt<i128, E>, LeInt<i128, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_i128()),
    Endianness::Little => Either::Right(le_i128()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_i128()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_i128()),
  }
}

/// Recognizes a big endian 4-byte floating point number.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_f32;
///
/// let parser = |s| {
///   be_f32::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&[0x40, 0x29, 0x00, 0x00][..]), Ok((&b""[..], 2.640625)));
/// assert_eq!(parser(&[0x01][..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn be_f32<I, E: ParseError<I>>() -> BeFloat<u32, E>
where
  I: Input<Item = u8>,
{
  BeFloat(be_u32())
}

/// Recognizes a big endian 8-byte floating point number.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::be_f64;
///
/// let parser = |s| {
///   be_f64::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&[0x40, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(parser(&[0x01][..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn be_f64<I, E: ParseError<I>>() -> BeFloat<u64, E>
where
  I: Input<Item = u8>,
{
  BeFloat(be_u64())
}

/// Parser for big endian 4-byte floating point numbers.
pub struct BeFloat<Uint, E>(BeUint<Uint, E>);

impl<I, E, Uint> Parser<I> for BeFloat<Uint, E>
where
  I: Input<Item = u8>,
  E: ParseError<I>,
  Uint: FloatBits,
  BeUint<Uint, E>: Parser<I, Output = Uint, Error = E>,
{
  type Output = Uint::Float;
  type Error = E;

  #[inline]
  fn process<OM: OutputMode>(&mut self, input: I) -> PResult<OM, I, Self::Output, Self::Error> {
    self
      .0
      .process::<OM>(input)
      .map(|(i, o)| (i, OM::Output::map(o, Uint::into_float)))
  }
}

/// Recognizes a little endian 4-byte floating point number.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_f32;
///
/// let parser = |s| {
///   le_f32::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&[0x00, 0x00, 0x48, 0x41][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(parser(&[0x01][..]), Err(Err::Incomplete(Needed::new(3))));
/// ```
#[inline]
pub fn le_f32<I, E: ParseError<I>>() -> LeFloat<u32, E>
where
  I: Input<Item = u8>,
{
  LeFloat(le_u32())
}

/// Recognizes a little endian 8-byte floating point number.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::le_f64;
///
/// let parser = |s| {
///   le_f64::<_, (_, ErrorKind)>().parse(s)
/// };
///
/// assert_eq!(parser(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x41][..]), Ok((&b""[..], 3145728.0)));
/// assert_eq!(parser(&[0x01][..]), Err(Err::Incomplete(Needed::new(7))));
/// ```
#[inline]
pub fn le_f64<I, E: ParseError<I>>() -> LeFloat<u64, E>
where
  I: Input<Item = u8>,
{
  LeFloat(le_u64())
}

/// Parser for big endian 4-byte floating point numbers.
pub struct LeFloat<Uint, E>(LeUint<Uint, E>);

impl<I, E, Uint> Parser<I> for LeFloat<Uint, E>
where
  I: Input<Item = u8>,
  E: ParseError<I>,
  Uint: FloatBits,
  LeUint<Uint, E>: Parser<I, Output = Uint, Error = E>,
{
  type Output = Uint::Float;
  type Error = E;

  #[inline]
  fn process<OM: OutputMode>(&mut self, input: I) -> PResult<OM, I, Self::Output, Self::Error> {
    self
      .0
      .process::<OM>(input)
      .map(|(i, o)| (i, OM::Output::map(o, Uint::into_float)))
  }
}

/// Recognizes a 4-byte floating point number
///
/// If the parameter is [`Endianness::Big`], parse a big endian f32 float,
/// otherwise if [`Endianness::Little`] parse a little endian f32 float.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::f32;
///
/// let be_f32 = |s| {
///   f32::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_f32(&[0x41, 0x48, 0x00, 0x00][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(be_f32(&b"abc"[..]), Err(Err::Incomplete(Needed::new(1))));
///
/// let le_f32 = |s| {
///   f32::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_f32(&[0x00, 0x00, 0x48, 0x41][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(le_f32(&b"abc"[..]), Err(Err::Incomplete(Needed::new(1))));
/// ```
#[inline]
pub fn f32<I, E: ParseError<I>>(endian: Endianness) -> Either<BeFloat<u32, E>, LeFloat<u32, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_f32()),
    Endianness::Little => Either::Right(le_f32()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_f32()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_f32()),
  }
}

/// Recognizes an 8-byte floating point number
///
/// If the parameter is [`Endianness::Big`], parse a big endian f64 float,
/// otherwise if [`Endianness::Little`] parse a little endian f64 float.
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if there is not enough data.
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// # use nom::Needed::Size;
/// use nom::number::f64;
///
/// let be_f64 = |s| {
///   f64::<_, (_, ErrorKind)>(nom::number::Endianness::Big).parse(s)
/// };
///
/// assert_eq!(be_f64(&[0x40, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(be_f64(&b"abc"[..]), Err(Err::Incomplete(Needed::new(5))));
///
/// let le_f64 = |s| {
///   f64::<_, (_, ErrorKind)>(nom::number::Endianness::Little).parse(s)
/// };
///
/// assert_eq!(le_f64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x29, 0x40][..]), Ok((&b""[..], 12.5)));
/// assert_eq!(le_f64(&b"abc"[..]), Err(Err::Incomplete(Needed::new(5))));
/// ```
#[inline]
pub fn f64<I, E: ParseError<I>>(endian: Endianness) -> Either<BeFloat<u64, E>, LeFloat<u64, E>>
where
  I: Input<Item = u8>,
{
  match endian {
    Endianness::Big => Either::Left(be_f64()),
    Endianness::Little => Either::Right(le_f64()),
    #[cfg(target_endian = "big")]
    Endianness::Native => Either::Left(be_f64()),
    #[cfg(target_endian = "little")]
    Endianness::Native => Either::Right(le_f64()),
  }
}

/// Recognizes a floating point number in text format and returns the corresponding part of the input.
///
/// *Streaming version*: Will return `Err(nom::Err::Incomplete(_))` if it reaches the end of input.
///
/// ```rust
/// # use nom::{Err, error::ErrorKind, Needed, Parser};
/// use nom::number::recognize_float;
///
/// let parser = |s| {
///   recognize_float().parse(s)
/// };
///
/// assert_eq!(parser("11e-1;"), Ok((";", "11e-1")));
/// assert_eq!(parser("123E-02;"), Ok((";", "123E-02")));
/// assert_eq!(parser("123K-01"), Ok(("K-01", "123")));
/// assert_eq!(parser("abc"), Err(Err::Error(("abc", ErrorKind::Char))));
/// ```
#[rustfmt::skip]
pub fn recognize_float<I, E: ParseError<I>>() -> RecognizeFloat<I, E>
where
  I: Clone + Offset,
  I: Input,
  <I as Input>::Item: AsChar,
{
  recognize((
      opt(alt((char('+'), char('-')))),
      alt((
        map((digit1(), opt(pair(char('.'), opt(digit1())))), drop),
        map((char('.'), digit1()), drop)
      )),
      opt((
        alt((char('e'), char('E'))),
        opt(alt((char('+'), char('-')))),
        cut(digit1())
      ))
  ))
}

/// Parser implementation for the [`recognize_float_or_exceptions`]
pub type RecognizeFloat<I, E> = Recognize<(
  Opt<Choice<(Char<E>, Char<E>)>>,
  Choice<(
    Map<MantissaWithWhole<E>, fn(<MantissaWithWhole<E> as Parser<I>>::Output)>,
    Map<MantissaWithoutWhole<E>, fn(<MantissaWithoutWhole<E> as Parser<I>>::Output)>,
  )>,
  Opt<(
    Choice<(Char<E>, Char<E>)>,
    Opt<Choice<(Char<E>, Char<E>)>>,
    Cut<Digit1<E>>,
  )>,
)>;

/// Parser implementation for the mantissa part of the float number, containing the whole part
pub type MantissaWithWhole<E> = (Digit1<E>, Opt<And<Char<E>, Opt<Digit1<E>>>>);

/// Parser implementation for the mantissa part of the float number, without the whole part
pub type MantissaWithoutWhole<E> = (Char<E>, Digit1<E>);

/// Float number text parser that also recognizes "nan", "infinity" and "inf" (case-insensitive)
pub fn recognize_float_or_exceptions<I, E: ParseError<I>>() -> RecognizeFloatOrExceptions<I, E>
where
  I: Clone + Offset,
  I: Input + Compare<&'static str>,
  <I as Input>::Item: AsChar,
{
  alt((
    recognize_float::<_, E>(),
    |i: I| {
      tag_no_case::<_, _, E>("nan")(i.clone())
        .map_err(|_| Err::Error(E::from_error_kind(i, ErrorKind::Float)))
    },
    |i: I| {
      tag_no_case::<_, _, E>("infinity")(i.clone())
        .map_err(|_| Err::Error(E::from_error_kind(i, ErrorKind::Float)))
    },
    |i: I| {
      tag_no_case::<_, _, E>("inf")(i.clone())
        .map_err(|_| Err::Error(E::from_error_kind(i, ErrorKind::Float)))
    },
  ))
}

/// Parser implementation for the [`recognize_float_or_exceptions`]
pub type RecognizeFloatOrExceptions<I, E> = Choice<(
  RecognizeFloat<I, E>,
  fn(I) -> IResult<I, I, E>,
  fn(I) -> IResult<I, I, E>,
  fn(I) -> IResult<I, I, E>,
)>;

/// Single precision floating point number parser from a text
pub fn float<T, E: ParseError<T>>() -> Float<f32, E>
where
  T: Clone + Offset,
  T: Input + crate::traits::ParseTo<f32> + Compare<&'static str>,
  <T as Input>::Item: AsChar + Clone,
  T: AsBytes,
  T: for<'a> Compare<&'a [u8]>,
{
  Float {
    o: PhantomData,
    e: PhantomData,
  }
}

/// Double precision floating point number parser from a text
pub fn double<T, E: ParseError<T>>() -> Float<f64, E>
where
  T: Clone + Offset,
  T: Input + crate::traits::ParseTo<f64> + Compare<&'static str>,
  <T as Input>::Item: AsChar + Clone,
  T: AsBytes,
  T: for<'a> Compare<&'a [u8]>,
{
  Float {
    o: PhantomData,
    e: PhantomData,
  }
}

/// `f64` parser from a text
pub struct Float<O, E> {
  o: PhantomData<O>,
  e: PhantomData<E>,
}

impl<I, O, E: ParseError<I>> Parser<I> for Float<O, E>
where
  I: Clone + Offset,
  I: Input + crate::traits::ParseTo<O> + Compare<&'static str>,
  <I as Input>::Item: AsChar + Clone,
  I: AsBytes,
  I: for<'a> Compare<&'a [u8]>,
{
  type Output = O;
  type Error = E;

  fn process<OM: OutputMode>(&mut self, input: I) -> PResult<OM, I, Self::Output, Self::Error> {
    let (i, s) =
      recognize_float_or_exceptions().process::<OutputM<Emit, OM::Error, OM::Incomplete>>(input)?;

    match s.parse_to() {
      Some(f) => Ok((i, OM::Output::bind(|| f))),
      None => Err(Err::Error(OM::Error::bind(|| {
        E::from_error_kind(i, ErrorKind::Float)
      }))),
    }
  }
}

#[cfg(test)]
#[cfg(feature = "std")]
mod tests {
  use super::*;
  use crate::error::ErrorKind;
  use crate::internal::Err;

  macro_rules! assert_parse(
    ($left: expr, $right: expr) => {
      let res: $crate::IResult<_, _, (_, ErrorKind)> = $left;
      assert_eq!(res, $right);
    };
  );

  #[test]
  fn test_be_i24() {
    let mut parser = be_i24::<_, (_, ErrorKind)>();

    assert_eq!(
      parser.parse(&b"\x00\x01\x02abcd"[..]),
      Ok((&b"abcd"[..], 0x000102))
    );
    assert_eq!(
      parser.parse(&b"\x80\x01\x02abcd"[..]),
      Ok((&b"abcd"[..], 0xFF800102_u32 as i32))
    );
    assert_eq!(parser.parse(&b""[..]), Err(Err::Incomplete(Needed::new(3))));
  }

  #[test]
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
    let (i, inf) = float::<_, ()>("infinity").unwrap();
    assert!(inf.is_infinite());
    assert!(i.is_empty());*/
  }
}
