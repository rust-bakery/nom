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
use traits::{AsChar, InputIter, InputLength, InputTakeAtPosition};
use traits::{need_more, need_more_err, AtEof, ParseTo};
use lib::std::ops::{Range, RangeFrom, RangeTo};
use traits::{Compare, CompareResult, Offset, Slice};
use util::ErrorKind;
use lib::std::mem::transmute;

#[cfg(feature = "alloc")]
#[inline]
pub fn tag_cl<'a, 'b>(rec: &'a [u8]) -> Box<Fn(&'b [u8]) -> IResult<&'b [u8], &'b [u8]> + 'a> {
  Box::new(move |i: &'b [u8]| -> IResult<&'b [u8], &'b [u8]> {
    if i.len() >= rec.len() && &i[0..rec.len()] == rec {
      Ok((&i[rec.len()..], &i[0..rec.len()]))
    } else {
      let e: ErrorKind<u32> = ErrorKind::TagClosure;
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

pub fn crlf<T>(input: T) -> IResult<T, T>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + AtEof,
  T: Compare<&'static str>,
{
  match input.compare("\r\n") {
    //FIXME: is this the right index?
    CompareResult::Ok => Ok((input.slice(2..), input.slice(0..2))),
    CompareResult::Incomplete => need_more_err(input, Needed::Size(2), ErrorKind::CrLf),
    CompareResult::Error => {
      let e: ErrorKind<u32> = ErrorKind::CrLf;
      Err(Err::Error(error_position!(input, e)))
    }
  }
}

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
// public methods
pub fn not_line_ending<T>(input: T) -> IResult<T, T>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength + AtEof,
  T: Compare<&'static str>,
  <T as InputIter>::Item: AsChar,
  <T as InputIter>::RawItem: AsChar,
{
  match input.position(|item| {
    let c = item.as_char();
    c == '\r' || c == '\n'
  }) {
    None => {
      if input.at_eof() {
        Ok((input.slice(input.input_len()..), input))
      } else {
        Err(Err::Incomplete(Needed::Unknown))
      }
    }
    Some(index) => {
      let mut it = input.slice(index..).iter_elements();
      let nth = it.next().unwrap().as_char();
      if nth == '\r' {
        let sliced = input.slice(index..);
        let comp = sliced.compare("\r\n");
        match comp {
          //FIXME: calculate the right index
          CompareResult::Incomplete => need_more_err(input, Needed::Unknown, ErrorKind::Tag),
          CompareResult::Error => {
            let e: ErrorKind<u32> = ErrorKind::Tag;
            Err(Err::Error(error_position!(input, e)))
          }
          CompareResult::Ok => Ok((input.slice(index..), input.slice(..index))),
        }
      } else {
        Ok((input.slice(index..), input.slice(..index)))
      }
    }
  }
}

/// Recognizes an end of line (both '\n' and '\r\n')
pub fn line_ending<T>(input: T) -> IResult<T, T>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength + AtEof,
  T: Compare<&'static str>,
{
  match input.compare("\n") {
    CompareResult::Ok => Ok((input.slice(1..), input.slice(0..1))),
    CompareResult::Incomplete => need_more_err(input, Needed::Size(1), ErrorKind::CrLf::<u32>),
    CompareResult::Error => {
      match input.compare("\r\n") {
        //FIXME: is this the right index?
        CompareResult::Ok => Ok((input.slice(2..), input.slice(0..2))),
        CompareResult::Incomplete => need_more_err(input, Needed::Size(2), ErrorKind::CrLf::<u32>),
        CompareResult::Error => Err(Err::Error(error_position!(input, ErrorKind::CrLf::<u32>))),
      }
    }
  }
}

pub fn eol<T>(input: T) -> IResult<T, T>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength + AtEof,
  T: Compare<&'static str>,
{
  line_ending(input)
}

/// Tests if byte is ASCII alphabetic: A-Z, a-z
#[inline]
pub fn is_alphabetic(chr: u8) -> bool {
  (chr >= 0x41 && chr <= 0x5A) || (chr >= 0x61 && chr <= 0x7A)
}

/// Tests if byte is ASCII digit: 0-9
#[inline]
pub fn is_digit(chr: u8) -> bool {
  chr >= 0x30 && chr <= 0x39
}

/// Tests if byte is ASCII hex digit: 0-9, A-F, a-f
#[inline]
pub fn is_hex_digit(chr: u8) -> bool {
  (chr >= 0x30 && chr <= 0x39) || (chr >= 0x41 && chr <= 0x46) || (chr >= 0x61 && chr <= 0x66)
}

/// Tests if byte is ASCII octal digit: 0-7
#[inline]
pub fn is_oct_digit(chr: u8) -> bool {
  chr >= 0x30 && chr <= 0x37
}

/// Tests if byte is ASCII alphanumeric: A-Z, a-z, 0-9
#[inline]
pub fn is_alphanumeric(chr: u8) -> bool {
  is_alphabetic(chr) || is_digit(chr)
}

/// Tests if byte is ASCII space or tab
#[inline]
pub fn is_space(chr: u8) -> bool {
  chr == b' ' || chr == b'\t'
}

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
//pub filter!(alpha is_alphabetic)
//pub filter!(digit is_digit)
//pub filter!(hex_digit is_hex_digit)
//pub filter!(oct_digit is_oct_digit)
//pub filter!(alphanumeric is_alphanumeric)

/// Recognizes one or more lowercase and uppercase alphabetic characters.
/// For ASCII strings: a-zA-Z
/// For UTF8 strings, any alphabetic code point (ie, not only the ASCII ones)
pub fn alpha<T>(input: T) -> IResult<T, T, u32>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  alpha1(input)
}

/// Recognizes zero or more lowercase and uppercase alphabetic characters.
/// For ASCII strings: a-zA-Z
/// For UTF8 strings, any alphabetic code point (ie, not only the ASCII ones)
pub fn alpha0<T>(input: T) -> IResult<T, T, u32>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position(|item| !item.is_alpha())
}

/// Recognizes one or more lowercase and uppercase alphabetic characters
/// For ASCII strings: a-zA-Z
/// For UTF8 strings, any alphabetic code point (ie, not only the ASCII ones)
pub fn alpha1<T>(input: T) -> IResult<T, T, u32>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1(|item| !item.is_alpha(), ErrorKind::Alpha)
}

/// Recognizes one or more numerical characters: 0-9
pub fn digit<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  digit1(input)
}

/// Recognizes zero or more numerical characters: 0-9
pub fn digit0<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position(|item| !item.is_dec_digit())
}

/// Recognizes one or more numerical characters: 0-9
pub fn digit1<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1(|item| !item.is_dec_digit(), ErrorKind::Digit)
}

/// Recognizes one or more hexadecimal numerical characters: 0-9, A-F, a-f
pub fn hex_digit<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  hex_digit1(input)
}

/// Recognizes zero or more hexadecimal numerical characters: 0-9, A-F, a-f
pub fn hex_digit0<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position(|item| !item.is_hex_digit())
}
/// Recognizes one or more hexadecimal numerical characters: 0-9, A-F, a-f
pub fn hex_digit1<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1(|item| !item.is_hex_digit(), ErrorKind::HexDigit)
}

/// Recognizes one or more octal characters: 0-7
pub fn oct_digit<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  oct_digit1(input)
}

/// Recognizes zero or more octal characters: 0-7
pub fn oct_digit0<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position(|item| !item.is_oct_digit())
}

/// Recognizes one or more octal characters: 0-7
pub fn oct_digit1<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1(|item| !item.is_oct_digit(), ErrorKind::OctDigit)
}

/// Recognizes one or more numerical and alphabetic characters
/// For ASCII strings: 0-9a-zA-Z
/// For UTF8 strings, 0-9 and any alphabetic code point (ie, not only the ASCII ones)
pub fn alphanumeric<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  alphanumeric1(input)
}

/// Recognizes zero or more numerical and alphabetic characters.
/// For ASCII strings: 0-9a-zA-Z
/// For UTF8 strings, 0-9 and any alphabetic code point (ie, not only the ASCII ones)
pub fn alphanumeric0<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position(|item| !item.is_alphanum())
}
/// Recognizes one or more numerical and alphabetic characters.
/// For ASCII strings: 0-9a-zA-Z
/// For UTF8 strings, 0-9 and any alphabetic code point (ie, not only the ASCII ones)
pub fn alphanumeric1<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1(|item| !item.is_alphanum(), ErrorKind::AlphaNumeric)
}

/// Recognizes one or more spaces and tabs
pub fn space<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  space1(input)
}

/// Recognizes zero or more spaces and tabs
pub fn space0<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position(|item| {
    let c = item.clone().as_char();
    !(c == ' ' || c == '\t')
  })
}
/// Recognizes one or more spaces and tabs
pub fn space1<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position1(
    |item| {
      let c = item.clone().as_char();
      !(c == ' ' || c == '\t')
    },
    ErrorKind::Space,
  )
}

/// Recognizes one or more spaces, tabs, carriage returns and line feeds
pub fn multispace<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  multispace1(input)
}

/// Recognizes zero or more spaces, tabs, carriage returns and line feeds
pub fn multispace0<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position(|item| {
    let c = item.clone().as_char();
    !(c == ' ' || c == '\t' || c == '\r' || c == '\n')
  })
}
/// Recognizes one or more spaces, tabs, carriage returns and line feeds
pub fn multispace1<T>(input: T) -> IResult<T, T>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position1(
    |item| {
      let c = item.clone().as_char();
      !(c == ' ' || c == '\t' || c == '\r' || c == '\n')
    },
    ErrorKind::MultiSpace,
  )
}

pub fn sized_buffer(input: &[u8]) -> IResult<&[u8], &[u8]> {
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

/// Recognizes an unsigned 1 byte integer (equivalent to take!(1)
#[inline]
pub fn be_u8(i: &[u8]) -> IResult<&[u8], u8> {
  if i.len() < 1 {
    need_more(i, Needed::Size(1))
  } else {
    Ok((&i[1..], i[0]))
  }
}

/// Recognizes big endian unsigned 2 bytes integer
#[inline]
pub fn be_u16(i: &[u8]) -> IResult<&[u8], u16> {
  if i.len() < 2 {
    need_more(i, Needed::Size(2))
  } else {
    let res = ((i[0] as u16) << 8) + i[1] as u16;
    Ok((&i[2..], res))
  }
}

/// Recognizes big endian unsigned 3 byte integer
#[inline]
pub fn be_u24(i: &[u8]) -> IResult<&[u8], u32> {
  if i.len() < 3 {
    need_more(i, Needed::Size(3))
  } else {
    let res = ((i[0] as u32) << 16) + ((i[1] as u32) << 8) + (i[2] as u32);
    Ok((&i[3..], res))
  }
}

/// Recognizes big endian unsigned 4 bytes integer
#[inline]
pub fn be_u32(i: &[u8]) -> IResult<&[u8], u32> {
  if i.len() < 4 {
    need_more(i, Needed::Size(4))
  } else {
    let res = ((i[0] as u32) << 24) + ((i[1] as u32) << 16) + ((i[2] as u32) << 8) + i[3] as u32;
    Ok((&i[4..], res))
  }
}

/// Recognizes big endian unsigned 8 bytes integer
#[inline]
pub fn be_u64(i: &[u8]) -> IResult<&[u8], u64, u32> {
  if i.len() < 8 {
    need_more(i, Needed::Size(8))
  } else {
    let res = ((i[0] as u64) << 56) + ((i[1] as u64) << 48) + ((i[2] as u64) << 40) + ((i[3] as u64) << 32) + ((i[4] as u64) << 24)
      + ((i[5] as u64) << 16) + ((i[6] as u64) << 8) + i[7] as u64;
    Ok((&i[8..], res))
  }
}

/// Recognizes big endian unsigned 16 bytes integer
#[inline]
pub fn be_u128(i: &[u8]) -> IResult<&[u8], u128, u32> {
  if i.len() < 16 {
    need_more(i, Needed::Size(16))
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
pub fn be_i8(i: &[u8]) -> IResult<&[u8], i8> {
  map!(i, be_u8, |x| x as i8)
}

/// Recognizes big endian signed 2 bytes integer
#[inline]
pub fn be_i16(i: &[u8]) -> IResult<&[u8], i16> {
  map!(i, be_u16, |x| x as i16)
}

/// Recognizes big endian signed 3 bytes integer
#[inline]
pub fn be_i24(i: &[u8]) -> IResult<&[u8], i32> {
  // Same as the unsigned version but we need to sign-extend manually here
  map!(i, be_u24, |x| if x & 0x80_00_00 != 0 {
    (x | 0xff_00_00_00) as i32
  } else {
    x as i32
  })
}

/// Recognizes big endian signed 4 bytes integer
#[inline]
pub fn be_i32(i: &[u8]) -> IResult<&[u8], i32> {
  map!(i, be_u32, |x| x as i32)
}

/// Recognizes big endian signed 8 bytes integer
#[inline]
pub fn be_i64(i: &[u8]) -> IResult<&[u8], i64> {
  map!(i, be_u64, |x| x as i64)
}

/// Recognizes big endian signed 16 bytes integer
#[inline]
pub fn be_i128(i: &[u8]) -> IResult<&[u8], i128> {
  map!(i, be_u128, |x| x as i128)
}

/// Recognizes an unsigned 1 byte integer (equivalent to take!(1)
#[inline]
pub fn le_u8(i: &[u8]) -> IResult<&[u8], u8> {
  if i.len() < 1 {
    need_more(i, Needed::Size(1))
  } else {
    Ok((&i[1..], i[0]))
  }
}

/// Recognizes little endian unsigned 2 bytes integer
#[inline]
pub fn le_u16(i: &[u8]) -> IResult<&[u8], u16> {
  if i.len() < 2 {
    need_more(i, Needed::Size(2))
  } else {
    let res = ((i[1] as u16) << 8) + i[0] as u16;
    Ok((&i[2..], res))
  }
}

/// Recognizes little endian unsigned 3 byte integer
#[inline]
pub fn le_u24(i: &[u8]) -> IResult<&[u8], u32> {
  if i.len() < 3 {
    need_more(i, Needed::Size(3))
  } else {
    let res = (i[0] as u32) + ((i[1] as u32) << 8) + ((i[2] as u32) << 16);
    Ok((&i[3..], res))
  }
}

/// Recognizes little endian unsigned 4 bytes integer
#[inline]
pub fn le_u32(i: &[u8]) -> IResult<&[u8], u32> {
  if i.len() < 4 {
    need_more(i, Needed::Size(4))
  } else {
    let res = ((i[3] as u32) << 24) + ((i[2] as u32) << 16) + ((i[1] as u32) << 8) + i[0] as u32;
    Ok((&i[4..], res))
  }
}

/// Recognizes little endian unsigned 8 bytes integer
#[inline]
pub fn le_u64(i: &[u8]) -> IResult<&[u8], u64> {
  if i.len() < 8 {
    need_more(i, Needed::Size(8))
  } else {
    let res = ((i[7] as u64) << 56) + ((i[6] as u64) << 48) + ((i[5] as u64) << 40) + ((i[4] as u64) << 32) + ((i[3] as u64) << 24)
      + ((i[2] as u64) << 16) + ((i[1] as u64) << 8) + i[0] as u64;
    Ok((&i[8..], res))
  }
}

/// Recognizes little endian unsigned 16 bytes integer
#[inline]
pub fn le_u128(i: &[u8]) -> IResult<&[u8], u128, u32> {
  if i.len() < 16 {
    need_more(i, Needed::Size(16))
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
pub fn le_i8(i: &[u8]) -> IResult<&[u8], i8> {
  map!(i, le_u8, |x| x as i8)
}

/// Recognizes little endian signed 2 bytes integer
#[inline]
pub fn le_i16(i: &[u8]) -> IResult<&[u8], i16> {
  map!(i, le_u16, |x| x as i16)
}

/// Recognizes little endian signed 3 bytes integer
#[inline]
pub fn le_i24(i: &[u8]) -> IResult<&[u8], i32> {
  // Same as the unsigned version but we need to sign-extend manually here
  map!(i, le_u24, |x| if x & 0x80_00_00 != 0 {
    (x | 0xff_00_00_00) as i32
  } else {
    x as i32
  })
}

/// Recognizes little endian signed 4 bytes integer
#[inline]
pub fn le_i32(i: &[u8]) -> IResult<&[u8], i32> {
  map!(i, le_u32, |x| x as i32)
}

/// Recognizes little endian signed 8 bytes integer
#[inline]
pub fn le_i64(i: &[u8]) -> IResult<&[u8], i64> {
  map!(i, le_u64, |x| x as i64)
}

/// Recognizes little endian signed 16 bytes integer
#[inline]
pub fn le_i128(i: &[u8]) -> IResult<&[u8], i128> {
  map!(i, le_u128, |x| x as i128)
}

/// Configurable endianness
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Endianness {
  Big,
  Little,
}

/// if the parameter is nom::Endianness::Big, parse a big endian u16 integer,
/// otherwise a little endian u16 integer
#[macro_export]
macro_rules! u16 ( ($i:expr, $e:expr) => ( {if $crate::Endianness::Big == $e { $crate::be_u16($i) } else { $crate::le_u16($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian u32 integer,
/// otherwise a little endian u32 integer
#[macro_export]
macro_rules! u32 ( ($i:expr, $e:expr) => ( {if $crate::Endianness::Big == $e { $crate::be_u32($i) } else { $crate::le_u32($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian u64 integer,
/// otherwise a little endian u64 integer
#[macro_export]
macro_rules! u64 ( ($i:expr, $e:expr) => ( {if $crate::Endianness::Big == $e { $crate::be_u64($i) } else { $crate::le_u64($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian u128 integer,
/// otherwise a little endian u128 integer
#[macro_export]
macro_rules! u128 ( ($i:expr, $e:expr) => ( {if $crate::Endianness::Big == $e { $crate::be_u128($i) } else { $crate::le_u128($i) } } ););

/// if the parameter is nom::Endianness::Big, parse a big endian i16 integer,
/// otherwise a little endian i16 integer
#[macro_export]
macro_rules! i16 ( ($i:expr, $e:expr) => ( {if $crate::Endianness::Big == $e { $crate::be_i16($i) } else { $crate::le_i16($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian i32 integer,
/// otherwise a little endian i32 integer
#[macro_export]
macro_rules! i32 ( ($i:expr, $e:expr) => ( {if $crate::Endianness::Big == $e { $crate::be_i32($i) } else { $crate::le_i32($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian i64 integer,
/// otherwise a little endian i64 integer
#[macro_export]
macro_rules! i64 ( ($i:expr, $e:expr) => ( {if $crate::Endianness::Big == $e { $crate::be_i64($i) } else { $crate::le_i64($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian i64 integer,
/// otherwise a little endian i64 integer
#[macro_export]
macro_rules! i128 ( ($i:expr, $e:expr) => ( {if $crate::Endianness::Big == $e { $crate::be_i128($i) } else { $crate::le_i128($i) } } ););

/// Recognizes big endian 4 bytes floating point number
#[inline]
pub fn be_f32(input: &[u8]) -> IResult<&[u8], f32> {
  match be_u32(input) {
    Err(e) => Err(e),
    Ok((i, o)) => unsafe { Ok((i, transmute::<u32, f32>(o))) },
  }
}

/// Recognizes big endian 8 bytes floating point number
#[inline]
pub fn be_f64(input: &[u8]) -> IResult<&[u8], f64> {
  match be_u64(input) {
    Err(e) => Err(e),
    Ok((i, o)) => unsafe { Ok((i, transmute::<u64, f64>(o))) },
  }
}

/// Recognizes little endian 4 bytes floating point number
#[inline]
pub fn le_f32(input: &[u8]) -> IResult<&[u8], f32> {
  match le_u32(input) {
    Err(e) => Err(e),
    Ok((i, o)) => unsafe { Ok((i, transmute::<u32, f32>(o))) },
  }
}

/// Recognizes little endian 8 bytes floating point number
#[inline]
pub fn le_f64(input: &[u8]) -> IResult<&[u8], f64> {
  match le_u64(input) {
    Err(e) => Err(e),
    Ok((i, o)) => unsafe { Ok((i, transmute::<u64, f64>(o))) },
  }
}

/// Recognizes a hex-encoded integer
#[inline]
pub fn hex_u32(input: &[u8]) -> IResult<&[u8], u32> {
  match is_a!(input, &b"0123456789abcdefABCDEF"[..]) {
    Err(e) => Err(e),
    Ok((i, o)) => {
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
  }
}

/// Recognizes non empty buffers
#[inline]
pub fn non_empty<T>(input: T) -> IResult<T, T>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputLength + AtEof,
{
  if input.input_len() == 0 {
    return need_more_err(input, Needed::Unknown, ErrorKind::NonEmpty::<u32>);
  } else {
    Ok((input.slice(input.input_len()..), input))
  }
}

/// Return the remaining input.
#[inline]
pub fn rest<T>(input: T) -> IResult<T, T>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputLength,
{
  Ok((input.slice(input.input_len()..), input))
}

/// Return the length of the remaining input.
#[inline]
pub fn rest_len<T>(input: T) -> IResult<T, usize>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputLength,
{
  let len = input.input_len();
  Ok((input, len))
}

/// Return the remaining input, for strings.
#[inline]
pub fn rest_s(input: &str) -> IResult<&str, &str> {
  Ok((&input[input.len()..], input))
}

#[allow(unused_imports)]
#[cfg_attr(rustfmt, rustfmt_skip)]
pub fn recognize_float<T>(input: T) -> IResult<T, T, u32>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: Clone + Offset,
  T: InputIter + AtEof,
  <T as InputIter>::Item: AsChar,
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
        digit
        )
      )
    )
  )
}

/// Recognizes floating point number in a byte string and returns a f32
#[cfg(feature = "alloc")]
//pub fn float(input: &[u8]) -> IResult<&[u8], f32> {
pub fn float<T>(input: T) -> IResult<T, f32, u32>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: Clone + Offset,
  T: InputIter + InputLength + ParseTo<f32> + AtEof,
  <T as InputIter>::Item: AsChar,
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar
{
  flat_map!(input, recognize_float, parse_to!(f32))
}

/// Recognizes floating point number in a string and returns a f32
#[cfg(feature = "alloc")]
#[deprecated(since = "4.1.0", note = "Please use `float` instead")]
pub fn float_s<T>(input: T) -> IResult<T, f32, u32>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: Clone + Offset,
  T: InputIter + InputLength + ParseTo<f32> + AtEof,
  <T as InputIter>::Item: AsChar,
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar
{
  flat_map!(input, call!(recognize_float), parse_to!(f32))
}

/// Recognizes floating point number in a byte string and returns a f64
#[cfg(feature = "alloc")]
pub fn double<T>(input: T) -> IResult<T, f64, u32>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: Clone + Offset,
  T: InputIter + InputLength + ParseTo<f64> + AtEof,
  <T as InputIter>::Item: AsChar,
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar
{
  flat_map!(input, call!(recognize_float), parse_to!(f64))
}

/// Recognizes floating point number in a string and returns a f64
#[cfg(feature = "alloc")]
#[deprecated(since = "4.1.0", note = "Please use `double` instead")]
pub fn double_s<T>(input: T) -> IResult<T, f64, u32>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: Clone + Offset,
  T: InputIter + InputLength + ParseTo<f64> + AtEof,
  <T as InputIter>::Item: AsChar,
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar
{
  flat_map!(input, call!(recognize_float), parse_to!(f64))
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Err, IResult, Needed};
  use types::{CompleteByteSlice, CompleteStr};

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
  fn character() {
    let empty: &[u8] = b"";
    let a: &[u8] = b"abcd";
    let b: &[u8] = b"1234";
    let c: &[u8] = b"a123";
    let d: &[u8] = "azé12".as_bytes();
    let e: &[u8] = b" ";
    let f: &[u8] = b" ;";
    assert_eq!(alpha(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      alpha(CompleteByteSlice(a)),
      Ok((CompleteByteSlice(empty), CompleteByteSlice(a)))
    );
    assert_eq!(
      alpha(b),
      Err(Err::Error(error_position!(b, ErrorKind::Alpha)))
    );
    assert_eq!(alpha(c), Ok((&c[1..], &b"a"[..])));
    assert_eq!(alpha(d), Ok(("é12".as_bytes(), &b"az"[..])));
    assert_eq!(
      digit(a),
      Err(Err::Error(error_position!(a, ErrorKind::Digit)))
    );
    assert_eq!(digit(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      digit(CompleteByteSlice(b)),
      Ok((CompleteByteSlice(empty), CompleteByteSlice(b)))
    );
    assert_eq!(
      digit(c),
      Err(Err::Error(error_position!(c, ErrorKind::Digit)))
    );
    assert_eq!(
      digit(d),
      Err(Err::Error(error_position!(d, ErrorKind::Digit)))
    );
    assert_eq!(hex_digit(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      hex_digit(CompleteByteSlice(a)),
      Ok((CompleteByteSlice(empty), CompleteByteSlice(a)))
    );
    assert_eq!(hex_digit(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      hex_digit(CompleteByteSlice(b)),
      Ok((CompleteByteSlice(empty), CompleteByteSlice(b)))
    );
    assert_eq!(hex_digit(c), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      hex_digit(CompleteByteSlice(c)),
      Ok((CompleteByteSlice(empty), CompleteByteSlice(c)))
    );
    assert_eq!(hex_digit(d), Ok(("zé12".as_bytes(), &b"a"[..])));
    assert_eq!(
      hex_digit(e),
      Err(Err::Error(error_position!(e, ErrorKind::HexDigit)))
    );
    assert_eq!(
      oct_digit(a),
      Err(Err::Error(error_position!(a, ErrorKind::OctDigit)))
    );
    assert_eq!(oct_digit(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      oct_digit(CompleteByteSlice(b)),
      Ok((CompleteByteSlice(empty), CompleteByteSlice(b)))
    );
    assert_eq!(
      oct_digit(c),
      Err(Err::Error(error_position!(c, ErrorKind::OctDigit)))
    );
    assert_eq!(
      oct_digit(d),
      Err(Err::Error(error_position!(d, ErrorKind::OctDigit)))
    );
    assert_eq!(alphanumeric(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      alphanumeric(CompleteByteSlice(a)),
      Ok((CompleteByteSlice(empty), CompleteByteSlice(a)))
    );
    //assert_eq!(fix_error!(b,(), alphanumeric), Ok((empty, b)));
    assert_eq!(alphanumeric(c), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      alphanumeric(CompleteByteSlice(c)),
      Ok((CompleteByteSlice(empty), CompleteByteSlice(c)))
    );
    assert_eq!(alphanumeric(d), Ok(("é12".as_bytes(), &b"az"[..])));
    assert_eq!(space(e), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      space(CompleteByteSlice(e)),
      Ok((CompleteByteSlice(empty), CompleteByteSlice(b" ")))
    );
    assert_eq!(space(f), Ok((&b";"[..], &b" "[..])));
    assert_eq!(
      space(CompleteByteSlice(f)),
      Ok((CompleteByteSlice(b";"), CompleteByteSlice(b" ")))
    );
  }

  #[cfg(feature = "alloc")]
  #[test]
  fn character_s() {
    let empty = "";
    let a = "abcd";
    let b = "1234";
    let c = "a123";
    let d = "azé12";
    let e = " ";
    assert_eq!(alpha(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      alpha(CompleteStr(a)),
      Ok((CompleteStr(empty), CompleteStr(a)))
    );
    assert_eq!(
      alpha(b),
      Err(Err::Error(error_position!(b, ErrorKind::Alpha)))
    );
    assert_eq!(alpha(c), Ok((&c[1..], &"a"[..])));
    assert_eq!(alpha(d), Ok(("12", &"azé"[..])));
    assert_eq!(
      digit(a),
      Err(Err::Error(error_position!(a, ErrorKind::Digit)))
    );
    assert_eq!(digit(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      digit(CompleteStr(b)),
      Ok((CompleteStr(empty), CompleteStr(b)))
    );
    assert_eq!(
      digit(c),
      Err(Err::Error(error_position!(c, ErrorKind::Digit)))
    );
    assert_eq!(
      digit(d),
      Err(Err::Error(error_position!(d, ErrorKind::Digit)))
    );
    assert_eq!(hex_digit(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      hex_digit(CompleteStr(a)),
      Ok((CompleteStr(empty), CompleteStr(a)))
    );
    assert_eq!(hex_digit(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      hex_digit(CompleteStr(b)),
      Ok((CompleteStr(empty), CompleteStr(b)))
    );
    assert_eq!(hex_digit(c), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      hex_digit(CompleteStr(c)),
      Ok((CompleteStr(empty), CompleteStr(c)))
    );
    assert_eq!(hex_digit(d), Ok(("zé12", &"a"[..])));
    assert_eq!(
      hex_digit(e),
      Err(Err::Error(error_position!(e, ErrorKind::HexDigit)))
    );
    assert_eq!(
      oct_digit(a),
      Err(Err::Error(error_position!(a, ErrorKind::OctDigit)))
    );
    assert_eq!(oct_digit(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      oct_digit(CompleteStr(b)),
      Ok((CompleteStr(empty), CompleteStr(b)))
    );
    assert_eq!(
      oct_digit(c),
      Err(Err::Error(error_position!(c, ErrorKind::OctDigit)))
    );
    assert_eq!(
      oct_digit(d),
      Err(Err::Error(error_position!(d, ErrorKind::OctDigit)))
    );
    assert_eq!(alphanumeric(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      alphanumeric(CompleteStr(a)),
      Ok((CompleteStr(empty), CompleteStr(a)))
    );
    //assert_eq!(fix_error!(b,(), alphanumeric), Ok((empty, b)));
    assert_eq!(alphanumeric(c), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      alphanumeric(CompleteStr(c)),
      Ok((CompleteStr(empty), CompleteStr(c)))
    );
    assert_eq!(alphanumeric(d), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      alphanumeric(CompleteStr(d)),
      Ok((CompleteStr(""), CompleteStr("azé12")))
    );
    assert_eq!(space(e), Err(Err::Incomplete(Needed::Size(1))));
  }

  use traits::Offset;
  #[test]
  fn offset() {
    let a = &b"abcd;"[..];
    let b = &b"1234;"[..];
    let c = &b"a123;"[..];
    let d = &b" \t;"[..];
    let e = &b" \t\r\n;"[..];
    let f = &b"123abcDEF;"[..];

    match alpha(a) {
      Ok((i, _)) => {
        assert_eq!(a.offset(i) + i.len(), a.len());
      }
      _ => panic!("wrong return type in offset test for alpha"),
    }
    match digit(b) {
      Ok((i, _)) => {
        assert_eq!(b.offset(i) + i.len(), b.len());
      }
      _ => panic!("wrong return type in offset test for digit"),
    }
    match alphanumeric(c) {
      Ok((i, _)) => {
        assert_eq!(c.offset(i) + i.len(), c.len());
      }
      _ => panic!("wrong return type in offset test for alphanumeric"),
    }
    match space(d) {
      Ok((i, _)) => {
        assert_eq!(d.offset(i) + i.len(), d.len());
      }
      _ => panic!("wrong return type in offset test for space"),
    }
    match multispace(e) {
      Ok((i, _)) => {
        assert_eq!(e.offset(i) + i.len(), e.len());
      }
      _ => panic!("wrong return type in offset test for multispace"),
    }
    match hex_digit(f) {
      Ok((i, _)) => {
        assert_eq!(f.offset(i) + i.len(), f.len());
      }
      _ => panic!("wrong return type in offset test for hex_digit"),
    }
    match oct_digit(f) {
      Ok((i, _)) => {
        assert_eq!(f.offset(i) + i.len(), f.len());
      }
      _ => panic!("wrong return type in offset test for oct_digit"),
    }
  }

  #[test]
  fn is_not_line_ending_bytes() {
    let a: &[u8] = b"ab12cd\nefgh";
    assert_eq!(not_line_ending(a), Ok((&b"\nefgh"[..], &b"ab12cd"[..])));

    let b: &[u8] = b"ab12cd\nefgh\nijkl";
    assert_eq!(
      not_line_ending(b),
      Ok((&b"\nefgh\nijkl"[..], &b"ab12cd"[..]))
    );

    let c: &[u8] = b"ab12cd\r\nefgh\nijkl";
    assert_eq!(
      not_line_ending(c),
      Ok((&b"\r\nefgh\nijkl"[..], &b"ab12cd"[..]))
    );

    let d = CompleteByteSlice(b"ab12cd");
    assert_eq!(not_line_ending(d), Ok((CompleteByteSlice(b""), d)));

    let d: &[u8] = b"ab12cd";
    assert_eq!(not_line_ending(d), Err(Err::Incomplete(Needed::Unknown)));
  }

  #[test]
  fn is_not_line_ending_str() {
    /*
    let a: &str = "ab12cd\nefgh";
    assert_eq!(not_line_ending(a), Ok((&"\nefgh"[..], &"ab12cd"[..])));

    let b: &str = "ab12cd\nefgh\nijkl";
    assert_eq!(not_line_ending(b), Ok((&"\nefgh\nijkl"[..], &"ab12cd"[..])));

    let c: &str = "ab12cd\r\nefgh\nijkl";
    assert_eq!(not_line_ending(c), Ok((&"\r\nefgh\nijkl"[..], &"ab12cd"[..])));

    let d = "βèƒôřè\nÂßÇáƒƭèř";
    assert_eq!(not_line_ending(d), Ok((&"\nÂßÇáƒƭèř"[..], &"βèƒôřè"[..])));

    let e = "βèƒôřè\r\nÂßÇáƒƭèř";
    assert_eq!(not_line_ending(e), Ok((&"\r\nÂßÇáƒƭèř"[..], &"βèƒôřè"[..])));
    */

    let f = "βèƒôřè\rÂßÇáƒƭèř";
    assert_eq!(
      not_line_ending(f),
      Err(Err::Error(error_position!(f, ErrorKind::Tag)))
    );

    let g = CompleteStr("ab12cd");
    assert_eq!(not_line_ending(g), Ok((CompleteStr(""), g)));

    let g2: &str = "ab12cd";
    assert_eq!(not_line_ending(g2), Err(Err::Incomplete(Needed::Unknown)));
  }

  #[test]
  #[cfg(feature = "alloc")]
  fn buffer_with_size() {
    use lib::std::vec::Vec;
    let i: Vec<u8> = vec![7, 8];
    let o: Vec<u8> = vec![4, 5, 6];
    //let arr:[u8; 6usize] = [3, 4, 5, 6, 7, 8];
    let arr: [u8; 6usize] = [3, 4, 5, 6, 7, 8];
    let res = sized_buffer(&arr[..]);
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

  #[test]
  fn i8_tests() {
    assert_eq!(be_i8(&[0x00]), Ok((&b""[..], 0)));
    assert_eq!(be_i8(&[0x7f]), Ok((&b""[..], 127)));
    assert_eq!(be_i8(&[0xff]), Ok((&b""[..], -1)));
    assert_eq!(be_i8(&[0x80]), Ok((&b""[..], -128)));
  }

  #[test]
  fn i16_tests() {
    assert_eq!(be_i16(&[0x00, 0x00]), Ok((&b""[..], 0)));
    assert_eq!(be_i16(&[0x7f, 0xff]), Ok((&b""[..], 32_767_i16)));
    assert_eq!(be_i16(&[0xff, 0xff]), Ok((&b""[..], -1)));
    assert_eq!(be_i16(&[0x80, 0x00]), Ok((&b""[..], -32_768_i16)));
  }

  #[test]
  fn u24_tests() {
    assert_eq!(be_u24(&[0x00, 0x00, 0x00]), Ok((&b""[..], 0)));
    assert_eq!(be_u24(&[0x00, 0xFF, 0xFF]), Ok((&b""[..], 65_535_u32)));
    assert_eq!(be_u24(&[0x12, 0x34, 0x56]), Ok((&b""[..], 1_193_046_u32)));
  }

  #[test]
  fn i24_tests() {
    assert_eq!(be_i24(&[0xFF, 0xFF, 0xFF]), Ok((&b""[..], -1_i32)));
    assert_eq!(be_i24(&[0xFF, 0x00, 0x00]), Ok((&b""[..], -65_536_i32)));
    assert_eq!(be_i24(&[0xED, 0xCB, 0xAA]), Ok((&b""[..], -1_193_046_i32)));
  }

  #[test]
  fn i32_tests() {
    assert_eq!(be_i32(&[0x00, 0x00, 0x00, 0x00]), Ok((&b""[..], 0)));
    assert_eq!(
      be_i32(&[0x7f, 0xff, 0xff, 0xff]),
      Ok((&b""[..], 2_147_483_647_i32))
    );
    assert_eq!(be_i32(&[0xff, 0xff, 0xff, 0xff]), Ok((&b""[..], -1)));
    assert_eq!(
      be_i32(&[0x80, 0x00, 0x00, 0x00]),
      Ok((&b""[..], -2_147_483_648_i32))
    );
  }

  #[test]
  fn i64_tests() {
    assert_eq!(
      be_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0))
    );
    assert_eq!(
      be_i64(&[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], 9_223_372_036_854_775_807_i64))
    );
    assert_eq!(
      be_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], -1))
    );
    assert_eq!(
      be_i64(&[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], -9_223_372_036_854_775_808_i64))
    );
  }

  #[test]
  fn i128_tests() {
    assert_eq!(
      be_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0))
    );
    assert_eq!(
      be_i128(&[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], 170_141_183_460_469_231_731_687_303_715_884_105_727_i128))
    );
    assert_eq!(
      be_i128(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], -1))
    );
    assert_eq!(
      be_i128(&[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], -170_141_183_460_469_231_731_687_303_715_884_105_728_i128))
    );
  }

  #[test]
  fn le_i8_tests() {
    assert_eq!(le_i8(&[0x00]), Ok((&b""[..], 0)));
    assert_eq!(le_i8(&[0x7f]), Ok((&b""[..], 127)));
    assert_eq!(le_i8(&[0xff]), Ok((&b""[..], -1)));
    assert_eq!(le_i8(&[0x80]), Ok((&b""[..], -128)));
  }

  #[test]
  fn le_i16_tests() {
    assert_eq!(le_i16(&[0x00, 0x00]), Ok((&b""[..], 0)));
    assert_eq!(le_i16(&[0xff, 0x7f]), Ok((&b""[..], 32_767_i16)));
    assert_eq!(le_i16(&[0xff, 0xff]), Ok((&b""[..], -1)));
    assert_eq!(le_i16(&[0x00, 0x80]), Ok((&b""[..], -32_768_i16)));
  }

  #[test]
  fn le_u24_tests() {
    assert_eq!(le_u24(&[0x00, 0x00, 0x00]), Ok((&b""[..], 0)));
    assert_eq!(le_u24(&[0xFF, 0xFF, 0x00]), Ok((&b""[..], 65_535_u32)));
    assert_eq!(le_u24(&[0x56, 0x34, 0x12]), Ok((&b""[..], 1_193_046_u32)));
  }

  #[test]
  fn le_i24_tests() {
    assert_eq!(le_i24(&[0xFF, 0xFF, 0xFF]), Ok((&b""[..], -1_i32)));
    assert_eq!(le_i24(&[0x00, 0x00, 0xFF]), Ok((&b""[..], -65_536_i32)));
    assert_eq!(le_i24(&[0xAA, 0xCB, 0xED]), Ok((&b""[..], -1_193_046_i32)));
  }

  #[test]
  fn le_i32_tests() {
    assert_eq!(le_i32(&[0x00, 0x00, 0x00, 0x00]), Ok((&b""[..], 0)));
    assert_eq!(
      le_i32(&[0xff, 0xff, 0xff, 0x7f]),
      Ok((&b""[..], 2_147_483_647_i32))
    );
    assert_eq!(le_i32(&[0xff, 0xff, 0xff, 0xff]), Ok((&b""[..], -1)));
    assert_eq!(
      le_i32(&[0x00, 0x00, 0x00, 0x80]),
      Ok((&b""[..], -2_147_483_648_i32))
    );
  }

  #[test]
  fn le_i64_tests() {
    assert_eq!(
      le_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0))
    );
    assert_eq!(
      le_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]),
      Ok((&b""[..], 9_223_372_036_854_775_807_i64))
    );
    assert_eq!(
      le_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], -1))
    );
    assert_eq!(
      le_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80]),
      Ok((&b""[..], -9_223_372_036_854_775_808_i64))
    );
  }

  #[test]
  fn le_i128_tests() {
    assert_eq!(
      le_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0))
    );
    assert_eq!(
      le_i128(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]),
      Ok((&b""[..], 170_141_183_460_469_231_731_687_303_715_884_105_727_i128))
    );
    assert_eq!(
      le_i128(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      Ok((&b""[..], -1))
    );
    assert_eq!(
      le_i128(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80]),
      Ok((&b""[..], -170_141_183_460_469_231_731_687_303_715_884_105_728_i128))
    );
  }

  #[test]
  fn be_f32_tests() {
    assert_eq!(be_f32(&[0x00, 0x00, 0x00, 0x00]), Ok((&b""[..], 0_f32)));
    assert_eq!(
      be_f32(&[0x4d, 0x31, 0x1f, 0xd8]),
      Ok((&b""[..], 185_728_392_f32))
    );
  }

  #[test]
  fn be_f64_tests() {
    assert_eq!(
      be_f64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0_f64))
    );
    assert_eq!(
      be_f64(&[0x41, 0xa6, 0x23, 0xfb, 0x10, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 185_728_392_f64))
    );
  }

  #[test]
  fn le_f32_tests() {
    assert_eq!(le_f32(&[0x00, 0x00, 0x00, 0x00]), Ok((&b""[..], 0_f32)));
    assert_eq!(
      le_f32(&[0xd8, 0x1f, 0x31, 0x4d]),
      Ok((&b""[..], 185_728_392_f32))
    );
  }

  #[test]
  fn le_f64_tests() {
    assert_eq!(
      le_f64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
      Ok((&b""[..], 0_f64))
    );
    assert_eq!(
      le_f64(&[0x00, 0x00, 0x00, 0x10, 0xfb, 0x23, 0xa6, 0x41]),
      Ok((&b""[..], 185_728_392_f64))
    );
  }

  #[test]
  fn hex_u32_tests() {
    assert_eq!(
      hex_u32(&b";"[..]),
      Err(Err::Error(error_position!(&b";"[..], ErrorKind::IsA)))
    );
    assert_eq!(hex_u32(&b"ff;"[..]), Ok((&b";"[..], 255)));
    assert_eq!(hex_u32(&b"1be2;"[..]), Ok((&b";"[..], 7138)));
    assert_eq!(hex_u32(&b"c5a31be2;"[..]), Ok((&b";"[..], 3_315_801_058)));
    assert_eq!(hex_u32(&b"C5A31be2;"[..]), Ok((&b";"[..], 3_315_801_058)));
    assert_eq!(hex_u32(&b"00c5a31be2;"[..]), Ok((&b"e2;"[..], 12_952_347)));
    assert_eq!(
      hex_u32(&b"c5a31be201;"[..]),
      Ok((&b"01;"[..], 3_315_801_058))
    );
    assert_eq!(hex_u32(&b"ffffffff;"[..]), Ok((&b";"[..], 4_294_967_295)));
    assert_eq!(hex_u32(&b"0x1be2;"[..]), Ok((&b"x1be2;"[..], 0)));
  }

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
    assert_eq!(rest(input), Ok((empty, input)));
  }

  #[test]
  fn rest_on_strs() {
    let input: &str = "Hello, world!";
    let empty: &str = "";
    assert_eq!(rest(input), Ok((empty, input)));
  }

  #[test]
  fn rest_len_on_slices() {
    let input: &[u8] = &b"Hello, world!"[..];
    assert_eq!(rest_len(input), Ok((input, input.len())));
  }

  #[test]
  fn configurable_endianness() {
    named!(be_tst16<u16>, u16!(Endianness::Big));
    named!(le_tst16<u16>, u16!(Endianness::Little));
    assert_eq!(be_tst16(&[0x80, 0x00]), Ok((&b""[..], 32_768_u16)));
    assert_eq!(le_tst16(&[0x80, 0x00]), Ok((&b""[..], 128_u16)));

    named!(be_tst32<u32>, u32!(Endianness::Big));
    named!(le_tst32<u32>, u32!(Endianness::Little));
    assert_eq!(
      be_tst32(&[0x12, 0x00, 0x60, 0x00]),
      Ok((&b""[..], 302_014_464_u32))
    );
    assert_eq!(
      le_tst32(&[0x12, 0x00, 0x60, 0x00]),
      Ok((&b""[..], 6_291_474_u32))
    );

    named!(be_tst64<u64>, u64!(Endianness::Big));
    named!(le_tst64<u64>, u64!(Endianness::Little));
    assert_eq!(
      be_tst64(&[0x12, 0x00, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 1_297_142_246_100_992_000_u64))
    );
    assert_eq!(
      le_tst64(&[0x12, 0x00, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 36_028_874_334_666_770_u64))
    );

    named!(be_tsti16<i16>, i16!(Endianness::Big));
    named!(le_tsti16<i16>, i16!(Endianness::Little));
    assert_eq!(be_tsti16(&[0x00, 0x80]), Ok((&b""[..], 128_i16)));
    assert_eq!(le_tsti16(&[0x00, 0x80]), Ok((&b""[..], -32_768_i16)));

    named!(be_tsti32<i32>, i32!(Endianness::Big));
    named!(le_tsti32<i32>, i32!(Endianness::Little));
    assert_eq!(
      be_tsti32(&[0x00, 0x12, 0x60, 0x00]),
      Ok((&b""[..], 1_204_224_i32))
    );
    assert_eq!(
      le_tsti32(&[0x00, 0x12, 0x60, 0x00]),
      Ok((&b""[..], 6_296_064_i32))
    );

    named!(be_tsti64<i64>, i64!(Endianness::Big));
    named!(le_tsti64<i64>, i64!(Endianness::Little));
    assert_eq!(
      be_tsti64(&[0x00, 0xFF, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 71_881_672_479_506_432_i64))
    );
    assert_eq!(
      le_tsti64(&[0x00, 0xFF, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 36_028_874_334_732_032_i64))
    );
  }

  #[test]
  #[cfg(feature = "std")]
  fn manual_configurable_endianness_test() {
    let x = 1;
    let int_parse: Box<Fn(&[u8]) -> IResult<&[u8], u16>> = if x == 2 {
      Box::new(be_u16)
    } else {
      Box::new(le_u16)
    };
    println!("{:?}", int_parse(&b"3"[..]));
    assert_eq!(int_parse(&[0x80, 0x00]), Ok((&b""[..], 128_u16)));
  }

  use lib::std::convert::From;
  impl From<u32> for CustomError {
    fn from(_: u32) -> Self {
      CustomError
    }
  }

  struct CustomError;
  #[allow(dead_code)]
  fn custom_error(input: &[u8]) -> IResult<&[u8], &[u8], CustomError> {
    fix_error!(input, CustomError, alphanumeric)
  }

  #[test]
  fn hex_digit_test() {
    let i = &b"0123456789abcdefABCDEF;"[..];
    assert_eq!(hex_digit(i), Ok((&b";"[..], &i[..i.len() - 1])));

    let i = &b"g"[..];
    assert_eq!(
      hex_digit(i),
      Err(Err::Error(error_position!(i, ErrorKind::HexDigit)))
    );

    let i = &b"G"[..];
    assert_eq!(
      hex_digit(i),
      Err(Err::Error(error_position!(i, ErrorKind::HexDigit)))
    );

    assert!(is_hex_digit(b'0'));
    assert!(is_hex_digit(b'9'));
    assert!(is_hex_digit(b'a'));
    assert!(is_hex_digit(b'f'));
    assert!(is_hex_digit(b'A'));
    assert!(is_hex_digit(b'F'));
    assert!(!is_hex_digit(b'g'));
    assert!(!is_hex_digit(b'G'));
    assert!(!is_hex_digit(b'/'));
    assert!(!is_hex_digit(b':'));
    assert!(!is_hex_digit(b'@'));
    assert!(!is_hex_digit(b'\x60'));
  }

  #[test]
  fn oct_digit_test() {
    let i = &b"01234567;"[..];
    assert_eq!(oct_digit(i), Ok((&b";"[..], &i[..i.len() - 1])));

    let i = &b"8"[..];
    assert_eq!(
      oct_digit(i),
      Err(Err::Error(error_position!(i, ErrorKind::OctDigit)))
    );

    assert!(is_oct_digit(b'0'));
    assert!(is_oct_digit(b'7'));
    assert!(!is_oct_digit(b'8'));
    assert!(!is_oct_digit(b'9'));
    assert!(!is_oct_digit(b'a'));
    assert!(!is_oct_digit(b'A'));
    assert!(!is_oct_digit(b'/'));
    assert!(!is_oct_digit(b':'));
    assert!(!is_oct_digit(b'@'));
    assert!(!is_oct_digit(b'\x60'));
  }

  #[test]
  fn full_line_windows() {
    named!(
      take_full_line<(&[u8], &[u8])>,
      tuple!(not_line_ending, line_ending)
    );
    let input = b"abc\r\n";
    let output = take_full_line(input);
    assert_eq!(output, Ok((&b""[..], (&b"abc"[..], &b"\r\n"[..]))));
  }

  #[test]
  fn full_line_unix() {
    named!(
      take_full_line<(&[u8], &[u8])>,
      tuple!(not_line_ending, line_ending)
    );
    let input = b"abc\n";
    let output = take_full_line(input);
    assert_eq!(output, Ok((&b""[..], (&b"abc"[..], &b"\n"[..]))));
  }

  #[test]
  fn check_windows_lineending() {
    let input = b"\r\n";
    let output = line_ending(&input[..]);
    assert_eq!(output, Ok((&b""[..], &b"\r\n"[..])));
  }

  #[test]
  fn check_unix_lineending() {
    let input = b"\n";
    let output = line_ending(&input[..]);
    assert_eq!(output, Ok((&b""[..], &b"\n"[..])));
  }

  #[test]
  fn cr_lf() {
    assert_eq!(crlf(&b"\r\na"[..]), Ok((&b"a"[..], &b"\r\n"[..])));
    assert_eq!(crlf(&b"\r"[..]), Err(Err::Incomplete(Needed::Size(2))));
    assert_eq!(
      crlf(&b"\ra"[..]),
      Err(Err::Error(error_position!(&b"\ra"[..], ErrorKind::CrLf)))
    );

    assert_eq!(crlf("\r\na"), Ok(("a", "\r\n")));
    assert_eq!(crlf("\r"), Err(Err::Incomplete(Needed::Size(2))));
    assert_eq!(
      crlf("\ra"),
      Err(Err::Error(error_position!("\ra", ErrorKind::CrLf)))
    );
  }

  #[test]
  fn end_of_line() {
    assert_eq!(eol(&b"\na"[..]), Ok((&b"a"[..], &b"\n"[..])));
    assert_eq!(eol(&b"\r\na"[..]), Ok((&b"a"[..], &b"\r\n"[..])));
    assert_eq!(eol(&b"\r"[..]), Err(Err::Incomplete(Needed::Size(2))));
    assert_eq!(
      eol(&b"\ra"[..]),
      Err(Err::Error(error_position!(&b"\ra"[..], ErrorKind::CrLf)))
    );

    assert_eq!(eol("\na"), Ok(("a", "\n")));
    assert_eq!(eol("\r\na"), Ok(("a", "\r\n")));
    assert_eq!(eol("\r"), Err(Err::Incomplete(Needed::Size(2))));
    assert_eq!(
      eol("\ra"),
      Err(Err::Error(error_position!("\ra", ErrorKind::CrLf)))
    );
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

      assert_eq!(
        recognize_float(CompleteStr(test)),
        Ok((CompleteStr(""), CompleteStr(test)))
      );
      let larger = format!("{};", test);
      assert_eq!(recognize_float(&larger[..]), Ok((";", test)));

      assert_eq!(float(larger.as_bytes()), Ok((&b";"[..], expected32)));
      assert_eq!(float(&larger[..]), Ok((";", expected32)));
      assert_eq!(float(CompleteByteSlice(test.as_bytes())), Ok((CompleteByteSlice(&b""[..]), expected32)));
      assert_eq!(float(CompleteStr(test)), Ok((CompleteStr(""), expected32)));

      assert_eq!(double(larger.as_bytes()), Ok((&b";"[..], expected64)));
      assert_eq!(double(&larger[..]), Ok((";", expected64)));
      assert_eq!(double(CompleteByteSlice(test.as_bytes())), Ok((CompleteByteSlice(&b""[..]), expected64)));
      assert_eq!(double(CompleteStr(test)), Ok((CompleteStr(""), expected64)));

      //deprecated functions
      assert_eq!(float_s(&larger[..]), Ok((";", expected32)));
      assert_eq!(double_s(&larger[..]), Ok((";", expected64)));
    }

    let remaining_exponent = "-1.234E-";
    assert_eq!(
      recognize_float(remaining_exponent),
      Err(Err::Incomplete(Needed::Size(1)))
    );
  }

  #[allow(dead_code)]
  pub fn end_of_line_completestr(input: CompleteStr) -> IResult<CompleteStr, CompleteStr> {
    alt!(input, eof!() | eol)
  }
}
