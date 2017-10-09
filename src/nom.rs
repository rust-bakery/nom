//! Useful parser combinators
//!
//! A number of useful parser combinators have already been implemented.
//! Some of them use macros, other are implemented through functions.
//! Hopefully, the syntax will converge to onely one way in the future,
//! but the macros system makes no promises.
//!

#[cfg(not(feature = "std"))]
use std::prelude::v1::*;
use std::boxed::Box;

use std::fmt::Debug;
use internal::*;
use internal::IResult::*;
use util::ErrorKind;
use traits::{AsChar,InputLength,InputIter};
use std::mem::transmute;
use std::ops::{Range,RangeFrom,RangeTo};
use traits::{Compare,CompareResult,Slice};

#[inline]
pub fn tag_cl<'a,'b>(rec:&'a[u8]) ->  Box<Fn(&'b[u8]) -> IResult<&'b[u8], &'b[u8]> + 'a> {
  Box::new(move |i: &'b[u8]| -> IResult<&'b[u8], &'b[u8]> {
    if i.len() >= rec.len() && &i[0..rec.len()] == rec {
      Done(&i[rec.len()..], &i[0..rec.len()])
    } else {
      Error(error_position!(ErrorKind::TagClosure, i))
    }
  })
}

#[cfg(feature = "std")]
#[inline]
pub fn print<T: Debug>(input: T) -> IResult<T, ()> {
  println!("{:?}", input);
  Done(input, ())
}

#[inline]
pub fn begin(input: &[u8]) -> IResult<(), &[u8]> {
  Done((), input)
}

pub fn crlf<T>(input:T) -> IResult<T,T> where
  T:Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
  T: InputIter,
  T: Compare<&'static str> {
    match input.compare("\r\n") {
      //FIXME: is this the right index?
      CompareResult::Ok         => {
        IResult::Done(input.slice(2..), input.slice(0..2))
      },
      CompareResult::Incomplete => IResult::Incomplete(Needed::Size(2)),
      CompareResult::Error      => IResult::Error(error_position!(ErrorKind::CrLf, input))
    }
}

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
// public methods
pub fn not_line_ending<T>(input:T) -> IResult<T,T> where
    T:Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputIter+InputLength,
    T: Compare<&'static str>,
    <T as InputIter>::Item: AsChar {
      match input.iter_elements().position(|item| {
        let c = item.as_char();
        c == '\r' || c == '\n'
      }) {
        None        => Done(input.slice(input.input_len()..), input),
        Some(index) => {
          let mut it = input.iter_elements();
          let nth    = it.nth(index).unwrap().as_char();
          if nth == '\r' {
            let sliced = input.slice(index..);
            let comp   = sliced.compare("\r\n");
            match comp {
              //FIXME: calculate the right index
              CompareResult::Incomplete => Incomplete(Needed::Unknown),
              CompareResult::Error      => Error(error_position!(ErrorKind::Tag, input)),
              CompareResult::Ok         => Done(input.slice(index..), input.slice(..index))
            }
          } else {
            Done(input.slice(index..), input.slice(..index))
          }
        }
      }
}

/// Recognizes an end of line (both '\n' and '\r\n')
pub fn line_ending<T>(input:T) -> IResult<T, T> where
    T: Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputIter+InputLength,
    T: Compare<&'static str> {

  match input.compare("\n") {
    CompareResult::Ok         => Done(input.slice(1..), input.slice(0..1)),
    CompareResult::Incomplete => Incomplete(Needed::Size(1)),
    CompareResult::Error      => match input.compare("\r\n") {
      //FIXME: is this the right index?
      CompareResult::Ok         => Done(input.slice(2..), input.slice(0..2)),
      CompareResult::Incomplete => Incomplete(Needed::Size(2)),
      CompareResult::Error      => Error(error_position!(ErrorKind::CrLf, input))
    }
  }
}

pub fn eol<T>(input:T) -> IResult<T,T> where
    T: Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputIter+InputLength,
    T: Compare<&'static str> {
  line_ending(input)
}

/// Tests if byte is ASCII alphabetic: A-Z, a-z
#[inline]
pub fn is_alphabetic(chr:u8) -> bool {
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
  (chr >= 0x30 && chr <= 0x39) ||
  (chr >= 0x41 && chr <= 0x46) ||
  (chr >= 0x61 && chr <= 0x66)
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
pub fn is_space(chr:u8) -> bool {
  chr == ' ' as u8 || chr == '\t' as u8
}

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
//pub filter!(alpha is_alphabetic)
//pub filter!(digit is_digit)
//pub filter!(hex_digit is_hex_digit)
//pub filter!(oct_digit is_oct_digit)
//pub filter!(alphanumeric is_alphanumeric)

/// Recognizes one or more lowercase and uppercase alphabetic characters: a-zA-Z
pub fn alpha<T>(input:T) -> IResult<T, T> where
    T: Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputIter+InputLength,
    <T as InputIter>::Item: AsChar {
  let input_length = input.input_len();
  if input_length == 0 {
    return Incomplete(Needed::Unknown);
  }

  for (idx, item) in input.iter_indices() {
    if ! item.is_alpha() {
      if idx == 0 {
        return Error(error_position!(ErrorKind::Alpha, input))
      } else {
        return Done(input.slice(idx..), input.slice(0..idx))
      }
    }
  }
  Done(input.slice(input_length..), input)
}

/// Recognizes one or more numerical characters: 0-9
pub fn digit<T>(input:T) -> IResult<T, T> where
    T: Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputIter+InputLength,
    <T as InputIter>::Item: AsChar {
  let input_length = input.input_len();
  if input_length == 0 {
    return Incomplete(Needed::Unknown);
  }

  for (idx, item) in input.iter_indices() {
    if ! item.is_dec_digit() {
      if idx == 0 {
        return Error(error_position!(ErrorKind::Digit, input))
      } else {
        return Done(input.slice(idx..), input.slice(0..idx))
      }
    }
  }
  Done(input.slice(input_length..), input)
}

/// Recognizes one or more hexadecimal numerical characters: 0-9, A-F, a-f
pub fn hex_digit<T>(input:T) -> IResult<T,T> where
    T: Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputIter+InputLength,
    <T as InputIter>::Item: AsChar {
  let input_length = input.input_len();
  if input_length == 0 {
    return Incomplete(Needed::Unknown);
  }

  for (idx, item) in input.iter_indices() {
    if ! item.is_hex_digit() {
      if idx == 0 {
        return Error(error_position!(ErrorKind::HexDigit, input))
      } else {
        return Done(input.slice(idx..), input.slice(0..idx))
      }
    }
  }
  Done(input.slice(input_length..), input)
}

/// Recognizes one or more octal characters: 0-7
pub fn oct_digit<T>(input:T) -> IResult<T,T> where
    T: Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputIter+InputLength,
    <T as InputIter>::Item: AsChar {
  let input_length = input.input_len();
  if input_length == 0 {
    return Incomplete(Needed::Unknown);
  }

  for (idx, item) in input.iter_indices() {
    if ! item.is_oct_digit() {
      if idx == 0 {
        return Error(error_position!(ErrorKind::OctDigit, input))
      } else {
        return Done(input.slice(idx..), input.slice(0..idx))
      }
    }
  }
  Done(input.slice(input_length..), input)
}

/// Recognizes one or more numerical and alphabetic characters: 0-9a-zA-Z
pub fn alphanumeric<T>(input:T) -> IResult<T,T> where
    T: Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputIter+InputLength,
    <T as InputIter>::Item: AsChar {
  let input_length = input.input_len();
  if input_length == 0 {
    return Incomplete(Needed::Unknown);
  }

  for (idx, item) in input.iter_indices() {
    if ! item.is_alphanum() {
      if idx == 0 {
        return Error(error_position!(ErrorKind::AlphaNumeric, input))
      } else {
        return Done(input.slice(idx..), input.slice(0..idx))
      }
    }
  }
  Done(input.slice(input_length..), input)
}

/// Recognizes one or more spaces and tabs
pub fn space<T>(input:T) -> IResult<T,T> where
    T: Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputIter+InputLength,
    <T as InputIter>::Item: AsChar {
  let input_length = input.input_len();
  if input_length == 0 {
    return Incomplete(Needed::Unknown);
  }

  for (idx, item) in input.iter_indices() {
    let chr = item.as_char();
    if ! (chr == ' ' || chr == '\t')  {
      if idx == 0 {
        return Error(error_position!(ErrorKind::Space, input))
      } else {
        return Done(input.slice(idx..), input.slice(0..idx))
      }
    }
  }
  Done(input.slice(input_length..), input)
}

/// Recognizes one or more spaces, tabs, carriage returns and line feeds
pub fn multispace<T>(input:T) -> IResult<T,T> where
    T: Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputIter+InputLength,
    <T as InputIter>::Item: AsChar {
  let input_length = input.input_len();
  if input_length == 0 {
    return Incomplete(Needed::Unknown);
  }

  for (idx, item) in input.iter_indices() {
    let chr = item.as_char();
    if ! (chr == ' ' || chr == '\t' || chr == '\r' || chr == '\n')  {
      if idx == 0 {
        return Error(error_position!(ErrorKind::MultiSpace, input))
      } else {
        return Done(input.slice(idx..), input.slice(0..idx))
      }
    }
  }
  Done(input.slice(input_length..), input)
}

pub fn sized_buffer(input:&[u8]) -> IResult<&[u8], &[u8]> {
  if input.is_empty() {
    return Incomplete(Needed::Unknown)
  }

  let len = input[0] as usize;

  if input.len() >= len + 1 {
    Done(&input[len+1..], &input[1..len+1])
  } else {
    Incomplete(Needed::Size(1 + len))
  }
}

/// Recognizes an unsigned 1 byte integer (equivalent to take!(1)
#[inline]
pub fn be_u8(i: &[u8]) -> IResult<&[u8], u8> {
  if i.len() < 1 {
    Incomplete(Needed::Size(1))
  } else {
    Done(&i[1..], i[0])
  }
}

/// Recognizes big endian unsigned 2 bytes integer
#[inline]
pub fn be_u16(i: &[u8]) -> IResult<&[u8], u16> {
  if i.len() < 2 {
    Incomplete(Needed::Size(2))
  } else {
    let res = ((i[0] as u16) << 8) + i[1] as u16;
    Done(&i[2..], res)
  }
}

/// Recognizes big endian unsigned 3 byte integer
#[inline]
pub fn be_u24(i: &[u8]) -> IResult<&[u8], u32> {
  if i.len() < 3 {
    Incomplete(Needed::Size(3))
  } else {
    let res = ((i[0] as u32) << 16) + ((i[1] as u32) << 8) + (i[2] as u32);
    Done(&i[3..], res)
  }
}

/// Recognizes big endian unsigned 4 bytes integer
#[inline]
pub fn be_u32(i: &[u8]) -> IResult<&[u8], u32> {
  if i.len() < 4 {
    Incomplete(Needed::Size(4))
  } else {
    let res = ((i[0] as u32) << 24) + ((i[1] as u32) << 16) + ((i[2] as u32) << 8) + i[3] as u32;
    Done(&i[4..], res)
  }
}

/// Recognizes big endian unsigned 8 bytes integer
#[inline]
pub fn be_u64(i: &[u8]) -> IResult<&[u8], u64> {
  if i.len() < 8 {
    Incomplete(Needed::Size(8))
  } else {
    let res = ((i[0] as u64) << 56) + ((i[1] as u64) << 48) + ((i[2] as u64) << 40) + ((i[3] as u64) << 32) +
      ((i[4] as u64) << 24) + ((i[5] as u64) << 16) + ((i[6] as u64) << 8) + i[7] as u64;
    Done(&i[8..], res)
  }
}

/// Recognizes a signed 1 byte integer (equivalent to take!(1)
#[inline]
pub fn be_i8(i:&[u8]) -> IResult<&[u8], i8> {
  map!(i, be_u8, | x | { x as i8 })
}

/// Recognizes big endian signed 2 bytes integer
#[inline]
pub fn be_i16(i:&[u8]) -> IResult<&[u8], i16> {
  map!(i, be_u16, | x | { x as i16 })
}

/// Recognizes big endian signed 3 bytes integer
#[inline]
pub fn be_i24(i: &[u8]) -> IResult<&[u8], i32> {
  // Same as the unsigned version but we need to sign-extend manually here
  map!(i, be_u24, | x | if x & 0x80_00_00 != 0 { (x | 0xff_00_00_00) as i32 } else { x as i32 })
}

/// Recognizes big endian signed 4 bytes integer
#[inline]
pub fn be_i32(i:&[u8]) -> IResult<&[u8], i32> {
  map!(i, be_u32, | x | { x as i32 })
}

/// Recognizes big endian signed 8 bytes integer
#[inline]
pub fn be_i64(i:&[u8]) -> IResult<&[u8], i64> {
  map!(i, be_u64, | x | { x as i64 })
}

/// Recognizes an unsigned 1 byte integer (equivalent to take!(1)
#[inline]
pub fn le_u8(i: &[u8]) -> IResult<&[u8], u8> {
  if i.len() < 1 {
    Incomplete(Needed::Size(1))
  } else {
    Done(&i[1..], i[0])
  }
}

/// Recognizes little endian unsigned 2 bytes integer
#[inline]
pub fn le_u16(i: &[u8]) -> IResult<&[u8], u16> {
  if i.len() < 2 {
    Incomplete(Needed::Size(2))
  } else {
    let res = ((i[1] as u16) << 8) + i[0] as u16;
    Done(&i[2..], res)
  }
}

/// Recognizes little endian unsigned 3 byte integer
#[inline]
pub fn le_u24(i: &[u8]) -> IResult<&[u8], u32> {
  if i.len() < 3 {
    Incomplete(Needed::Size(3))
  } else {
    let res = (i[0] as u32) + ((i[1] as u32) << 8) + ((i[2] as u32) << 16);
    Done(&i[3..], res)
  }
}

/// Recognizes little endian unsigned 4 bytes integer
#[inline]
pub fn le_u32(i: &[u8]) -> IResult<&[u8], u32> {
  if i.len() < 4 {
    Incomplete(Needed::Size(4))
  } else {
    let res = ((i[3] as u32) << 24) + ((i[2] as u32) << 16) + ((i[1] as u32) << 8) + i[0] as u32;
    Done(&i[4..], res)
  }
}

/// Recognizes little endian unsigned 8 bytes integer
#[inline]
pub fn le_u64(i: &[u8]) -> IResult<&[u8], u64> {
  if i.len() < 8 {
    Incomplete(Needed::Size(8))
  } else {
    let res = ((i[7] as u64) << 56) + ((i[6] as u64) << 48) + ((i[5] as u64) << 40) + ((i[4] as u64) << 32) +
      ((i[3] as u64) << 24) + ((i[2] as u64) << 16) + ((i[1] as u64) << 8) + i[0] as u64;
    Done(&i[8..], res)
  }
}

/// Recognizes a signed 1 byte integer (equivalent to take!(1)
#[inline]
pub fn le_i8(i:&[u8]) -> IResult<&[u8], i8> {
  map!(i, le_u8, | x | { x as i8 })
}

/// Recognizes little endian signed 2 bytes integer
#[inline]
pub fn le_i16(i:&[u8]) -> IResult<&[u8], i16> {
  map!(i, le_u16, | x | { x as i16 })
}

/// Recognizes little endian signed 3 bytes integer
#[inline]
pub fn le_i24(i: &[u8]) -> IResult<&[u8], i32> {
  // Same as the unsigned version but we need to sign-extend manually here
  map!(i, le_u24, | x | if x & 0x80_00_00 != 0 { (x | 0xff_00_00_00) as i32 } else { x as i32 })
}

/// Recognizes little endian signed 4 bytes integer
#[inline]
pub fn le_i32(i:&[u8]) -> IResult<&[u8], i32> {
  map!(i, le_u32, | x | { x as i32 })
}

/// Recognizes little endian signed 8 bytes integer
#[inline]
pub fn le_i64(i:&[u8]) -> IResult<&[u8], i64> {
  map!(i, le_u64, | x | { x as i64 })
}

/// Configurable endianness
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
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

/// Recognizes big endian 4 bytes floating point number
#[inline]
pub fn be_f32(input: &[u8]) -> IResult<&[u8], f32> {
  match be_u32(input) {
    Error(e)      => Error(e),
    Incomplete(e) => Incomplete(e),
    Done(i,o) => {
      unsafe {
        Done(i, transmute::<u32, f32>(o))
      }
    }
  }
}

/// Recognizes big endian 8 bytes floating point number
#[inline]
pub fn be_f64(input: &[u8]) -> IResult<&[u8], f64> {
  match be_u64(input) {
    Error(e)      => Error(e),
    Incomplete(e) => Incomplete(e),
    Done(i,o) => {
      unsafe {
        Done(i, transmute::<u64, f64>(o))
      }
    }
  }
}

/// Recognizes little endian 4 bytes floating point number
#[inline]
pub fn le_f32(input: &[u8]) -> IResult<&[u8], f32> {
  match le_u32(input) {
    Error(e)      => Error(e),
    Incomplete(e) => Incomplete(e),
    Done(i,o) => {
      unsafe {
        Done(i, transmute::<u32, f32>(o))
      }
    }
  }
}

/// Recognizes little endian 8 bytes floating point number
#[inline]
pub fn le_f64(input: &[u8]) -> IResult<&[u8], f64> {
  match le_u64(input) {
    Error(e)      => Error(e),
    Incomplete(e) => Incomplete(e),
    Done(i,o) => {
      unsafe {
        Done(i, transmute::<u64, f64>(o))
      }
    }
  }
}

/// Recognizes a hex-encoded integer
#[inline]
pub fn hex_u32(input: &[u8]) -> IResult<&[u8], u32> {
  match is_a!(input, &b"0123456789abcdefABCDEF"[..]) {
    Error(e)    => Error(e),
    Incomplete(e) => Incomplete(e),
    Done(i,o) => {
      let mut res = 0u32;

      // Do not parse more than 8 characters for a u32
      let mut remaining = i;
      let mut parsed    = o;
      if o.len() > 8 {
        remaining = &input[8..];
        parsed    = &input[..8];
      }

      for &e in parsed {
        let digit = e as char;
        let value = digit.to_digit(16).unwrap_or(0);
        res = value + (res << 4);
      }
      Done(remaining, res)
    }
  }
}

/// Recognizes non empty buffers
#[inline]
pub fn non_empty<T>(input:T) -> IResult<T,T> where
    T: Slice<Range<usize>>+Slice<RangeFrom<usize>>+Slice<RangeTo<usize>>,
    T: InputLength {
  if input.input_len() == 0 {
    Error(error_position!(ErrorKind::NonEmpty, input))
  } else {
    Done(input.slice(input.input_len()..), input)
  }
}

/// Return the remaining input.
#[inline]
pub fn rest(input: &[u8]) -> IResult<&[u8], &[u8]> {
    IResult::Done(&input[input.len()..], input)
}

/// Return the remaining input, for strings.
#[inline]
pub fn rest_s(input: &str) -> IResult<&str, &str> {
    IResult::Done(&input[input.len()..], input)
}

/// Recognizes floating point number in a byte string and returns a f32
#[cfg(feature = "std")]
pub fn float(input: &[u8]) -> IResult<&[u8],f32> {
  flat_map!(input,
    recognize!(
      tuple!(
        opt!(alt!(tag!("+") | tag!("-"))),
        alt!(
          delimited!(digit, tag!("."), opt!(digit))
          | delimited!(opt!(digit), tag!("."), digit)
        ),
        opt!(complete!(tuple!(
          alt!(tag!("e") | tag!("E")),
          opt!(alt!(tag!("+") | tag!("-"))),
          digit
          )
        ))
      )
    ),
    parse_to!(f32)
  )
}

/// Recognizes floating point number in a string and returns a f32
#[cfg(feature = "std")]
pub fn float_s(input: &str) -> IResult<&str,f32> {
  flat_map!(input,
    recognize!(
      tuple!(
        opt!(alt!(tag!("+") | tag!("-"))),
        alt!(
          delimited!(digit, tag!("."), opt!(digit))
          | delimited!(opt!(digit), tag!("."), digit)
        ),
        opt!(complete!(tuple!(
          alt!(tag!("e") | tag!("E")),
          opt!(alt!(tag!("+") | tag!("-"))),
          digit
          )
        ))
      )
    ),
    parse_to!(f32)
  )
}

/// Recognizes floating point number in a byte string and returns a f64
#[cfg(feature = "std")]
pub fn double(input: &[u8]) -> IResult<&[u8],f64> {
  flat_map!(input,
    recognize!(
      tuple!(
        opt!(alt!(tag!("+") | tag!("-"))),
        alt!(
          delimited!(digit, tag!("."), opt!(digit))
          | delimited!(opt!(digit), tag!("."), digit)
        ),
        opt!(complete!(tuple!(
          alt!(tag!("e") | tag!("E")),
          opt!(alt!(tag!("+") | tag!("-"))),
          digit
          )
        ))
      )
    ),
    parse_to!(f64)
  )
}

/// Recognizes floating point number in a string and returns a f64
#[cfg(feature = "std")]
pub fn double_s(input: &str) -> IResult<&str,f64> {
  flat_map!(input,
    recognize!(
      tuple!(
        opt!(alt!(tag!("+") | tag!("-"))),
        alt!(
          delimited!(digit, tag!("."), opt!(digit))
          | delimited!(opt!(digit), tag!("."), digit)
        ),
        opt!(complete!(tuple!(
          alt!(tag!("e") | tag!("E")),
          opt!(alt!(tag!("+") | tag!("-"))),
          digit
          )
        ))
      )
    ),
    parse_to!(f64)
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Needed,IResult};
  use util::ErrorKind;

  #[test]
  fn tag_closure() {
    let x = tag_cl(&b"abcd"[..]);
    let r = x(&b"abcdabcdefgh"[..]);
    assert_eq!(r, Done(&b"abcdefgh"[..], &b"abcd"[..]));

    let r2 = x(&b"abcefgh"[..]);
    assert_eq!(r2, Error(error_position!(ErrorKind::TagClosure, &b"abcefgh"[..])));
  }

  #[test]
  fn character() {
    let empty: &[u8] = b"";
    let a: &[u8] = b"abcd";
    let b: &[u8] = b"1234";
    let c: &[u8] = b"a123";
    let d: &[u8] = "azé12".as_bytes();
    let e: &[u8] = b" ";
    assert_eq!(alpha(a), Done(empty, a));
    assert_eq!(alpha(b), Error(error_position!(ErrorKind::Alpha,b)));
    assert_eq!(alpha(c), Done(&c[1..], &b"a"[..]));
    assert_eq!(alpha(d), Done("é12".as_bytes(), &b"az"[..]));
    assert_eq!(digit(a), Error(error_position!(ErrorKind::Digit,a)));
    assert_eq!(digit(b), Done(empty, b));
    assert_eq!(digit(c), Error(error_position!(ErrorKind::Digit,c)));
    assert_eq!(digit(d), Error(error_position!(ErrorKind::Digit,d)));
    assert_eq!(hex_digit(a), Done(empty, a));
    assert_eq!(hex_digit(b), Done(empty, b));
    assert_eq!(hex_digit(c), Done(empty, c));
    assert_eq!(hex_digit(d), Done("zé12".as_bytes(), &b"a"[..]));
    assert_eq!(hex_digit(e), Error(error_position!(ErrorKind::HexDigit,e)));
    assert_eq!(oct_digit(a), Error(error_position!(ErrorKind::OctDigit,a)));
    assert_eq!(oct_digit(b), Done(empty, b));
    assert_eq!(oct_digit(c), Error(error_position!(ErrorKind::OctDigit,c)));
    assert_eq!(oct_digit(d), Error(error_position!(ErrorKind::OctDigit,d)));
    assert_eq!(alphanumeric(a), Done(empty, a));
    assert_eq!(fix_error!(b,(), alphanumeric), Done(empty, b));
    assert_eq!(alphanumeric(c), Done(empty, c));
    assert_eq!(alphanumeric(d), Done("é12".as_bytes(), &b"az"[..]));
    assert_eq!(space(e), Done(&b""[..], &b" "[..]));
  }

  #[test]
  fn character_s() {
    let empty = "";
    let a     = "abcd";
    let b     = "1234";
    let c     = "a123";
    let d     = "azé12";
    let e     = " ";
    assert_eq!(alpha(a), Done(empty, a));
    assert_eq!(alpha(b), Error(error_position!(ErrorKind::Alpha,b)));
    assert_eq!(alpha(c), Done(&c[1..], &"a"[..]));
    assert_eq!(alpha(d), Done("12", &"azé"[..]));
    assert_eq!(digit(a), Error(error_position!(ErrorKind::Digit,a)));
    assert_eq!(digit(b), Done(empty, b));
    assert_eq!(digit(c), Error(error_position!(ErrorKind::Digit,c)));
    assert_eq!(digit(d), Error(error_position!(ErrorKind::Digit,d)));
    assert_eq!(hex_digit(a), Done(empty, a));
    assert_eq!(hex_digit(b), Done(empty, b));
    assert_eq!(hex_digit(c), Done(empty, c));
    assert_eq!(hex_digit(d), Done("zé12", &"a"[..]));
    assert_eq!(hex_digit(e), Error(error_position!(ErrorKind::HexDigit,e)));
    assert_eq!(oct_digit(a), Error(error_position!(ErrorKind::OctDigit,a)));
    assert_eq!(oct_digit(b), Done(empty, b));
    assert_eq!(oct_digit(c), Error(error_position!(ErrorKind::OctDigit,c)));
    assert_eq!(oct_digit(d), Error(error_position!(ErrorKind::OctDigit,d)));
    assert_eq!(alphanumeric(a), Done(empty, a));
    assert_eq!(fix_error!(b,(), alphanumeric), Done(empty, b));
    assert_eq!(alphanumeric(c), Done(empty, c));
    assert_eq!(alphanumeric(d), Done("", &"azé12"[..]));
    assert_eq!(space(e), Done(&""[..], &" "[..]));
  }

  use util::Offset;
  #[test]
  fn offset() {
    let a = &b"abcd"[..];
    let b = &b"1234"[..];
    let c = &b"a123"[..];
    let d = &b" \t"[..];
    let e = &b" \t\r\n"[..];
    let f = &b"123abcDEF"[..];

    match alpha(a) {
        Done(i, _)  => { assert_eq!(a.offset(i) + i.len(), a.len()); }
        _           => { panic!("wrong return type in offset test for alpha") }
    }
    match digit(b) {
        Done(i, _)  => { assert_eq!(b.offset(i) + i.len(), b.len()); }
        _           => { panic!("wrong return type in offset test for digit") }
    }
    match alphanumeric(c) {
        Done(i, _)  => { assert_eq!(c.offset(i) + i.len(), c.len()); }
        _           => { panic!("wrong return type in offset test for alphanumeric") }
    }
    match space(d) {
        Done(i, _)  => { assert_eq!(d.offset(i) + i.len(), d.len()); }
        _           => { panic!("wrong return type in offset test for space") }
    }
    match multispace(e) {
        Done(i, _)  => { assert_eq!(e.offset(i) + i.len(), e.len()); }
        _           => { panic!("wrong return type in offset test for multispace") }
    }
    match hex_digit(f) {
        Done(i, _)  => { assert_eq!(f.offset(i) + i.len(), f.len()); }
        _           => { panic!("wrong return type in offset test for hex_digit") }
    }
    match oct_digit(f) {
        Done(i, _)  => { assert_eq!(f.offset(i) + i.len(), f.len()); }
        _           => { panic!("wrong return type in offset test for oct_digit") }
    }
  }

  #[test]
  fn is_not_line_ending_bytes() {
    let a: &[u8] = b"ab12cd\nefgh";
    assert_eq!(not_line_ending(a), Done(&b"\nefgh"[..], &b"ab12cd"[..]));

    let b: &[u8] = b"ab12cd\nefgh\nijkl";
    assert_eq!(not_line_ending(b), Done(&b"\nefgh\nijkl"[..], &b"ab12cd"[..]));

    let c: &[u8] = b"ab12cd\r\nefgh\nijkl";
    assert_eq!(not_line_ending(c), Done(&b"\r\nefgh\nijkl"[..], &b"ab12cd"[..]));

    let d: &[u8] = b"ab12cd";
    assert_eq!(not_line_ending(d), Done(&b""[..], d));
  }

  #[test]
  fn is_not_line_ending_str() {
    /*
    let a: &str = "ab12cd\nefgh";
    assert_eq!(not_line_ending(a), Done(&"\nefgh"[..], &"ab12cd"[..]));

    let b: &str = "ab12cd\nefgh\nijkl";
    assert_eq!(not_line_ending(b), Done(&"\nefgh\nijkl"[..], &"ab12cd"[..]));

    let c: &str = "ab12cd\r\nefgh\nijkl";
    assert_eq!(not_line_ending(c), Done(&"\r\nefgh\nijkl"[..], &"ab12cd"[..]));

    let d = "βèƒôřè\nÂßÇáƒƭèř";
    assert_eq!(not_line_ending(d), Done(&"\nÂßÇáƒƭèř"[..], &"βèƒôřè"[..]));

    let e = "βèƒôřè\r\nÂßÇáƒƭèř";
    assert_eq!(not_line_ending(e), Done(&"\r\nÂßÇáƒƭèř"[..], &"βèƒôřè"[..]));
    */

    let f = "βèƒôřè\rÂßÇáƒƭèř";
    assert_eq!(not_line_ending(f), Error(error_position!(ErrorKind::Tag,f)));

    let g: &str = "ab12cd";
    assert_eq!(not_line_ending(g), Done("", g));
  }

  #[test]
  #[cfg(feature = "std")]
  fn buffer_with_size() {
    let i:Vec<u8> = vec![7,8];
    let o:Vec<u8> = vec![4,5,6];
    //let arr:[u8; 6usize] = [3, 4, 5, 6, 7, 8];
    let arr:[u8; 6usize] = [3, 4, 5, 6, 7, 8];
    let res = sized_buffer(&arr[..]);
    assert_eq!(res, Done(&i[..], &o[..]))
  }

  /*#[test]
  fn t1() {
    let v1:Vec<u8> = vec![1,2,3];
    let v2:Vec<u8> = vec![4,5,6];
    let d = Done(&v1[..], &v2[..]);
    let res = d.flat_map(print);
    assert_eq!(res, Done(&v2[..], ()));
  }*/

  #[test]
  fn i8_tests() {
    assert_eq!(be_i8(&[0x00]), Done(&b""[..], 0));
    assert_eq!(be_i8(&[0x7f]), Done(&b""[..], 127));
    assert_eq!(be_i8(&[0xff]), Done(&b""[..], -1));
    assert_eq!(be_i8(&[0x80]), Done(&b""[..], -128));
  }

  #[test]
  fn i16_tests() {
    assert_eq!(be_i16(&[0x00, 0x00]), Done(&b""[..], 0));
    assert_eq!(be_i16(&[0x7f, 0xff]), Done(&b""[..], 32767_i16));
    assert_eq!(be_i16(&[0xff, 0xff]), Done(&b""[..], -1));
    assert_eq!(be_i16(&[0x80, 0x00]), Done(&b""[..], -32768_i16));
  }

  #[test]
  fn u24_tests() {
    assert_eq!(be_u24(&[0x00, 0x00, 0x00]), Done(&b""[..], 0));
    assert_eq!(be_u24(&[0x00, 0xFF, 0xFF]), Done(&b""[..], 65535_u32));
    assert_eq!(be_u24(&[0x12, 0x34, 0x56]), Done(&b""[..], 1193046_u32));
  }

  #[test]
  fn i24_tests() {
    assert_eq!(be_i24(&[0xFF, 0xFF, 0xFF]), Done(&b""[..], -1_i32));
    assert_eq!(be_i24(&[0xFF, 0x00, 0x00]), Done(&b""[..], -65536_i32));
    assert_eq!(be_i24(&[0xED, 0xCB, 0xAA]), Done(&b""[..], -1193046_i32));
  }

  #[test]
  fn i32_tests() {
    assert_eq!(be_i32(&[0x00, 0x00, 0x00, 0x00]), Done(&b""[..], 0));
    assert_eq!(be_i32(&[0x7f, 0xff, 0xff, 0xff]), Done(&b""[..], 2147483647_i32));
    assert_eq!(be_i32(&[0xff, 0xff, 0xff, 0xff]), Done(&b""[..], -1));
    assert_eq!(be_i32(&[0x80, 0x00, 0x00, 0x00]), Done(&b""[..], -2147483648_i32));
  }

  #[test]
  fn i64_tests() {
    assert_eq!(be_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]), Done(&b""[..], 0));
    assert_eq!(be_i64(&[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]), Done(&b""[..], 9223372036854775807_i64));
    assert_eq!(be_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]), Done(&b""[..], -1));
    assert_eq!(be_i64(&[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]), Done(&b""[..], -9223372036854775808_i64));
  }

  #[test]
  fn le_i8_tests() {
    assert_eq!(le_i8(&[0x00]), Done(&b""[..], 0));
    assert_eq!(le_i8(&[0x7f]), Done(&b""[..], 127));
    assert_eq!(le_i8(&[0xff]), Done(&b""[..], -1));
    assert_eq!(le_i8(&[0x80]), Done(&b""[..], -128));
  }

  #[test]
  fn le_i16_tests() {
    assert_eq!(le_i16(&[0x00, 0x00]), Done(&b""[..], 0));
    assert_eq!(le_i16(&[0xff, 0x7f]), Done(&b""[..], 32767_i16));
    assert_eq!(le_i16(&[0xff, 0xff]), Done(&b""[..], -1));
    assert_eq!(le_i16(&[0x00, 0x80]), Done(&b""[..], -32768_i16));
  }

  #[test]
  fn le_u24_tests() {
    assert_eq!(le_u24(&[0x00, 0x00, 0x00]), Done(&b""[..], 0));
    assert_eq!(le_u24(&[0xFF, 0xFF, 0x00]), Done(&b""[..], 65535_u32));
    assert_eq!(le_u24(&[0x56, 0x34, 0x12]), Done(&b""[..], 1193046_u32));
  }

  #[test]
  fn le_i24_tests() {
    assert_eq!(le_i24(&[0xFF, 0xFF, 0xFF]), Done(&b""[..], -1_i32));
    assert_eq!(le_i24(&[0x00, 0x00, 0xFF]), Done(&b""[..], -65536_i32));
    assert_eq!(le_i24(&[0xAA, 0xCB, 0xED]), Done(&b""[..], -1193046_i32));
  }

  #[test]
  fn le_i32_tests() {
    assert_eq!(le_i32(&[0x00, 0x00, 0x00, 0x00]), Done(&b""[..], 0));
    assert_eq!(le_i32(&[0xff, 0xff, 0xff, 0x7f]), Done(&b""[..], 2147483647_i32));
    assert_eq!(le_i32(&[0xff, 0xff, 0xff, 0xff]), Done(&b""[..], -1));
    assert_eq!(le_i32(&[0x00, 0x00, 0x00, 0x80]), Done(&b""[..], -2147483648_i32));
  }

  #[test]
  fn le_i64_tests() {
    assert_eq!(le_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]), Done(&b""[..], 0));
    assert_eq!(le_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]), Done(&b""[..], 9223372036854775807_i64));
    assert_eq!(le_i64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]), Done(&b""[..], -1));
    assert_eq!(le_i64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80]), Done(&b""[..], -9223372036854775808_i64));
  }

  #[test]
  fn be_f32_tests() {
    assert_eq!(be_f32(&[0x00, 0x00, 0x00, 0x00]), Done(&b""[..], 0_f32));
    assert_eq!(be_f32(&[0x4d, 0x31, 0x1f, 0xd8]), Done(&b""[..], 185728392_f32));
  }

  #[test]
  fn be_f64_tests() {
    assert_eq!(be_f64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]), Done(&b""[..], 0_f64));
    assert_eq!(be_f64(&[0x41, 0xa6, 0x23, 0xfb, 0x10, 0x00, 0x00, 0x00]), Done(&b""[..], 185728392_f64));
  }

  #[test]
  fn le_f32_tests() {
    assert_eq!(le_f32(&[0x00, 0x00, 0x00, 0x00]), Done(&b""[..], 0_f32));
    assert_eq!(le_f32(&[0xd8, 0x1f, 0x31, 0x4d]), Done(&b""[..], 185728392_f32));
  }

  #[test]
  fn le_f64_tests() {
    assert_eq!(le_f64(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]), Done(&b""[..], 0_f64));
    assert_eq!(le_f64(&[0x00, 0x00, 0x00, 0x10, 0xfb, 0x23, 0xa6, 0x41]), Done(&b""[..], 185728392_f64));
  }

  #[test]
  fn hex_u32_tests() {
    assert_eq!(hex_u32(&b""[..]), Done(&b""[..], 0));
    assert_eq!(hex_u32(&b"ff"[..]), Done(&b""[..], 255));
    assert_eq!(hex_u32(&b"1be2"[..]), Done(&b""[..], 7138));
    assert_eq!(hex_u32(&b"c5a31be2"[..]), Done(&b""[..], 3315801058));
    assert_eq!(hex_u32(&b"C5A31be2"[..]), Done(&b""[..], 3315801058));
    assert_eq!(hex_u32(&b"00c5a31be2"[..]), Done(&b"e2"[..], 12952347));
    assert_eq!(hex_u32(&b"c5a31be201"[..]), Done(&b"01"[..], 3315801058));
    assert_eq!(hex_u32(&b"ffffffff"[..]), Done(&b""[..], 4294967295));
    assert_eq!(hex_u32(&b"0x1be2"[..]), Done(&b"x1be2"[..], 0));
  }

    #[test]
    fn end_of_input() {
        let not_over = &b"Hello, world!"[..];
        let is_over = &b""[..];
        named!(eof_test, eof!());

        let res_not_over = eof_test(not_over);
        assert_eq!(res_not_over, Error(error_position!(ErrorKind::Eof, not_over)));

        let res_over = eof_test(is_over);
        assert_eq!(res_over, Done(is_over, is_over));
    }

  #[test]
  fn configurable_endianness() {
    named!(be_tst16<u16>, u16!(Endianness::Big));
    named!(le_tst16<u16>, u16!(Endianness::Little));
    assert_eq!(be_tst16(&[0x80, 0x00]), Done(&b""[..], 32768_u16));
    assert_eq!(le_tst16(&[0x80, 0x00]), Done(&b""[..], 128_u16));

    named!(be_tst32<u32>, u32!(Endianness::Big));
    named!(le_tst32<u32>, u32!(Endianness::Little));
    assert_eq!(be_tst32(&[0x12, 0x00, 0x60, 0x00]), Done(&b""[..], 302014464_u32));
    assert_eq!(le_tst32(&[0x12, 0x00, 0x60, 0x00]), Done(&b""[..], 6291474_u32));

    named!(be_tst64<u64>, u64!(Endianness::Big));
    named!(le_tst64<u64>, u64!(Endianness::Little));
    assert_eq!(be_tst64(&[0x12, 0x00, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]), Done(&b""[..], 1297142246100992000_u64));
    assert_eq!(le_tst64(&[0x12, 0x00, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]), Done(&b""[..], 36028874334666770_u64));

    named!(be_tsti16<i16>, i16!(Endianness::Big));
    named!(le_tsti16<i16>, i16!(Endianness::Little));
    assert_eq!(be_tsti16(&[0x00, 0x80]), Done(&b""[..], 128_i16));
    assert_eq!(le_tsti16(&[0x00, 0x80]), Done(&b""[..], -32768_i16));

    named!(be_tsti32<i32>, i32!(Endianness::Big));
    named!(le_tsti32<i32>, i32!(Endianness::Little));
    assert_eq!(be_tsti32(&[0x00, 0x12, 0x60, 0x00]), Done(&b""[..], 1204224_i32));
    assert_eq!(le_tsti32(&[0x00, 0x12, 0x60, 0x00]), Done(&b""[..], 6296064_i32));

    named!(be_tsti64<i64>, i64!(Endianness::Big));
    named!(le_tsti64<i64>, i64!(Endianness::Little));
    assert_eq!(be_tsti64(&[0x00, 0xFF, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]), Done(&b""[..], 71881672479506432_i64));
    assert_eq!(le_tsti64(&[0x00, 0xFF, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]), Done(&b""[..], 36028874334732032_i64));

  }

  #[test]
  #[cfg(feature = "std")]
  fn manual_configurable_endianness_test() {
    let x = 1;
    let int_parse: Box<Fn(&[u8]) -> IResult<&[u8], u16> > = if x == 2 {
      Box::new(be_u16)
    } else {
      Box::new(le_u16)
    };
    println!("{:?}", int_parse(&b"3"[..]));
    assert_eq!(int_parse(&[0x80, 0x00]), Done(&b""[..], 128_u16));
  }

  #[allow(dead_code)]
  fn custom_error(input: &[u8]) -> IResult<&[u8], &[u8], ()> {
    fix_error!(input, (), alphanumeric)
  }

  #[test]
  fn hex_digit_test() {
    let empty = &b""[..];

    let i = &b"0123456789abcdefABCDEF"[..];
    assert_eq!(hex_digit(i), Done(empty, i));

    let i = &b"g"[..];
    assert_eq!(hex_digit(i), Error(error_position!(ErrorKind::HexDigit,i)));

    let i = &b"G"[..];
    assert_eq!(hex_digit(i), Error(error_position!(ErrorKind::HexDigit,i)));

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
    let empty = &b""[..];

    let i = &b"01234567"[..];
    assert_eq!(oct_digit(i), Done(empty, i));

    let i = &b"8"[..];
    assert_eq!(oct_digit(i), Error(error_position!(ErrorKind::OctDigit,i)));

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
    named!(take_full_line<(&[u8], &[u8])>, tuple!(not_line_ending, line_ending));
    let input = b"abc\r\n";
    let output = take_full_line(input);
    assert_eq!(output, Done(&b""[..], (&b"abc"[..], &b"\r\n"[..])));
  }

  #[test]
  fn full_line_unix() {
    named!(take_full_line<(&[u8], &[u8])>, tuple!(not_line_ending, line_ending));
    let input = b"abc\n";
    let output = take_full_line(input);
    assert_eq!(output, Done(&b""[..], (&b"abc"[..], &b"\n"[..])));
  }

  #[test]
  fn check_windows_lineending() {
    let input = b"\r\n";
    let output = line_ending(&input[..]);
    assert_eq!(output, Done(&b""[..], &b"\r\n"[..]));
  }

  #[test]
  fn check_unix_lineending() {
    let input = b"\n";
    let output = line_ending(&input[..]);
    assert_eq!(output, Done(&b""[..], &b"\n"[..]));
  }

  #[test]
  fn cr_lf() {
    assert_eq!(crlf(&b"\r\na"[..]), Done(&b"a"[..], &b"\r\n"[..]));
    assert_eq!(crlf(&b"\r"[..]),    Incomplete(Needed::Size(2)));
    assert_eq!(crlf(&b"\ra"[..]),   Error(error_position!(ErrorKind::CrLf, &b"\ra"[..])));

    assert_eq!(crlf("\r\na"), Done("a", "\r\n"));
    assert_eq!(crlf("\r"),    Incomplete(Needed::Size(2)));
    assert_eq!(crlf("\ra"),   Error(error_position!(ErrorKind::CrLf, "\ra")));
  }

  #[test]
  fn end_of_line() {
    assert_eq!(eol(&b"\na"[..]),   Done(&b"a"[..], &b"\n"[..]));
    assert_eq!(eol(&b"\r\na"[..]), Done(&b"a"[..], &b"\r\n"[..]));
    assert_eq!(eol(&b"\r"[..]),    Incomplete(Needed::Size(2)));
    assert_eq!(eol(&b"\ra"[..]),   Error(error_position!(ErrorKind::CrLf, &b"\ra"[..])));

    assert_eq!(eol("\na"),   Done("a", "\n"));
    assert_eq!(eol("\r\na"), Done("a", "\r\n"));
    assert_eq!(eol("\r"),    Incomplete(Needed::Size(2)));
    assert_eq!(eol("\ra"),   Error(error_position!(ErrorKind::CrLf, "\ra")));
  }

  #[test]
  #[cfg(feature = "std")]
  fn float_test() {
    assert_eq!(float(&b"+3.14"[..]),   Done(&b""[..], 3.14));
    assert_eq!(float_s(&"3.14"[..]),   Done(&""[..], 3.14));
    assert_eq!(double(&b"3.14"[..]),   Done(&b""[..], 3.14));
    assert_eq!(double_s(&"3.14"[..]),   Done(&""[..], 3.14));

    assert_eq!(float(&b"-1.234E-12"[..]),   Done(&b""[..], -1.234E-12));
    assert_eq!(float_s(&"-1.234E-12"[..]),   Done(&""[..], -1.234E-12));
    assert_eq!(double(&b"-1.234E-12"[..]),   Done(&b""[..], -1.234E-12));
    assert_eq!(double_s(&"-1.234E-12"[..]),   Done(&""[..], -1.234E-12));
  }
}
