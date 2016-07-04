//! Useful parser combinators
//!
//! A number of useful parser combinators have already been implemented.
//! Some of them use macros, other are implemented through functions.
//! Hopefully, the syntax will converge to onely one way in the future,
//! but the macros system makes no promises.
//!

#[cfg(feature = "core")]
use std::prelude::v1::*;
use std::boxed::Box;

use std::fmt::Debug;
use internal::*;
use internal::IResult::*;
use internal::Err::*;
use util::{ErrorKind,IterIndices,AsChar,InputLength};
use std::mem::transmute;

#[inline]
pub fn tag_cl<'a,'b>(rec:&'a[u8]) ->  Box<Fn(&'b[u8]) -> IResult<&'b[u8], &'b[u8]> + 'a> {
  Box::new(move |i: &'b[u8]| -> IResult<&'b[u8], &'b[u8]> {
    if i.len() >= rec.len() && &i[0..rec.len()] == rec {
      Done(&i[rec.len()..], &i[0..rec.len()])
    } else {
      Error(Position(ErrorKind::TagClosure, i))
    }
  })
}

#[cfg(not(feature = "core"))]
#[inline]
pub fn print<T: Debug>(input: T) -> IResult<T, ()> {
  println!("{:?}", input);
  Done(input, ())
}

#[inline]
pub fn begin(input: &[u8]) -> IResult<(), &[u8]> {
  Done((), input)
}

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
// public methods
//pub is_not!(line_ending b"\r\n")
pub fn not_line_ending(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for (idx, item) in input.iter().enumerate() {
    for &i in b"\r\n".iter() {
      if *item == i {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(&input[input.len()..], input)
}

named!(tag_ln, tag!("\n"));

/// Recognizes a line feed
#[inline]
pub fn line_ending(input:&[u8]) -> IResult<&[u8], &[u8]> {
  tag_ln(input)
}

#[inline]
pub fn is_alphabetic(chr:u8) -> bool {
  (chr >= 0x41 && chr <= 0x5A) || (chr >= 0x61 && chr <= 0x7A)
}

#[inline]
pub fn is_digit(chr: u8) -> bool {
  chr >= 0x30 && chr <= 0x39
}

#[inline]
pub fn is_hex_digit(chr: u8) -> bool {
  (chr >= 0x30 && chr <= 0x39) ||
  (chr >= 0x41 && chr <= 0x46) ||
  (chr >= 0x61 && chr <= 0x66)
}

#[inline]
pub fn is_oct_digit(chr: u8) -> bool {
  chr >= 0x30 && chr <= 0x37
}

#[inline]
pub fn is_alphanumeric(chr: u8) -> bool {
  is_alphabetic(chr) || is_digit(chr)
}

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

use std::ops::{Index,Range,RangeFrom};
/// Recognizes lowercase and uppercase alphabetic characters: a-zA-Z
pub fn alpha<'a, T: ?Sized>(input:&'a T) -> IResult<&'a T, &'a T> where
    T:Index<Range<usize>, Output=T>+Index<RangeFrom<usize>, Output=T>,
    &'a T: IterIndices+InputLength {
  let input_length = input.input_len();
  if input_length == 0 {
    return Error(Position(ErrorKind::Alpha, input))
  }

  for (idx, item) in input.iter_indices() {
    if ! item.is_alpha() {
      if idx == 0 {
        return Error(Position(ErrorKind::Alpha, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(&input[input_length..], input)
}

/// Recognizes numerical characters: 0-9
pub fn digit<'a, T: ?Sized>(input:&'a T) -> IResult<&'a T, &'a T> where
    T:Index<Range<usize>, Output=T>+Index<RangeFrom<usize>, Output=T>,
    &'a T: IterIndices+InputLength {
  let input_length = input.input_len();
  if input_length == 0 {
    return Error(Position(ErrorKind::Digit, input))
  }

  for (idx, item) in input.iter_indices() {
    if ! item.is_0_to_9() {
      if idx == 0 {
        return Error(Position(ErrorKind::Digit, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(&input[input_length..], input)
}

/// Recognizes hexadecimal numerical characters: 0-9, A-F, a-f
pub fn hex_digit<'a, T: ?Sized>(input:&'a T) -> IResult<&'a T, &'a T> where
    T:Index<Range<usize>, Output=T>+Index<RangeFrom<usize>, Output=T>,
    &'a T: IterIndices+InputLength {
  let input_length = input.input_len();
  if input_length == 0 {
    return Error(Position(ErrorKind::HexDigit, input))
  }

  for (idx, item) in input.iter_indices() {
    if ! item.is_hex_digit() {
      if idx == 0 {
        return Error(Position(ErrorKind::HexDigit, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(&input[input_length..], input)
}

/// Recognizes octal characters: 0-7
pub fn oct_digit<'a, T: ?Sized>(input:&'a T) -> IResult<&'a T, &'a T> where
    T:Index<Range<usize>, Output=T>+Index<RangeFrom<usize>, Output=T>,
    &'a T: IterIndices+InputLength {
  let input_length = input.input_len();
  if input_length == 0 {
    return Error(Position(ErrorKind::OctDigit, input))
  }

  for (idx, item) in input.iter_indices() {
    if ! item.is_oct_digit() {
      if idx == 0 {
        return Error(Position(ErrorKind::OctDigit, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(&input[input_length..], input)
}

/// Recognizes numerical and alphabetic characters: 0-9a-zA-Z
pub fn alphanumeric<'a, T: ?Sized>(input:&'a T) -> IResult<&'a T, &'a T> where
    T:Index<Range<usize>, Output=T>+Index<RangeFrom<usize>, Output=T>,
    &'a T: IterIndices+InputLength {
  let input_length = input.input_len();
  if input_length == 0 {
    return Error(Position(ErrorKind::AlphaNumeric, input));
  }

  for (idx, item) in input.iter_indices() {
    if ! item.is_alphanum() {
      if idx == 0 {
        return Error(Position(ErrorKind::AlphaNumeric, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(&input[input_length..], input)
}

/// Recognizes spaces and tabs
pub fn space<'a, T: ?Sized>(input:&'a T) -> IResult<&'a T, &'a T> where
    T:Index<Range<usize>, Output=T>+Index<RangeFrom<usize>, Output=T>,
    &'a T: IterIndices+InputLength {
  let input_length = input.input_len();
  if input_length == 0 {
    return Error(Position(ErrorKind::Space, input));
  }

  for (idx, item) in input.iter_indices() {
    let chr = item.as_char();
    if ! (chr == ' ' || chr == '\t')  {
      if idx == 0 {
        return Error(Position(ErrorKind::Space, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(&input[input_length..], input)
}

/// Recognizes spaces, tabs, carriage returns and line feeds
pub fn multispace<'a, T: ?Sized>(input:&'a T) -> IResult<&'a T, &'a T> where
    T:Index<Range<usize>, Output=T>+Index<RangeFrom<usize>, Output=T>,
    &'a T: IterIndices+InputLength {
  let input_length = input.input_len();
  if input_length == 0 {
    return Error(Position(ErrorKind::MultiSpace, input));
  }

  for (idx, item) in input.iter_indices() {
    let chr = item.as_char();
    if ! (chr == ' ' || chr == '\t' || chr == '\r' || chr == '\n')  {
      if idx == 0 {
        return Error(Position(ErrorKind::MultiSpace, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(&input[input_length..], input)
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

pub fn length_value(input:&[u8]) -> IResult<&[u8], &[u8]> {
  let input_len = input.len();
  if input_len == 0 {
    return Error(Position(ErrorKind::LengthValueFn, input))
  }

  let len = input[0] as usize;
  if input_len - 1 >= len {
    IResult::Done(&input[len+1..], &input[1..len+1])
  } else {
    IResult::Incomplete(Needed::Size(1+len))
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

/// if parameter is true, parse a big endian u16 integer,
/// otherwise a little endian u16 integer
#[macro_export]
macro_rules! u16 ( ($i:expr, $e:expr) => ( {if $e { $crate::be_u16($i) } else { $crate::le_u16($i) } } ););
/// if parameter is true, parse a big endian u32 integer,
/// otherwise a little endian u32 integer
#[macro_export]
macro_rules! u32 ( ($i:expr, $e:expr) => ( {if $e { $crate::be_u32($i) } else { $crate::le_u32($i) } } ););
/// if parameter is true, parse a big endian u64 integer,
/// otherwise a little endian u64 integer
#[macro_export]
macro_rules! u64 ( ($i:expr, $e:expr) => ( {if $e { $crate::be_u64($i) } else { $crate::le_u64($i) } } ););

/// if parameter is true, parse a big endian i16 integer,
/// otherwise a little endian i16 integer
#[macro_export]
macro_rules! i16 ( ($i:expr, $e:expr) => ( {if $e { $crate::be_i16($i) } else { $crate::le_i16($i) } } ););
/// if parameter is true, parse a big endian i32 integer,
/// otherwise a little endian i32 integer
#[macro_export]
macro_rules! i32 ( ($i:expr, $e:expr) => ( {if $e { $crate::be_i32($i) } else { $crate::le_i32($i) } } ););
/// if parameter is true, parse a big endian i64 integer,
/// otherwise a little endian i64 integer
#[macro_export]
macro_rules! i64 ( ($i:expr, $e:expr) => ( {if $e { $crate::be_i64($i) } else { $crate::le_i64($i) } } ););

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
  match is_a!(input, &b"0123456789abcdef"[..]) {
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

/// Recognizes empty input buffers
///
/// useful to verify that the previous parsers used all of the input
#[inline]
//pub fn eof(input:&[u8]) -> IResult<&[u8], &[u8]> {
pub fn eof<'a, T:?Sized>(input: &'a T) -> IResult<&'a T,&'a T> where
    T:Index<Range<usize>, Output=T>+Index<RangeFrom<usize>, Output=T>,
    &'a T: InputLength {
  if input.input_len() == 0 {
      Done(input, input)
  } else {
      Error(Position(ErrorKind::Eof, input))
  }
}

/// Recognizes non empty buffers
#[inline]
pub fn non_empty<'a, T:?Sized>(input: &'a T) -> IResult<&'a T,&'a T> where
    T:Index<Range<usize>, Output=T>+Index<RangeFrom<usize>, Output=T>,
    &'a T: InputLength {
  if input.input_len() == 0 {
    Error(Position(ErrorKind::NonEmpty, input))
  } else {
    Done(&input[input.input_len()..], input)
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

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Needed,IResult};
  use internal::IResult::*;
  use internal::Err::*;
  use util::ErrorKind;

  #[test]
  fn tag_closure() {
    let x = tag_cl(&b"abcd"[..]);
    let r = x(&b"abcdabcdefgh"[..]);
    assert_eq!(r, Done(&b"abcdefgh"[..], &b"abcd"[..]));

    let r2 = x(&b"abcefgh"[..]);
    assert_eq!(r2, Error(Position(ErrorKind::TagClosure, &b"abcefgh"[..])));
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
    assert_eq!(alpha(b), Error(Position(ErrorKind::Alpha,b)));
    assert_eq!(alpha(c), Done(&c[1..], &b"a"[..]));
    assert_eq!(alpha(d), Done("é12".as_bytes(), &b"az"[..]));
    assert_eq!(digit(a), Error(Position(ErrorKind::Digit,a)));
    assert_eq!(digit(b), Done(empty, b));
    assert_eq!(digit(c), Error(Position(ErrorKind::Digit,c)));
    assert_eq!(digit(d), Error(Position(ErrorKind::Digit,d)));
    assert_eq!(hex_digit(a), Done(empty, a));
    assert_eq!(hex_digit(b), Done(empty, b));
    assert_eq!(hex_digit(c), Done(empty, c));
    assert_eq!(hex_digit(d), Done("zé12".as_bytes(), &b"a"[..]));
    assert_eq!(hex_digit(e), Error(Position(ErrorKind::HexDigit,e)));
    assert_eq!(oct_digit(a), Error(Position(ErrorKind::OctDigit,a)));
    assert_eq!(oct_digit(b), Done(empty, b));
    assert_eq!(oct_digit(c), Error(Position(ErrorKind::OctDigit,c)));
    assert_eq!(oct_digit(d), Error(Position(ErrorKind::OctDigit,d)));
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
    assert_eq!(alpha(b), Error(Position(ErrorKind::Alpha,b)));
    assert_eq!(alpha(c), Done(&c[1..], &"a"[..]));
    assert_eq!(alpha(d), Done("12", &"azé"[..]));
    assert_eq!(digit(a), Error(Position(ErrorKind::Digit,a)));
    assert_eq!(digit(b), Done(empty, b));
    assert_eq!(digit(c), Error(Position(ErrorKind::Digit,c)));
    assert_eq!(digit(d), Error(Position(ErrorKind::Digit,d)));
    assert_eq!(hex_digit(a), Done(empty, a));
    assert_eq!(hex_digit(b), Done(empty, b));
    assert_eq!(hex_digit(c), Done(empty, c));
    assert_eq!(hex_digit(d), Done("zé12", &"a"[..]));
    assert_eq!(hex_digit(e), Error(Position(ErrorKind::HexDigit,e)));
    assert_eq!(oct_digit(a), Error(Position(ErrorKind::OctDigit,a)));
    assert_eq!(oct_digit(b), Done(empty, b));
    assert_eq!(oct_digit(c), Error(Position(ErrorKind::OctDigit,c)));
    assert_eq!(oct_digit(d), Error(Position(ErrorKind::OctDigit,d)));
    assert_eq!(alphanumeric(a), Done(empty, a));
    assert_eq!(fix_error!(b,(), alphanumeric), Done(empty, b));
    assert_eq!(alphanumeric(c), Done(empty, c));
    assert_eq!(alphanumeric(d), Done("", &"azé12"[..]));
    assert_eq!(space(e), Done(&""[..], &" "[..]));
  }

  use util::HexDisplay;
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
  fn is_not() {
    let a: &[u8] = b"ab12cd\nefgh";
    assert_eq!(not_line_ending(a), Done(&b"\nefgh"[..], &b"ab12cd"[..]));

    let b: &[u8] = b"ab12cd\nefgh\nijkl";
    assert_eq!(not_line_ending(b), Done(&b"\nefgh\nijkl"[..], &b"ab12cd"[..]));

    let c: &[u8] = b"ab12cd";
    assert_eq!(not_line_ending(c), Done(&b""[..], c));
  }

  #[test]
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
  fn length_value_test() {
    let i1 = vec![7,8];
    let o1 = vec![4, 5, 6];
    let arr1:[u8; 6usize] = [3, 4, 5, 6, 7, 8];
    let res1 = length_value(&arr1);
    assert_eq!(Done(&i1[..], &o1[..]), res1);

    let i2:Vec<u8> = vec![4,5,6,7,8];
    let o2: &[u8] = b"";
    let arr2:[u8; 6usize] = [0, 4, 5, 6, 7, 8];
    let res2 = length_value(&arr2);
    assert_eq!(Done(&i2[..], o2), res2);

    let arr3:[u8; 7usize] = [8, 4, 5, 6, 7, 8, 9];
    let res3 = length_value(&arr3);
    //FIXME: should be incomplete
    assert_eq!(Incomplete(Needed::Size(9)), res3);
  }

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
    assert_eq!(hex_u32(&b"00c5a31be2"[..]), Done(&b"e2"[..], 12952347));
    assert_eq!(hex_u32(&b"c5a31be201"[..]), Done(&b"01"[..], 3315801058));
    assert_eq!(hex_u32(&b"ffffffff"[..]), Done(&b""[..], 4294967295));
    assert_eq!(hex_u32(&b"0x1be2"[..]), Done(&b"x1be2"[..], 0));
  }

    #[test]
    fn end_of_input() {
        let not_over = &b"Hello, world!"[..];
        let is_over = &b""[..];

        let res_not_over = eof(not_over);
        assert_eq!(res_not_over, Error(Position(ErrorKind::Eof, not_over)));

        let res_over = eof(is_over);
        assert_eq!(res_over, Done(is_over, is_over));
    }

  #[test]
  fn configurable_endianness() {
    named!(be_tst16<u16>, u16!(true));
    named!(le_tst16<u16>, u16!(false));
    assert_eq!(be_tst16(&[0x80, 0x00]), Done(&b""[..], 32768_u16));
    assert_eq!(le_tst16(&[0x80, 0x00]), Done(&b""[..], 128_u16));

    named!(be_tst32<u32>, u32!(true));
    named!(le_tst32<u32>, u32!(false));
    assert_eq!(be_tst32(&[0x12, 0x00, 0x60, 0x00]), Done(&b""[..], 302014464_u32));
    assert_eq!(le_tst32(&[0x12, 0x00, 0x60, 0x00]), Done(&b""[..], 6291474_u32));

    named!(be_tst64<u64>, u64!(true));
    named!(le_tst64<u64>, u64!(false));
    assert_eq!(be_tst64(&[0x12, 0x00, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]), Done(&b""[..], 1297142246100992000_u64));
    assert_eq!(le_tst64(&[0x12, 0x00, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]), Done(&b""[..], 36028874334666770_u64));

    named!(be_tsti16<i16>, i16!(true));
    named!(le_tsti16<i16>, i16!(false));
    assert_eq!(be_tsti16(&[0x00, 0x80]), Done(&b""[..], 128_i16));
    assert_eq!(le_tsti16(&[0x00, 0x80]), Done(&b""[..], -32768_i16));

    named!(be_tsti32<i32>, i32!(true));
    named!(le_tsti32<i32>, i32!(false));
    assert_eq!(be_tsti32(&[0x00, 0x12, 0x60, 0x00]), Done(&b""[..], 1204224_i32));
    assert_eq!(le_tsti32(&[0x00, 0x12, 0x60, 0x00]), Done(&b""[..], 6296064_i32));

    named!(be_tsti64<i64>, i64!(true));
    named!(le_tsti64<i64>, i64!(false));
    assert_eq!(be_tsti64(&[0x00, 0xFF, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]), Done(&b""[..], 71881672479506432_i64));
    assert_eq!(le_tsti64(&[0x00, 0xFF, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]), Done(&b""[..], 36028874334732032_i64));

  }

  #[test]
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
    assert_eq!(hex_digit(i), Error(Position(ErrorKind::HexDigit,i)));

    let i = &b"G"[..];
    assert_eq!(hex_digit(i), Error(Position(ErrorKind::HexDigit,i)));

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
    assert_eq!(oct_digit(i), Error(Position(ErrorKind::OctDigit,i)));

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
}
