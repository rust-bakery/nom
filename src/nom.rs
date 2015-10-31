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
use util::ErrorKind;
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
  Done(b"", input)
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
//pub filter!(alphanumeric is_alphanumeric)

/// Recognizes lowercase and uppercase alphabetic characters: a-zA-Z
pub fn alpha(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for (idx, item) in input.iter().enumerate() {
    if !is_alphabetic(*item) {
      if idx == 0 {
        return Error(Position(ErrorKind::Alpha, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

/// Recognizes numerical characters: 0-9
pub fn digit(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for (idx, item) in input.iter().enumerate() {
    if !is_digit(*item) {
      if idx == 0 {
        return Error(Position(ErrorKind::Digit, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

/// Recognizes numerical and alphabetic characters: 0-9a-zA-Z
pub fn alphanumeric(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for (idx, item) in input.iter().enumerate() {
    if !is_alphanumeric(*item) {
      if idx == 0 {
        return Error(Position(ErrorKind::AlphaNumeric, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

/// Recognizes spaces and tabs
pub fn space(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for (idx, item) in input.iter().enumerate() {
    if !is_space(*item) {
      if idx == 0 {
        return Error(Position(ErrorKind::Space, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

/// Recognizes spaces, tabs, carriage returns and line feeds
pub fn multispace(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for (idx, item) in input.iter().enumerate() {
    // println!("multispace at index: {}", idx);
    if !is_space(*item) && *item != '\r' as u8 && *item != '\n' as u8 {
      if idx == 0 {
        return Error(Position(ErrorKind::MultiSpace, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
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

/// Recognizes empty input buffers
///
/// useful to verify that the previous parsers used all of the input
#[inline]
pub fn eof(input:&[u8]) -> IResult<&[u8], &[u8]> {
    if input.is_empty() {
        Done(input, input)
    } else {
        Error(Position(ErrorKind::Eof, input))
    }
}

/// Return the remaining input.
#[inline]
pub fn rest(i: &[u8]) -> IResult<&[u8], &[u8]> {
	IResult::Done(b"", i)
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
    assert_eq!(alphanumeric(a), Done(empty, a));
    assert_eq!(fix_error!(b,(), alphanumeric), Done(empty, b));
    assert_eq!(alphanumeric(c), Done(empty, c));
    assert_eq!(alphanumeric(d), Done("é12".as_bytes(), &b"az"[..]));
    assert_eq!(space(e), Done(&b""[..], &b" "[..]));
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

  fn custom_error(input: &[u8]) -> IResult<&[u8], &[u8], ()> {
    fix_error!(input, (), alphanumeric)
  }
}
