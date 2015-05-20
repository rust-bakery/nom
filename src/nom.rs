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
use util::ErrorCode;
use std::mem::transmute;

pub fn tag_cl<'a,'b>(rec:&'a[u8]) ->  Box<Fn(&'b[u8]) -> IResult<'b, &'b[u8], &'b[u8]> + 'a> {
  Box::new(move |i: &'b[u8]| -> IResult<'b, &'b[u8], &'b[u8]> {
    if i.len() >= rec.len() && &i[0..rec.len()] == rec {
      Done(&i[rec.len()..], &i[0..rec.len()])
    } else {
      Error(Position(ErrorCode::TagClosure as u32, i))
    }
  })
}

#[cfg(not(feature = "core"))]
pub fn print<'a,T: Debug>(input: T) -> IResult<'a,T, ()> {
  println!("{:?}", input);
  Done(input, ())
}

pub fn begin<'a>(input: &'a [u8]) -> IResult<'a,(), &'a [u8]> {
  Done((), input)
}

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
// public methods
//pub is_not!(line_ending b"\r\n")
pub fn not_line_ending<'a>(input:&[u8]) -> IResult<'a, &[u8], &[u8]> {
  for idx in 0..input.len() {
    for &i in b"\r\n".iter() {
      if input[idx] == i {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

named!(tag_ln, tag!("\n"));

pub fn line_ending<'a>(input:&'a[u8]) -> IResult<'a, &[u8], &[u8]> {
  tag_ln(input)
}

pub fn is_alphabetic(chr:u8) -> bool {
  (chr >= 0x41 && chr <= 0x5A) || (chr >= 0x61 && chr <= 0x7A)
}

pub fn is_digit(chr: u8) -> bool {
  chr >= 0x30 && chr <= 0x39
}

pub fn is_alphanumeric(chr: u8) -> bool {
  is_alphabetic(chr) || is_digit(chr)
}

pub fn is_space(chr:u8) -> bool {
  chr == ' ' as u8 || chr == '\t' as u8
}

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
//pub filter!(alpha is_alphabetic)
//pub filter!(digit is_digit)
//pub filter!(alphanumeric is_alphanumeric)
pub fn alpha<'a>(input:&'a [u8]) -> IResult<'a,&'a [u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_alphabetic(input[idx]) {
      if idx == 0 {
        return Error(Position(ErrorCode::Alpha as u32, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

pub fn digit<'a>(input:&'a [u8]) -> IResult<'a,&'a [u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_digit(input[idx]) {
      if idx == 0 {
        return Error(Position(ErrorCode::Digit as u32, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

pub fn alphanumeric<'a>(input:&'a [u8]) -> IResult<'a,&'a [u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_alphanumeric(input[idx]) {
      if idx == 0 {
        return Error(Position(ErrorCode::AlphaNumeric as u32, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

pub fn space<'a>(input:&'a [u8]) -> IResult<'a,&'a [u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_space(input[idx]) {
      if idx == 0 {
        return Error(Position(ErrorCode::Space as u32, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

pub fn multispace<'a>(input:&'a [u8]) -> IResult<'a,&'a [u8], &[u8]> {
  for idx in 0..input.len() {
    // println!("multispace at index: {}", idx);
    if !is_space(input[idx]) && input[idx] != '\r' as u8 && input[idx] != '\n' as u8 {
      if idx == 0 {
        return Error(Position(ErrorCode::MultiSpace as u32, input))
      } else {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

pub fn sized_buffer<'a>(input:&'a [u8]) -> IResult<'a,&'a [u8], &[u8]> {
  if input.len() == 0 {
    return Incomplete(Needed::Unknown)
  }

  let len = input[0] as usize;

  if input.len() >= len + 1 {
    return Done(&input[len+1..], &input[1..len+1])
  } else {
    return Incomplete(Needed::Size(1 + len as u32))
  }
}

pub fn length_value<'a>(input:&'a [u8]) -> IResult<'a,&'a [u8], &[u8]> {
  let input_len = input.len();
  if input_len == 0 {
    return Error(Position(ErrorCode::LengthValueFn as u32, input))
  }

  let len = input[0] as usize;
  if input_len - 1 >= len {
    return IResult::Done(&input[len+1..], &input[1..len+1])
  } else {
    // FIXME: return Incomplete
    return IResult::Incomplete(Needed::Size(1+len as u32))
  }
}

pub fn be_u8<'a>(i: &[u8]) -> IResult<'a,&[u8], u8> {
  if i.len() < 1 {
    Incomplete(Needed::Size(1))
  } else {
    Done(&i[1..], i[0])
  }
}

pub fn be_u16<'a>(i: &[u8]) -> IResult<'a,&[u8], u16> {
  if i.len() < 2 {
    Incomplete(Needed::Size(2))
  } else {
    let res = ((i[0] as u16) << 8) + i[1] as u16;
    Done(&i[2..], res)
  }
}

pub fn be_u32<'a>(i: &[u8]) -> IResult<'a,&[u8], u32> {
  if i.len() < 4 {
    Incomplete(Needed::Size(4))
  } else {
    let res = ((i[0] as u32) << 24) + ((i[1] as u32) << 16) + ((i[2] as u32) << 8) + i[3] as u32;
    Done(&i[4..], res)
  }
}

pub fn be_u64<'a>(i: &[u8]) -> IResult<'a,&[u8], u64> {
  if i.len() < 8 {
    Incomplete(Needed::Size(8))
  } else {
    let res = ((i[0] as u64) << 56) + ((i[1] as u64) << 48) + ((i[2] as u64) << 40) + ((i[3] as u64) << 32) +
      ((i[4] as u64) << 24) + ((i[5] as u64) << 16) + ((i[6] as u64) << 8) + i[7] as u64;
    Done(&i[8..], res)
  }
}

pub fn be_i8<'a>(i:&'a [u8]) -> IResult<&'a [u8], i8> {
  map!(i, be_u8, | x | { x as i8 })
}

pub fn be_i16<'a>(i:&'a [u8]) -> IResult<&'a [u8], i16> {
  map!(i, be_u16, | x | { x as i16 })
}

pub fn be_i32<'a>(i:&'a [u8]) -> IResult<&'a [u8], i32> {
  map!(i, be_u32, | x | { x as i32 })
}

pub fn be_i64<'a>(i:&'a [u8]) -> IResult<&'a [u8], i64> {
  map!(i, be_u64, | x | { x as i64 })
}

pub fn le_u8(i: &[u8]) -> IResult<&[u8], u8> {
  if i.len() < 1 {
    Incomplete(Needed::Size(1))
  } else {
    Done(&i[1..], i[0])
  }
}

pub fn le_u16(i: &[u8]) -> IResult<&[u8], u16> {
  if i.len() < 2 {
    Incomplete(Needed::Size(2))
  } else {
    let res = ((i[1] as u16) << 8) + i[0] as u16;
    Done(&i[2..], res)
  }
}

pub fn le_u32(i: &[u8]) -> IResult<&[u8], u32> {
  if i.len() < 4 {
    Incomplete(Needed::Size(4))
  } else {
    let res = ((i[3] as u32) << 24) + ((i[2] as u32) << 16) + ((i[1] as u32) << 8) + i[0] as u32;
    Done(&i[4..], res)
  }
}

pub fn le_u64(i: &[u8]) -> IResult<&[u8], u64> {
  if i.len() < 8 {
    Incomplete(Needed::Size(8))
  } else {
    let res = ((i[7] as u64) << 56) + ((i[6] as u64) << 48) + ((i[5] as u64) << 40) + ((i[4] as u64) << 32) +
      ((i[3] as u64) << 24) + ((i[2] as u64) << 16) + ((i[1] as u64) << 8) + i[0] as u64;
    Done(&i[8..], res)
  }
}

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

pub fn eof(input:&[u8]) -> IResult<&[u8], &[u8]> {
    if input.len() == 0 {
        Done(input, input)
    } else {
        Error(Position(ErrorCode::Eof as u32, input))
    }
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::Needed;
  use internal::IResult::*;
  use internal::Err::*;
  use util::ErrorCode;

  #[test]
  fn tag_closure() {
    let x = tag_cl(&b"abcd"[..]);
    let r = x(&b"abcdabcdefgh"[..]);
    assert_eq!(r, Done(&b"abcdefgh"[..], &b"abcd"[..]));

    let r2 = x(&b"abcefgh"[..]);
    assert_eq!(r2, Error(Position(ErrorCode::TagClosure as u32, &b"abcefgh"[..])));
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
    assert_eq!(alpha(b), Error(Position(ErrorCode::Alpha as u32,b)));
    assert_eq!(alpha(c), Done(&c[1..], &b"a"[..]));
    assert_eq!(alpha(d), Done("é12".as_bytes(), &b"az"[..]));
    assert_eq!(digit(a), Error(Position(ErrorCode::Digit as u32,a)));
    assert_eq!(digit(b), Done(empty, b));
    assert_eq!(digit(c), Error(Position(ErrorCode::Digit as u32,c)));
    assert_eq!(digit(d), Error(Position(ErrorCode::Digit as u32,d)));
    assert_eq!(alphanumeric(a), Done(empty, a));
    assert_eq!(alphanumeric(b), Done(empty, b));
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
    fn end_of_input() {
        let not_over = &b"Hello, world!"[..];
        let is_over = &b""[..];

        let res_not_over = eof(not_over);
        assert_eq!(res_not_over, Error(Position(ErrorCode::Eof as u32, not_over)));

        let res_over = eof(is_over);
        assert_eq!(res_over, Done(is_over, is_over));
    }

}
