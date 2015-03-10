//! Useful parser combinators
//!
//! A number of useful parser combinators have already been implemented.
//! Some of them use macros, other are implemented through functions.
//! Hopefully, the syntax will converge to onely one way in the future,
//! but the macros system makes no promises.
//!

extern crate collections;

use std::fmt::Debug;
use internal::*;
use internal::IResult::*;
use std::mem::transmute;

pub fn tag_cl<'a,'b>(rec:&'a[u8]) ->  Box<Fn(&'b[u8]) -> IResult<&'b[u8], &'b[u8]> + 'a> {
  Box::new(move |i: &'b[u8]| -> IResult<&'b[u8], &'b[u8]> {
    if i.len() >= rec.len() && &i[0..rec.len()] == rec {
      Done(&i[rec.len()..], &i[0..rec.len()])
    } else {
      Error(0)
    }
  })
}

pub fn print<T: Debug>(input: T) -> IResult<T, ()> {
  println!("{:?}", input);
  Done(input, ())
}

pub fn begin<'a>(input: &'a [u8]) -> IResult<(), &'a [u8]> {
  Done((), input)
}

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
// public methods
//pub is_not!(line_ending b"\r\n")
pub fn not_line_ending(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    for &i in b"\r\n".iter() {
      if input[idx] == i {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done(b"", input)
}

tag!(tag_ln "\n");

pub fn line_ending(input:&[u8]) -> IResult<&[u8], &[u8]> {
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
pub fn alpha(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_alphabetic(input[idx]) {
      return Done(&input[idx..], &input[0..idx])
    }
  }
  Done(b"", input)
}

pub fn digit(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_digit(input[idx]) {
      return Done(&input[idx..], &input[0..idx])
    }
  }
  Done(b"", input)
}

pub fn alphanumeric(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_alphanumeric(input[idx]) {
      return Done(&input[idx..], &input[0..idx])
    }
  }
  Done(b"", input)
}

pub fn space(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_space(input[idx]) {
      return Done(&input[idx..], &input[0..idx])
    }
  }
  Done(b"", input)
}

pub fn multispace(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_space(input[idx]) && input[idx] != '\r' as u8 && input[idx] != '\n' as u8 {
      return Done(&input[idx..], &input[0..idx])
    }
  }
  Done(b"", input)
}

pub fn sized_buffer(input:&[u8]) -> IResult<&[u8], &[u8]> {
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

pub fn length_value(input:&[u8]) -> IResult<&[u8], &[u8]> {
  let input_len = input.len();
  if input_len == 0 {
    return IResult::Error(0)
  }

  let len = input[0] as usize;
  if input_len - 1 >= len {
    return IResult::Done(&input[len+1..], &input[1..len+1])
  } else {
    // FIXME: return Incomplete
    return IResult::Incomplete(Needed::Size(1+len as u32))
  }
}

pub fn be_u8(i: &[u8]) -> IResult<&[u8], u8> {
  if i.len() < 1 {
    Incomplete(Needed::Size(1))
  } else {
    Done(&i[1..], i[0])
  }
}

pub fn be_u16(i: &[u8]) -> IResult<&[u8], u16> {
  if i.len() < 2 {
    Incomplete(Needed::Size(2))
  } else {
    let res = ((i[0] as u16) << 8) + i[1] as u16;
    Done(&i[2..], res)
  }
}

pub fn be_u32(i: &[u8]) -> IResult<&[u8], u32> {
  if i.len() < 4 {
    Incomplete(Needed::Size(4))
  } else {
    let res = ((i[0] as u32) << 24) + ((i[1] as u32) << 16) + ((i[2] as u32) << 8) + i[3] as u32;
    Done(&i[4..], res)
  }
}

pub fn be_u64(i: &[u8]) -> IResult<&[u8], u64> {
  if i.len() < 8 {
    Incomplete(Needed::Size(8))
  } else {
    let res = ((i[0] as u64) << 56) + ((i[1] as u64) << 48) + ((i[2] as u64) << 40) + ((i[3] as u64) << 32) +
      ((i[4] as u64) << 24) + ((i[5] as u64) << 16) + ((i[6] as u64) << 8) + i[7] as u64;
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

#[cfg(test)]
mod tests {
  use super::*;
  use map::*;
  use internal::Needed;
  use internal::IResult;
  use internal::IResult::*;

  #[test]
  fn tag_closure() {
    let x = tag_cl(b"abcd");
    let r = x(b"abcdabcdefgh");
    assert_eq!(r, Done(b"abcdefgh", b"abcd"));

    let r2 = x(b"abcefgh");
    assert_eq!(r2, Error(0));
  }

  #[test]
  fn character() {
    let empty = b"";
    let a = b"abcd";
    let b = b"1234";
    let c = b"a123";
    let d = "azé12".as_bytes();
    let e = b" ";
    assert_eq!(alpha(a), Done(empty, a));
    assert_eq!(alpha(b), Done(b, empty));
    assert_eq!(alpha(c), Done(&c[1..], b"a"));
    assert_eq!(alpha(d), Done("é12".as_bytes(), b"az"));
    assert_eq!(digit(a), Done(a, empty));
    assert_eq!(digit(b), Done(empty, b));
    assert_eq!(digit(c), Done(c, empty));
    assert_eq!(digit(d), Done(d, empty));
    assert_eq!(alphanumeric(a), Done(empty, a));
    assert_eq!(alphanumeric(b), Done(empty, b));
    assert_eq!(alphanumeric(c), Done(empty, c));
    assert_eq!(alphanumeric(d), Done("é12".as_bytes(), b"az"));
    assert_eq!(space(e), Done(b"", b" "));
  }

  #[test]
  fn is_not() {
    let a = b"ab12cd\nefgh";
    assert_eq!(not_line_ending(a), Done(b"\nefgh", b"ab12cd"));

    let b = b"ab12cd\nefgh\nijkl";
    assert_eq!(not_line_ending(b), Done(b"\nefgh\nijkl", b"ab12cd"));

    let c = b"ab12cd";
    assert_eq!(not_line_ending(c), Done(b"", b"ab12cd"));
  }

  #[test]
  fn buffer_with_size() {
    let i:Vec<u8> = vec![7,8];
    let o:Vec<u8> = vec![4,5,6];
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
    let o2 = b"";
    let arr2:[u8; 6usize] = [0, 4, 5, 6, 7, 8];
    let res2 = length_value(&arr2);
    assert_eq!(Done(&i2[..], o2), res2);

    let arr3:[u8; 7usize] = [8, 4, 5, 6, 7, 8, 9];
    let res3 = length_value(&arr3);
    //FIXME: should be incomplete
    assert_eq!(Incomplete(Needed::Size(9)), res3);
  }

}
