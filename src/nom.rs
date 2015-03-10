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
  fn is_a() {
    is_a!(a_or_b   b"ab");

    let a = b"abcd";
    assert_eq!(a_or_b(a), Done(b"cd", b"ab"));

    let b = b"bcde";
    assert_eq!(a_or_b(b), Done(b"cde", b"b"));

    let c = b"cdef";
    assert_eq!(a_or_b(c), Done(b"cdef", b""));

    let d = b"bacdef";
    assert_eq!(a_or_b(d), Done(b"cdef", b"ba"));
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

  #[derive(PartialEq,Eq,Debug)]
  struct B {
    a: u8,
    b: u8
  }

  #[test]
  fn chain_and_ignore() {
    tag!(x "abcd");
    tag!(y "efgh");
    fn ret_int(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    //o!(z<&[u8], int>  x S x S retInt Z y);
    o!(z<&[u8], u8>  x ~ x ~ [ ret_int ] ~ y);

    let r = z(b"abcdabcdefgh");
    assert_eq!(r, Done(b"", 1));
  }


  #[test]
  fn chain() {
    tag!(x "abcd");
    fn temp_ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    o!(ret_int1<&[u8],u8> x ~ [ temp_ret_int1 ]);
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };
    chain!(f<&[u8],B>,
      aa: ret_int1 ~
      bb: ret_int2 ,
      ||{B{a: aa, b: bb}}
    );

    let r = f(b"abcde");
    assert_eq!(r, Done(b"e", B{a: 1, b: 2}));
  }

  #[test]
  fn chain2() {
    tag!(x "abcd");
    tag!(y "efgh");
    //fn temp_ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    //o!(ret_int1<&[u8],u8> x ~ [ temp_ret_int1 ]);
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };
    chain!(f<&[u8],B>,
      x            ~
      x?           ~
      aa: ret_int1 ~
      y            ~
      bb: ret_int2 ~
      y            ,
      ||{B{a: aa, b: bb}});

    let r = f(b"abcdabcdefghefghX");
    assert_eq!(r, Done(b"X", B{a: 1, b: 2}));

    let r2 = f(b"abcdefghefghX");
    assert_eq!(r2, Done(b"X", B{a: 1, b: 2}));
  }

  #[derive(PartialEq,Eq,Debug)]
  struct C {
    a: u8,
    b: Option<u8>
  }


  #[test]
  fn chain_opt() {
    tag!(x "abcd");
    tag!(y "efgh");
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_y(i:&[u8]) -> IResult<&[u8], u8> {
      y(i).map(|_| 2)
    };

    chain!(f<&[u8],C>,
      x            ~
      aa: ret_int1 ~
      bb: ret_y?   ,
      ||{C{a: aa, b: bb}});

    let r = f(b"abcdefghX");
    assert_eq!(r, Done(b"X", C{a: 1, b: Some(2)}));

    let r2 = f(b"abcdWXYZ");
    assert_eq!(r2, Done(b"WXYZ", C{a: 1, b: None}));

    let r3 = f(b"abcdX");
    assert_eq!(r3, Incomplete(Needed::Size(4)));
  }

  #[test]
  fn alt() {
    fn work(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Done(b"", input)
    }

    #[allow(unused_variables)]
    fn dont_work(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Error(3)
    }

    fn work2(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Done(input, b"")
    }

    alt!(alt1<&[u8],&[u8]>, dont_work | dont_work);
    alt!(alt2<&[u8],&[u8]>, dont_work | work);
    alt!(alt3<&[u8],&[u8]>, dont_work | dont_work | work2 | dont_work);

    let a = b"abcd";
    assert_eq!(alt1(a), Error(1));
    assert_eq!(alt2(a), Done(b"", a));
    assert_eq!(alt3(a), Done(a, b""));
  }

  #[test]
  fn opt() {
    tag!(x "abcd");
    opt!(o<&[u8],&[u8]> x);

    let a = b"abcdef";
    let b = b"bcdefg";
    assert_eq!(o(a), Done(b"ef", Some(b"abcd")));
    assert_eq!(o(b), Done(b"bcdefg", None));
  }

  #[test]
  fn many0() {
    tag!(x "abcd");
    many0!(multi<&[u8],&[u8]> x);

    let a = b"abcdef";
    let b = b"abcdabcdef";
    let c = b"azerty";

    let res1 = vec![b"abcd"];
    assert_eq!(multi(a), Done(b"ef", res1));
    let res2 = vec![b"abcd", b"abcd"];
    assert_eq!(multi(b), Done(b"ef", res2));
    assert_eq!(multi(c), Done(b"azerty", Vec::new()));
  }

  #[test]
  fn many1() {
    tag!(x "abcd");
    many1!(multi<&[u8],&[u8]> x);

    let a = b"abcdef";
    let b = b"abcdabcdef";
    let c = b"azerty";
    let res1 = vec![b"abcd"];
    assert_eq!(multi(a), Done(b"ef", res1));
    let res2 = vec![b"abcd", b"abcd"];
    assert_eq!(multi(b), Done(b"ef", res2));
    assert_eq!(multi(c), Error(0));
  }

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

  #[test]
  fn take_until_test() {
    take_until!(x "efgh");
    let r = x(b"abcdabcdefghijkl");
    assert_eq!(r, Done(b"ijkl", b"abcdabcd"));

    println!("Done 1\n");

    let r2 = x(b"abcdabcdefgh");
    assert_eq!(r2, Done(b"", b"abcdabcd"));

    println!("Done 2\n");
    let r3 = x(b"abcefg");
    assert_eq!(r3, Incomplete(Needed::Size(7)));
  }
}
