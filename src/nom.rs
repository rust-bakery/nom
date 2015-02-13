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

/// declares a byte array as a suite to recognize
///
/// consumes the recognized characters
///
/// ```ignore
///  tag!(x "abcd".as_bytes());
///  let r = Done((), "abcdabcdefgh".as_bytes()).flat_map(x);
///  assert_eq!(r, Done("efgh".as_bytes(), "abcd".as_bytes()));
/// ```
#[macro_export]
macro_rules! tag(
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      if i.len() >= $inp.len() && i.slice(0, $inp.len()) == $inp {
        Done(&i[$inp.len()..], &i[0..$inp.len()])
      } else {
        Error(0)
      }
    }
  )
);

pub fn tag_cl<'a,'b>(rec:&'a[u8]) ->  Box<Fn(&'b[u8]) -> IResult<&'b[u8], &'b[u8]>> {
  Box::new(move |i: &'b[u8]| -> IResult<&'b[u8], &'b[u8]> {
    if i.len() >= rec.len() && i.slice(0, rec.len()) == rec {
      Done(&i[rec.len()..], &i[0..rec.len()])
    } else {
      Error(0)
    }
  })
}

/// chains parsers and returns the result of only one of them
///
/// ```ignore
/// tag!(x "abcd".as_bytes());
/// tag!(y "efgh".as_bytes());
///
/// fn ret_int(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
///
///  // parse the x tag two times, return an int, parse the y tag
///  o!(z<&[u8], u8>  x ~ x ~ [ ret_int ] ~ y);
///
/// let r = Done((), "abcdabcdefgh".as_bytes()).flat_map(z);
/// assert_eq!(r, Done("".as_bytes(), 1));
/// ```
#[macro_export]
macro_rules! o(
  ($name:ident<$i:ty,$o:ty> $f1:ident ~ $($rest:tt)*) => (
    #[allow(unused_variables)]
    fn $name(input:$i) -> IResult<$i, $o>{
      match $f1(input) {
        IResult::Error(e)      => IResult::Error(e),
        IResult::Incomplete(i) => IResult::Error(42),//IResult::Incomplete(i),
        IResult::Done(i,o)     => {
          o_parser!(i ~ o ~ $($rest)*)
        }
      }
    }
  );
);

#[macro_export]
macro_rules! o_parser(
  ($i:ident ~ $o:ident ~ [ $e:ident ] ~ $s:ident) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Error(42),//IResult::Incomplete(i),
      IResult::Done(i,o)     => {
        match $s(i) {
          IResult::Error(e)      => IResult::Error(e),
          IResult::Incomplete(i) => IResult::Error(42),//IResult::Incomplete(i),
          IResult::Done(i2,o2)     => {
            IResult::Done(i2, o)
          }
        }
      }
    }
  );

  ($i:ident ~ $o:ident ~ [ $e:ident ] ~ $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Error(42),//IResult::Incomplete(i),
      IResult::Done(i,o)     => {
        o_parser!(i ~ o ~ $($rest)*)
      }
    }
  );

  ($i:ident ~ $o:ident ~ [ $e:ident ]) => (
    $e($i)
  );

  ($i:ident ~ $o:ident ~ $e:ident ~ $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Error(42),//IResult::Incomplete(i),
      IResult::Done(i,_)     => {
        o_parser!(i ~ $o ~ $($rest)*)
      }
    }
  );

  ($i:ident ~ $o:ident ~ $e:ident) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Error(42),//IResult::Incomplete(i),
      IResult::Done(i,_)     => {
        IResult::Done(i, $o)
      }
    }
  );

  ($i:ident ~ $o:ident) => (Done($i,$o));

);

#[macro_export]
macro_rules! chain (
  ($name:ident<$i:ty,$o:ty>, $assemble:expr, $($rest:tt)*) => (
    #[allow(unused_variables)]
    fn $name(i:$i) -> IResult<$i,$o>{
      chaining_parser!(i, $assemble, $($rest)*)
    }
  );
);

#[macro_export]
macro_rules! chaining_parser (
  ($i:expr, $assemble:expr, $field:ident : $e:expr, $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Error(42),//IResult::Incomplete(i),
      IResult::Done(i,o)     => {
        let $field = o;
        chaining_parser!(i, $assemble, $($rest)*)
      }
    }
  );

  ($i:expr, $assemble:expr, ) => (
    IResult::Done($i, $assemble())
  )
);

#[macro_export]
macro_rules! alt (
  ($name:ident<$i:ty,$o:ty>, $($rest:tt)*) => (
    fn $name(i:$i) -> IResult<$i,$o>{
      alt_parser!(i | $($rest)*)
    }
  );
);

#[macro_export]
macro_rules! alt_parser (
  ($i:ident | $e:ident | $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(_)      => alt_parser!($i | $($rest)*),
      IResult::Incomplete(_) => alt_parser!($i | $($rest)*),
      IResult::Done(i,o)     => IResult::Done(i,o)
    }
  );

  ($i:ident | $e:ident) => (
    match $e($i) {
      IResult::Error(_)      => alt_parser!($i),
      IResult::Incomplete(_) => alt_parser!($i),
      IResult::Done(i,o)     => IResult::Done(i,o)
    }
  );

  ($i:ident) => (
    IResult::Error(1)
  )
);

pub fn print<'y,T: Debug>(input: T) -> IResult<'y,T, ()> {
  println!("{:?}", input);
  Done(input, ())
}

pub fn begin<'a,'y>(input: &'a [u8]) -> IResult<'y,(), &'a [u8]> {
  Done((), input)
}

#[macro_export]
macro_rules! is_not(
  ($name:ident $arr:expr) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      for idx in range(0, input.len()) {
        for &i in $arr.iter() {
          if input[idx] == i {
            return IResult::Done(input.slice_from(idx), input.slice(0, idx))
          }
        }
      }
      IResult::Done("".as_bytes(), input)
    }
  )
);

#[macro_export]
macro_rules! is_a(
  ($name:ident $arr:expr) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      for idx in range(0, input.len()) {
        var res = false
        for &i in $arr.iter() {
          if input[idx] == i {
            res = true
          }
        }
        if !res {
          return IResult::Done(input.slice_from(idx), input.slice(0, idx))
        }
      }
      IResult::Done("".as_bytes(), input)
    }
  )
);

#[macro_export]
macro_rules! filter(
  ($name:ident $f:ident) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      for idx in 0..input.len() {
        if !$f(input[idx]) {
          return IResult::Done(&input[idx..], &input[0..idx])
        }
      }
      IResult::Done("".as_bytes(), input)
    }
  )
);

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
// public methods
//pub is_not!(line_ending "\r\n".as_bytes())
pub fn not_line_ending(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    for &i in "\r\n".as_bytes().iter() {
      if input[idx] == i {
        return Done(&input[idx..], &input[0..idx])
      }
    }
  }
  Done("".as_bytes(), input)
}

tag!(tag_ln "\n".as_bytes());

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
  Done("".as_bytes(), input)
}

pub fn digit(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_digit(input[idx]) {
      return Done(&input[idx..], &input[0..idx])
    }
  }
  Done("".as_bytes(), input)
}

pub fn alphanumeric(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_alphanumeric(input[idx]) {
      return Done(&input[idx..], &input[0..idx])
    }
  }
  Done("".as_bytes(), input)
}

pub fn space(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_space(input[idx]) {
      return Done(&input[idx..], &input[0..idx])
    }
  }
  Done("".as_bytes(), input)
}

pub fn multispace(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in 0..input.len() {
    if !is_space(input[idx]) && input[idx] != '\r' as u8 && input[idx] != '\n' as u8 {
      return Done(&input[idx..], &input[0..idx])
    }
  }
  Done("".as_bytes(), input)
}

pub fn sized_buffer(input:&[u8]) -> IResult<&[u8], &[u8]> {
  if input.len() == 0 {
    return Error(42)//Incomplete(0)
  }

  let len = input[0] as usize;

  if input.len() >= len + 1 {
    return Done(&input[len+1..], &input[1..len+1])
  } else {
    return Error(42)//Incomplete(0)
  }
}

#[macro_export]
macro_rules! opt(
  ($name:ident<$i:ty,$o:ty> $f:ident) => (
    fn $name(input:$i) -> IResult<$i, Option<$o>> {
      match $f(input) {
        IResult::Done(i,o) => IResult::Done(i, Some(o)),
        _                  => IResult::Done(input, None)
      }
    }
  )
);

// 0 or more
#[macro_export]
macro_rules! many0(
  ($name:ident<$i:ty,$o:ty> $f:ident) => (
    fn $name(input:$i) -> IResult<$i,Vec<$o>> {
      let mut begin = 0;
      let mut remaining = input.len();
      let mut res: Vec<$o> = Vec::new();
      loop {
        match $f(input.slice_from(begin)) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            return IResult::Done(input.slice_from(begin), res)
          }
        }
      }
    }
  )
);

// one or more
#[macro_export]
macro_rules! many1(
  ($name:ident<$i:ty,$o:ty> $f:ident) => (
    fn $name(input:$i) -> IResult<$i,Vec<$o>> {
      let mut begin = 0;
      let mut remaining = input.len();
      let mut res: Vec<$o> = Vec::new();
      loop {
        match $f(input.slice_from(begin)) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            if begin == 0 {
              return IResult::Error(0)
            } else {
              return IResult::Done(input.slice_from(begin), res)
            }
          }
        }
      }
    }
  )
);

#[macro_export]
macro_rules! fold0(
  ($name:ident<$i:ty,$o:ty>, $assemble:expr, $f:ident) => (
    fn $name(input:$i, z:$o) -> IResult<$i,$o> {
      fold0_impl!(<$i, $o>, $assemble, $f, input, z);
    }
  );
);

#[macro_export]
macro_rules! fold0_impl(
  (<$i:ty,$o:ty>, $assemble:expr, $f:ident, $input:ident, $z:ident) => (
    {
      let mut begin = 0;
      let mut remaining = $input.len();
      let mut res: $o = $z;
      loop {
        match $f($input.slice_from(begin)) {
          IResult::Done(i,o) => {
            //res.push(o);
            res = $assemble(res, o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= $input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            return IResult::Done($input.slice_from(begin), res)
          }
        }
      }
    }
  );
);

#[macro_export]
macro_rules! fold1(
  ($name:ident<$i:ty,$o:ty>, $assemble:expr, $f:ident) => (
    fn $name(input:$i, z:$o) -> IResult<$i,$o> {
      fold1_impl!(<$i, $o>, $assemble, $f, input, z);
    }
  );
);

#[macro_export]
macro_rules! fold1_impl(
  (<$i:ty,$o:ty>, $assemble:expr, $f:ident, $input:ident, $z:ident) => (
    {
      let mut begin = 0;
      let mut remaining = $input.len();
      let mut res: $o = $z;
      loop {
        match $f($input.slice_from(begin)) {
          IResult::Done(i,o) => {
            //res.push(o);
            res = $assemble(res, o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= $input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            if begin == 0 {
              return IResult::Error(0)
            } else {
              return IResult::Done($input.slice_from(begin), res)
            }
          }
        }
      }
    }
  );
);

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
    return IResult::Error(0)
  }
}

#[macro_export]
macro_rules! take_until(
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      for idx in 0..i.len() {
        println!("inp: {:?} i: {:?} idx: {:?}", $inp.len(), i.len(), idx);
        if idx + $inp.len() > i.len() {
          return Error(42)
        }
        println!("next 1: {:?}", i.slice(idx, idx+$inp.len()));
        if i.slice(idx, idx+$inp.len()) == $inp {
          println!("next 2");
          if idx + $inp.len() > i.len() {
            println!("next 3");
            return Done("".as_bytes(), &i[0..idx])
          } else {
            println!("next 4");
            return Done(&i[(idx+$inp.len())..], &i[0..idx])
          }
        }
        println!("next");
      }
      return Error(0)
    }
  )
);

#[macro_export]
macro_rules! take_until_and_leave(
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      for idx in 0..i.len() {
        println!("inp: {:?} i: {:?} idx: {:?}", $inp.len(), i.len(), idx);
        if idx + $inp.len() > i.len() {
          return Error(42)
        }
        println!("next 1: {:?}", i.slice(idx, idx+$inp.len()));
        if i.slice(idx, idx+$inp.len()) == $inp {
          println!("next 2");
          return Done(&i[idx..], &i[0..idx])
        }
        println!("next");
      }
      return Error(0)
    }
  )
);

#[macro_export]
macro_rules! take_until_either(
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      for idx in 0..i.len() {
        println!("inp: {:?} i: {:?} idx: {:?}", $inp.len(), i.len(), idx);
        if idx + 1 > i.len() {
          return Error(42)
        }
        println!("next 1: {:?}", i.slice(idx, idx+1));
        for &t in $inp.iter() {
          if i[idx] == t {
            println!("next 2");
            if idx + 1 > i.len() {
              println!("next 3");
              return Done("".as_bytes(), &i[0..idx])
            } else {
              println!("next 4");
              return Done(&i[(idx+1)..], &i[0..idx])
            }
          }
        }
        println!("next");
      }
      return Error(0)
    }
  )
);

#[macro_export]
macro_rules! take_until_either_and_leave(
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      for idx in 0..i.len() {
        println!("inp: {:?} i: {:?} idx: {:?}", $inp.len(), i.len(), idx);
        if idx + 1 > i.len() {
          return Error(42)
        }
        println!("next 1: {:?}", i.slice(idx, idx+1));
        for &t in $inp.iter() {
          println!("testing el = {:?} and t = {:?}", i[idx], t);
          if i[idx] == t {
            println!("next 2");
            return Done(&i[idx..], &i[0..idx])
          }
        }
        println!("next");
      }
      return Error(0)
    }
  )
);

#[cfg(test)]
mod tests {
  use super::*;
  use map::*;
  use internal::IResult;
  use internal::IResult::*;

  #[test]
  fn tag_closure() {
    let x = tag_cl("abcd".as_bytes());
    let r = x("abcdabcdefgh".as_bytes());
    assert_eq!(r, Done("abcdefgh".as_bytes(), "abcd".as_bytes()));

    let r2 = x("abcefgh".as_bytes());
    assert_eq!(r2, Error(0));
  }

  #[test]
  fn character() {
    let empty = "".as_bytes();
    let a = "abcd".as_bytes();
    let b = "1234".as_bytes();
    let c = "a123".as_bytes();
    let d = "azé12".as_bytes();
    let e = " ".as_bytes();
    assert_eq!(alpha(a), Done(empty, a));
    assert_eq!(alpha(b), Done(b, empty));
    assert_eq!(alpha(c), Done(&c[1..], "a".as_bytes()));
    assert_eq!(alpha(d), Done("é12".as_bytes(), "az".as_bytes()));
    assert_eq!(digit(a), Done(a, empty));
    assert_eq!(digit(b), Done(empty, b));
    assert_eq!(digit(c), Done(c, empty));
    assert_eq!(digit(d), Done(d, empty));
    assert_eq!(alphanumeric(a), Done(empty, a));
    assert_eq!(alphanumeric(b), Done(empty, b));
    assert_eq!(alphanumeric(c), Done(empty, c));
    assert_eq!(alphanumeric(d), Done("é12".as_bytes(), "az".as_bytes()));
    assert_eq!(space(e), Done("".as_bytes(), " ".as_bytes()));
  }

  #[test]
  fn is_not() {
    let a = "ab12cd\nefgh".as_bytes();
    assert_eq!(not_line_ending(a), Done("\nefgh".as_bytes(), "ab12cd".as_bytes()));

    let b = "ab12cd\nefgh\nijkl".as_bytes();
    assert_eq!(not_line_ending(b), Done("\nefgh\nijkl".as_bytes(), "ab12cd".as_bytes()));
  }

  #[test]
  fn buffer_with_size() {
    let i:Vec<u8> = vec![7,8];
    let o:Vec<u8> = vec![4,5,6];
    let arr:[u8; 6us] = [3, 4, 5, 6, 7, 8];
    let res = sized_buffer(&arr[]);
    assert_eq!(res, Done(&i[], &o[]))
  }

  /*#[test]
  fn t1() {
    let v1:Vec<u8> = vec![1,2,3];
    let v2:Vec<u8> = vec![4,5,6];
    let d = Done(&v1[], &v2[]);
    let res = d.flat_map(print);
    assert_eq!(res, Done(&v2[], ()));
  }*/

  #[derive(PartialEq,Eq,Debug)]
  struct B {
    a: u8,
    b: u8
  }

  #[test]
  fn chain_and_ignore() {
    tag!(x "abcd".as_bytes());
    tag!(y "efgh".as_bytes());
    fn ret_int(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    //o!(z<&[u8], int>  x S x S retInt Z y);
    o!(z<&[u8], u8>  x ~ x ~ [ ret_int ] ~ y);

    let r = z("abcdabcdefgh".as_bytes());
    assert_eq!(r, Done("".as_bytes(), 1));
  }


  #[test]
  fn chain() {
    tag!(x "abcd".as_bytes());
    fn temp_ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    o!(ret_int1<&[u8],u8> x ~ [ temp_ret_int1 ]);
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };
    chain!(f<&[u8],B>, ||{B{a: aa, b: bb}}, aa: ret_int1, bb: ret_int2,);

    let r = f("abcde".as_bytes());
    assert_eq!(r, Done("e".as_bytes(), B{a: 1, b: 2}));
  }

  #[test]
  fn alt() {
    fn work(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Done("".as_bytes(), input)
    }

    #[allow(unused_variables)]
    fn dont_work(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Error(3)
    }

    fn work2(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Done(input, "".as_bytes())
    }

    alt!(alt1<&[u8],&[u8]>, dont_work | dont_work);
    alt!(alt2<&[u8],&[u8]>, dont_work | work);
    alt!(alt3<&[u8],&[u8]>, dont_work | dont_work | work2 | dont_work);

    let a = "abcd".as_bytes();
    assert_eq!(alt1(a), Error(1));
    assert_eq!(alt2(a), Done("".as_bytes(), a));
    assert_eq!(alt3(a), Done(a, "".as_bytes()));
  }

  #[test]
  fn opt() {
    tag!(x "abcd".as_bytes());
    opt!(o<&[u8],&[u8]> x);

    let a = "abcdef".as_bytes();
    let b = "bcdefg".as_bytes();
    assert_eq!(o(a), Done("ef".as_bytes(), Some("abcd".as_bytes())));
    assert_eq!(o(b), Done("bcdefg".as_bytes(), None));
  }

  #[test]
  fn many0() {
    tag!(x "abcd".as_bytes());
    many0!(multi<&[u8],&[u8]> x);

    let a = "abcdef".as_bytes();
    let b = "abcdabcdef".as_bytes();
    let c = "azerty".as_bytes();

    let res1 = vec!["abcd".as_bytes()];
    assert_eq!(multi(a), Done("ef".as_bytes(), res1));
    let res2 = vec!["abcd".as_bytes(), "abcd".as_bytes()];
    assert_eq!(multi(b), Done("ef".as_bytes(), res2));
    assert_eq!(multi(c), Done("azerty".as_bytes(), Vec::new()));
  }

  #[test]
  fn many1() {
    tag!(x "abcd".as_bytes());
    many1!(multi<&[u8],&[u8]> x);

    let a = "abcdef".as_bytes();
    let b = "abcdabcdef".as_bytes();
    let c = "azerty".as_bytes();
    let res1 = vec!["abcd".as_bytes()];
    assert_eq!(multi(a), Done("ef".as_bytes(), res1));
    let res2 = vec!["abcd".as_bytes(), "abcd".as_bytes()];
    assert_eq!(multi(b), Done("ef".as_bytes(), res2));
    assert_eq!(multi(c), Error(0));
  }

  #[test]
  fn length_value_test() {
    let i1 = vec![7,8];
    let o1 = vec![4, 5, 6];
    let arr1:[u8; 6us] = [3, 4, 5, 6, 7, 8];
    let res1 = length_value(&arr1);
    assert_eq!(Done(&i1[], &o1[]), res1);

    let i2:Vec<u8> = vec![4,5,6,7,8];
    let o2 = "";
    let arr2:[u8; 6us] = [0, 4, 5, 6, 7, 8];
    let res2 = length_value(&arr2);
    assert_eq!(Done(&i2[], o2.as_bytes()), res2);

    let arr3:[u8; 7us] = [8, 4, 5, 6, 7, 8, 9];
    let res3 = length_value(&arr3);
    //FIXME: should be incomplete
    assert_eq!(Error(0), res3);
  }

  #[test]
  fn take_until_test() {
    take_until!(x "efgh".as_bytes());
    let r = x("abcdabcdefghijkl".as_bytes());
    assert_eq!(r, Done("ijkl".as_bytes(), "abcdabcd".as_bytes()));

    println!("Done 1\n");

    let r2 = x("abcdabcdefgh".as_bytes());
    assert_eq!(r2, Done("".as_bytes(), "abcdabcd".as_bytes()));

    println!("Done 2\n");
    let r3 = x("abcefg".as_bytes());
    assert_eq!(r3, Error(42));
  }
}
