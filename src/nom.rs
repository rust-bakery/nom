#![desc = "Omnomnom incremental byte parser"]
#![license = "MIT"]
#![macro_escape]

extern crate collections;

use std::fmt::Show;
use internal::*;
use internal::IResult::*;

#[macro_export]
macro_rules! tag(
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      if i.len() >= $inp.len() && i.slice(0, $inp.len()) == $inp {
        Done(i.slice_from($inp.len()), i.slice(0, 0))
      } else {
        Error(0)
      }
    }
  )
)

macro_rules! o (
  ($name:ident<$i:ty,$o:ty> $f1:expr $($rest:tt)*) => (
    #[allow(unused_variables)]
    fn $name(input:$i) -> IResult<$i, $o>{
      match $f1(input) {
        IResult::Error(e)      => IResult::Error(e),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i,o)     => {
          o_parser!(i o $($rest)*)
        }
      }
    }
  );
)

macro_rules! o_parser (
  ($i:expr $o:expr) => (Done($i,$o));

  ($i:expr $o:expr ~ $e:expr ~ $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,o)     => {
        o_parser!(i o $($rest)*)
      }
    }

   );
  ($i:expr $o:expr $e:expr $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,_)     => {
        o_parser!(i $o $($rest)*)
      }
    }
   );
)

macro_rules! chain (
  ($name:ident<$i:ty,$o:ty>, $assemble:expr, $($rest:tt)*) => (
    fn $name(i:$i) -> IResult<$i,$o>{
      chaining_parser!(i, $assemble, $($rest)*)
    }
  );
)

macro_rules! chaining_parser (
  ($i:expr, $assemble:expr, $field:ident : $e:expr, $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,o)     => {
        let $field = o;
        chaining_parser!(i, $assemble, $($rest)*)
      }
    }
  );

  ($i:expr, $assemble:expr, ) => (
    IResult::Done($i, $assemble())
  )
)

macro_rules! alt (
  ($name:ident<$i:ty,$o:ty>, $($rest:tt)*) => (
    fn $name(i:$i) -> IResult<$i,$o>{
      alt_parser!(i, $($rest)*)
    }
  );
)

macro_rules! alt_parser (
  ($i:expr, $e:expr $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(_)      => alt_parser!($i, $($rest)*),
      IResult::Incomplete(_) => alt_parser!($i, $($rest)*),
      IResult::Done(i,o)     => IResult::Done(i,o)
    }
  );

  ($i:expr, ) => (
    IResult::Error(1)
  )
)

pub fn print<'a,T: Show>(input: T) -> IResult<T, ()> {
  println!("{}", input);
  Done(input, ())
}

pub fn begin<'a>(input: &'a [u8]) -> IResult<(), &'a [u8]> {
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
)

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
)

#[macro_export]
macro_rules! filter(
  ($name:ident $f:ident) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      for idx in range(0, input.len()) {
        if !$f(input[idx]) {
          return IResult::Done(input.slice_from(idx), input.slice(0, idx))
        }
      }
      IResult::Done("".as_bytes(), input)
    }
  )
)

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
// public methods
//pub is_not!(line_ending "\r\n".as_bytes())
pub fn line_ending(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in range(0, input.len()) {
    for &i in "\r\n".as_bytes().iter() {
      if input[idx] == i {
        return Done(input.slice_from(idx), input.slice(0, idx))
      }
    }
  }
  Done("".as_bytes(), input)
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


// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
//pub filter!(alpha is_alphabetic)
//pub filter!(digit is_digit)
//pub filter!(alphanumeric is_alphanumeric)
pub fn alpha(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in range(0, input.len()) {
    if !is_alphabetic(input[idx]) {
      return Done(input.slice_from(idx), input.slice(0, idx))
    }
  }
  Done("".as_bytes(), input)
}

pub fn digit(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in range(0, input.len()) {
    if !is_digit(input[idx]) {
      return Done(input.slice_from(idx), input.slice(0, idx))
    }
  }
  Done("".as_bytes(), input)
}

pub fn alphanumeric(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in range(0, input.len()) {
    if !is_alphanumeric(input[idx]) {
      return Done(input.slice_from(idx), input.slice(0, idx))
    }
  }
  Done("".as_bytes(), input)
}

pub fn sized_buffer(input:&[u8]) -> IResult<&[u8], &[u8]> {
  if input.len() == 0 {
    return Incomplete(0)
  }

  let len = input[0] as uint;

  if input.len() >= len + 1 {
    return Done(input.slice_from(len+1), input.slice(1, len+1))
  } else {
    return Incomplete(0)
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
)

#[cfg(test)]
mod tests {
  use super::*;
  use map::*;
  use internal::IResult;
  use internal::IResult::*;

  #[test]
  fn character_test() {
    let empty = "".as_bytes();
    let a = "abcd".as_bytes();
    let b = "1234".as_bytes();
    let c = "a123".as_bytes();
    let d = "azé12".as_bytes();
    assert_eq!(Done((),a).flat_map(alpha), Done(empty, a))
    assert_eq!(Done((),b).flat_map(alpha), Done(b, empty))
    assert_eq!(Done((),c).flat_map(alpha), Done(c.slice_from(1), "a".as_bytes()))
    assert_eq!(Done((),d).flat_map(alpha), Done("é12".as_bytes(), "az".as_bytes()))
    assert_eq!(Done((),a).flat_map(digit), Done(a, empty))
    assert_eq!(Done((),b).flat_map(digit), Done(empty, b))
    assert_eq!(Done((),c).flat_map(digit), Done(c, empty))
    assert_eq!(Done((),d).flat_map(digit), Done(d, empty))
    assert_eq!(Done((),a).flat_map(alphanumeric), Done(empty, a))
    assert_eq!(Done((),b).flat_map(alphanumeric), Done(empty, b))
    assert_eq!(Done((),c).flat_map(alphanumeric), Done(empty, c))
    assert_eq!(Done((),d).flat_map(alphanumeric), Done("é12".as_bytes(), "az".as_bytes()))
  }

  #[test]
  fn is_not_test() {
    let a = "ab12cd\nefgh".as_bytes();
    assert_eq!(Done((), a).flat_map(line_ending), Done("\nefgh".as_bytes(), "ab12cd".as_bytes()))
  }

  #[test]
  fn sized_buffer_test() {
    let arr:[u8, ..6] = [3, 4, 5, 6, 7, 8];
    let res = Done((), arr.as_slice()).flat_map(sized_buffer);
    let i = [7,8];
    let o = [4,5,6];
    assert_eq!(res, Done(i.as_slice(), o.as_slice()))
  }

  #[test]
  fn t1() {
    let v1:Vec<u8> = vec![1,2,3];
    let v2:Vec<u8> = vec![4,5,6];
    let d = Done(v1.as_slice(), v2.as_slice());
    let res = d.flat_map(print);
    assert_eq!(res, Done(v2.as_slice(), ()));
  }

  #[deriving(PartialEq,Eq,Show)]
  struct B {
    a: int,
    b: int
  }

  #[test]
  fn chain_and_ignore_test() {
    tag!(x "abcd".as_bytes());
    tag!(y "efgh".as_bytes());
    fn ret_int(i:&[u8]) -> IResult<&[u8], int> { Done(i,1) };
    //o!(z<&[u8], int>  x S x S retInt Z y);
    o!(z<&[u8], int>  x  x ~ret_int~ y);

    let r = Done((), "abcdabcdefgh".as_bytes()).flat_map(z);
    assert_eq!(r, Done("".as_bytes(), 1));
  }


  #[test]
  fn chain_test() {
    tag!(x "abcd".as_bytes());
    fn temp_ret_int1(i:&[u8]) -> IResult<&[u8], int> { Done(i,1) };
    o!(ret_int1<&[u8],int> x ~ temp_ret_int1 ~);
    fn ret_int2(i:&[u8]) -> IResult<&[u8], int> { Done(i,2) };
    chain!(f<&[u8],B>, ||{B{a: aa, b: bb}}, aa: ret_int1, bb: ret_int2,);

    let r = Done((), "abcde".as_bytes()).flat_map(f);
    assert_eq!(r, Done("e".as_bytes(), B{a: 1, b: 2}));
  }

  #[test]
  fn alt_test() {
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

    alt!(alt1<&[u8],&[u8]>, dont_work dont_work)
    alt!(alt2<&[u8],&[u8]>, dont_work work)
    alt!(alt3<&[u8],&[u8]>, dont_work dont_work work2 dont_work)

    let a = "abcd".as_bytes();
    assert_eq!(Done((), a).flat_map(alt1), Error(1))
    assert_eq!(Done((), a).flat_map(alt2), Done("".as_bytes(), a))
    assert_eq!(Done((), a).flat_map(alt3), Done(a, "".as_bytes()))
  }

#[test]
  fn opt_test() {
    tag!(x "abcd".as_bytes())
    opt!(o<&[u8],&[u8]> x)

    let a = "abcdef".as_bytes();
    let b = "bcdefg".as_bytes();
    assert_eq!(Done((),a).flat_map(o), Done("ef".as_bytes(), Some("".as_bytes())))
    assert_eq!(Done((),b).flat_map(o), Done("bcdefg".as_bytes(), None))
  }

  /* FIXME: this makes rustc weep
  fn pr(par: IResult<(),&[u8]>) -> IResult<&[u8], ()> {
    Error(0)
  }

  #[test]
  fn rustc_panic_test() {
    FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
      let mut p = producer;
      p.push(pr);
    });
  }*/
}
