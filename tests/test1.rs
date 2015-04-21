#[macro_use]
extern crate nom;

use nom::{IResult,Needed,Producer,FileProducer,ProducerState,not_line_ending};
use nom::IResult::*;
use nom::Err::*;

use std::str;
use std::fmt::Debug;
/*
#[test]
fn map_test_x() {
  let res = Done((), &b"abcd"[..]).map(|data| { str::from_utf8(data).unwrap() });
  assert_eq!(res, Done((), "abcd"));
}
*/
#[test]
#[allow(unused_must_use)]
fn tag() {
  FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
    let mut p = producer;
    named!(f,tag!("https://"));
    //p.push(|par| par.flat_map(f).flat_map(print));
    fn pr<'a>(data:&'a [u8]) -> IResult<&'a [u8],()> {
      //let p = f(data).map_res(str::from_utf8);//.flat_map(print);
      let p = f(data);
      println!("p : {:?}", p);
      Done(&b""[..], ())
    }
    pusher!(ps, pr);
    ps(&mut p);
    //assert!(false);
  });
}

pub fn print<'a,T: Debug>(input: T) -> IResult<'a,T,()> {
  println!("{:?}", input);
  Done(input, ())
}


#[test]
fn is_not() {
  //is_not!(foo b"\r\n");
  named!(foo<&[u8],&[u8]>, is_not!(&b"\r\n"[..]));
  let a = &b"ab12cd\nefgh"[..];
  assert_eq!(foo(a), Done(&b"\nefgh"[..], &b"ab12cd"[..]));
}

#[test]
fn exported_public_method_defined_by_macro() {
  let a = &b"ab12cd\nefgh"[..];
  assert_eq!(not_line_ending(a), Done(&b"\nefgh"[..], &b"ab12cd"[..]));
}

