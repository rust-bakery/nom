#[macro_use]
extern crate nom;

use nom::{IResult,Producer,FileProducer,ProducerState,FlatMapOpt,Functor,not_line_ending};
use nom::IResult::*;

use std::str;
use std::fmt::Debug;

#[test]
fn map_test_x() {
  let res = Done((),"abcd".as_bytes()).map(|data| { str::from_utf8(data).unwrap() });
  assert_eq!(res, Done((), "abcd"));
}

#[test]
#[allow(unused_must_use)]
fn tag() {
  FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
    let mut p = producer;
    tag!(f "https://".as_bytes());
    //p.push(|par| par.flat_map(f).flat_map(print));
    fn pr<'a>(data:&'a [u8]) -> IResult<&'a [u8],()> {
      let p = f(data).map_res(str::from_utf8);//.flat_map(print);
      println!("p : {:?}", p);
      Done("".as_bytes(), ())
    }
    pusher!(ps, pr);
    ps(&mut p);
    //assert!(false);
  }); 
}

pub fn print<T: Debug>(input: T) -> IResult<T,()> {
  println!("{:?}", input);
  Done(input, ())
}


#[test]
fn is_not() {
  is_not!(foo "\r\n".as_bytes());
  let a = "ab12cd\nefgh".as_bytes();
  assert_eq!(foo(a), Done("\nefgh".as_bytes(), "ab12cd".as_bytes()));
}


#[test]
fn exported_public_method_defined_by_macro() {
  let a = "ab12cd\nefgh".as_bytes();
  assert_eq!(not_line_ending(a), Done("\nefgh".as_bytes(), "ab12cd".as_bytes()));
}

