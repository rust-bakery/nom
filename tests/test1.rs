#![feature(globs,macro_rules,phase)]

#[phase(plugin,link)]
extern crate nom;

use nom::{IResult,Producer,FileProducer,ProducerState,Mapper,Mapper2,not_line_ending};
use nom::IResult::*;

use std::str;
use std::fmt::Show;

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
    fn pr(par: IResult<(),&[u8]>) -> IResult<&[u8],()> {
      let p = par.flat_map(f).map_res(str::from_utf8).flat_map(print);
      println!("p : {}", p);
      Done("".as_bytes(), ())
    }
    pusher!(ps, pr);
    ps(&mut p);
    //assert!(false);
  }); 
}

pub fn print<'a,T: Show>(input: T) -> IResult<T, ()> {
  println!("{}", input);
  Done(input, ())
}


#[test]
fn is_not() {
  is_not!(foo "\r\n".as_bytes());
  let a = "ab12cd\nefgh".as_bytes();
  assert_eq!(Done((), a).flat_map(foo), Done("\nefgh".as_bytes(), "ab12cd".as_bytes()));
}


#[test]
fn exported_public_method_defined_by_macro() {
  let a = "ab12cd\nefgh".as_bytes();
  assert_eq!(Done((), a).flat_map(not_line_ending), Done("\nefgh".as_bytes(), "ab12cd".as_bytes()));
}

