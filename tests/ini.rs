#![feature(globs,macro_rules,phase)]

#[phase(plugin,link)]
extern crate nom;

use nom::{IResult,Producer,FileProducer,ProducerState,Mapper,Mapper2,line_ending,not_line_ending};
use nom::IResult::*;

use std::str;
use std::fmt::Show;

fn empty_result(i:&[u8]) -> IResult<&[u8], ()> { Done(i,()) }

#[test]
fn parse_ini_test() {
  let ini_file = ";comment
[category]
parameter=value
key = value2

[other]
number = 1234
str = a b cc dd ; comment";

  let ini_without_comment = "[category]
parameter=value
key = value2

[other]
number = 1234
str = a b cc dd ; comment";

  tag!(semicolon ";".as_bytes());
  o!(comment<&[u8], ()> semicolon not_line_ending line_ending ~ empty_result ~);

  let res = Done((), ini_file.as_bytes()).flat_map(comment);
  println!("{}", res);
  match res {
    IResult::Done(i, o) => println!("i: {} | o: {}", str::from_utf8(i), o),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_comment.as_bytes(), ()));
}

