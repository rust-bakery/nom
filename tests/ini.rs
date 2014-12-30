#![feature(globs,macro_rules,phase)]

#[phase(plugin,link)]
extern crate nom;

use nom::{IResult,Producer,FileProducer,ProducerState,Mapper,Mapper2,line_ending,not_line_ending};
use nom::IResult::*;

use std::str;
use std::fmt::Show;

fn empty_result(i:&[u8]) -> IResult<&[u8], ()> { Done(i,()) }
tag!(semicolon ";".as_bytes());
o!(comment<&[u8], ()> semicolon not_line_ending line_ending ~ empty_result ~);
tag!(lsb "[".as_bytes());
tag!(rsb "]".as_bytes());
fn not_rsb(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in range(0, input.len()) {
    if input[idx] == ']' as u8 {
      return Done(input.slice_from(idx), input.slice(0, idx))
    }
  }
  Done("".as_bytes(), input)
}
o!(category<&[u8], &[u8]> lsb ~ not_rsb ~ rsb line_ending);

#[test]
fn parse_comment_test() {
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

  let res = Done((), ini_file.as_bytes()).flat_map(comment);
  println!("{}", res);
  match res {
    IResult::Done(i, o) => println!("i: {} | o: {}", str::from_utf8(i), o),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_comment.as_bytes(), ()));
}

#[test]
fn parse_category_test() {
  let ini_file = "[category]
parameter=value
key = value2";

  let ini_without_category = "parameter=value
key = value2";

  let res = Done((), ini_file.as_bytes()).flat_map(category);
  println!("{}", res);
  match res {
    IResult::Done(i, o) => println!("i: {} | o: {}", str::from_utf8(i), str::from_utf8(o)),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_category.as_bytes(), "category".as_bytes()));
}

