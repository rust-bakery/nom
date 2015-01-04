#![feature(globs,macro_rules,phase)]

#[phase(plugin,link)]
extern crate nom;

use nom::{IResult,Producer,FileProducer,ProducerState,Mapper,Mapper2,line_ending,not_line_ending, space, alphanumeric};
use nom::IResult::*;

use std::str;
use std::fmt::Show;

fn empty_result(i:&[u8]) -> IResult<&[u8], ()> { Done(i,()) }
tag!(semicolon ";".as_bytes());
o!(comment_body<&[u8],&[u8]> semicolon ~ not_line_ending ~ );
o!(comment<&[u8], ()> comment_body line_ending ~ empty_result ~);
opt!(opt_comment<&[u8],&[u8]> comment_body);

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

tag!(equal "=".as_bytes());
fn not_equal(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in range(0, input.len()) {
    if input[idx] == '=' as u8 {
      return Done(input.slice_from(idx), input.slice(0, idx))
    }
  }
  Done("".as_bytes(), input)
}

fn not_line_ending_or_semicolon(input:&[u8]) -> IResult<&[u8], &[u8]> {
  for idx in range(0, input.len()) {
    if input[idx] == '\n' as u8 || input[idx] == ';' as u8 {
      return Done(input.slice_from(idx), input.slice(0, idx))
    }
  }
  Done("".as_bytes(), input)
}

opt!(opt_line_ending<&[u8],&[u8]> line_ending);
o!(value<&[u8],&[u8]> space equal space ~ not_line_ending_or_semicolon ~ space opt_comment  opt_line_ending);
chain!(key_value<&[u8],(&[u8],&[u8])>, ||{(key, val)},  key: alphanumeric, val: value,);

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

#[test]
fn parse_key_value_test() {
  let ini_file = "parameter=value
key = value2";

  let ini_without_key_value = "key = value2";

  let res = Done((), ini_file.as_bytes()).flat_map(key_value);
  println!("{}", res);
  match res {
    IResult::Done(i, (o1, o2)) => println!("i: {} | o: ({},{})", str::from_utf8(i), str::from_utf8(o1), str::from_utf8(o2)),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_key_value.as_bytes(), ("parameter".as_bytes(), "value".as_bytes())));
}


#[test]
fn parse_key_value_with_space_test() {
  let ini_file = "parameter = value
key = value2";

  let ini_without_key_value = "key = value2";

  let res = Done((), ini_file.as_bytes()).flat_map(key_value);
  println!("{}", res);
  match res {
    IResult::Done(i, (o1, o2)) => println!("i: {} | o: ({},{})", str::from_utf8(i), str::from_utf8(o1), str::from_utf8(o2)),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_key_value.as_bytes(), ("parameter".as_bytes(), "value".as_bytes())));
}

#[test]
fn parse_key_value_with_comment_test() {
  let ini_file = "parameter=value;abc
key = value2";

  let ini_without_key_value = "key = value2";

  let res = Done((), ini_file.as_bytes()).flat_map(key_value);
  println!("{}", res);
  match res {
    IResult::Done(i, (o1, o2)) => println!("i: {} | o: ({},{})", str::from_utf8(i), str::from_utf8(o1), str::from_utf8(o2)),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_key_value.as_bytes(), ("parameter".as_bytes(), "value".as_bytes())));
}
