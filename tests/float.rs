#[macro_use]
extern crate nom;

use nom::{IResult,digit};

use std::str;
use std::str::FromStr;

named!(float <f32>, map_res!(
  map_res!(
    recognize!(
      alt!(
        delimited!(digit, tag!("."), opt!(digit)) |
        delimited!(opt!(digit), tag!("."), digit)
      )
    ),
    str::from_utf8
  ),
  FromStr::from_str
));

#[test]
fn float_test() {
  assert_eq!(float(&b"123.456"[..]), IResult::Done(&b""[..], 123.456));
  assert_eq!(float(&b"0.123"[..]),   IResult::Done(&b""[..], 0.123));
  assert_eq!(float(&b"123.0"[..]),   IResult::Done(&b""[..], 123.0));
  assert_eq!(float(&b"123."[..]),    IResult::Done(&b""[..], 123.0));
  assert_eq!(float(&b".123"[..]),    IResult::Done(&b""[..], 0.123));
}
