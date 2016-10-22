#[macro_use]
extern crate nom;

use nom::{IResult,alphanumeric,eol};

use std::str;

named!(end_of_line, alt!(eof!() | eol));
named!(read_line <&str>, map_res!(
  terminated!(alphanumeric, end_of_line),
  str::from_utf8
));
named!(read_lines <Vec<&str> >, many0!(read_line));

#[test]
fn read_lines_test() {
  let res = IResult::Done(&b""[..], vec!["Duck", "Dog", "Cow"]);

  assert_eq!(read_lines(&b"Duck\nDog\nCow\n"[..]), res);
  assert_eq!(read_lines(&b"Duck\nDog\nCow"[..]),   res);
}
