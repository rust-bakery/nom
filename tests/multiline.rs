#[macro_use]
extern crate nom;

use nom::types::CompleteStr;
use nom::{alphanumeric, eol};
use nom::IResult;

pub fn end_of_line(input: CompleteStr) -> IResult<CompleteStr, CompleteStr> {
  alt!(input, eof!() | eol)
}

pub fn read_line(input: CompleteStr) -> IResult<CompleteStr, CompleteStr> {
  terminated!(input, alphanumeric, end_of_line)
}

pub fn read_lines(input: CompleteStr) -> IResult<CompleteStr, Vec<CompleteStr>> {
  many0!(input, read_line)
}

#[cfg(feature = "alloc")]
#[test]
fn read_lines_test() {
  let res = Ok((
    CompleteStr(""),
    vec![CompleteStr("Duck"), CompleteStr("Dog"), CompleteStr("Cow")],
  ));

  assert_eq!(read_lines(CompleteStr("Duck\nDog\nCow\n")), res);
  assert_eq!(read_lines(CompleteStr("Duck\nDog\nCow")), res);
}
