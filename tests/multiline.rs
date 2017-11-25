#[macro_use]
extern crate nom;

use nom::types::CompleteStr;
use nom::{alphanumeric,eol};
use nom::IResult;

use std::str;

pub fn end_of_line<'a>(input: CompleteStr<'a>) -> IResult<CompleteStr<'a>, CompleteStr<'a>> {
  alt!(input, eof!() | eol)
}

pub fn read_line<'a>(input: CompleteStr<'a>) -> IResult<CompleteStr<'a>, CompleteStr<'a>> {
  terminated!(input, alphanumeric, end_of_line)
}

pub fn read_lines<'a>(input: CompleteStr<'a>) -> IResult<CompleteStr<'a>, Vec<CompleteStr<'a>>> {
  many0!(input, read_line)
}

#[test]
fn read_lines_test() {
  let res = Ok((
    CompleteStr(""),
    vec![CompleteStr("Duck"), CompleteStr("Dog"), CompleteStr("Cow")]
  ));

  assert_eq!(read_lines(CompleteStr("Duck\nDog\nCow\n")), res);
  assert_eq!(read_lines(CompleteStr("Duck\nDog\nCow")),  res);
}
