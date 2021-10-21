#![allow(dead_code)]

use nom::bytes::streaming::tag;
use nom::character::streaming::digit1 as digit;
use nom::combinator::verify;
use nom::error::{ParseContext, ParserKind};
#[cfg(feature = "alloc")]
use nom::multi::count;
use nom::sequence::terminated;
use nom::ParseResult;

#[derive(Debug)]
pub struct CustomError(String);

impl<'a> From<(&'a str, ParserKind)> for CustomError {
  fn from(error: (&'a str, ParserKind)) -> Self {
    CustomError(format!("error code was: {:?}", error))
  }
}

impl<'a> ParseContext<&'a str> for CustomError {
  fn from_parser_kind(_: &'a str, kind: ParserKind) -> Self {
    CustomError(format!("error code was: {:?}", kind))
  }

  fn append(_: &'a str, kind: ParserKind, other: CustomError) -> Self {
    CustomError(format!("{:?}\nerror code was: {:?}", other, kind))
  }
}

fn test1(input: &str) -> ParseResult<&str, &str, CustomError> {
  //fix_error!(input, CustomError, tag!("abcd"))
  tag("abcd")(input)
}

fn test2(input: &str) -> ParseResult<&str, &str, CustomError> {
  //terminated!(input, test1, fix_error!(CustomError, digit))
  terminated(test1, digit)(input)
}

fn test3(input: &str) -> ParseResult<&str, &str, CustomError> {
  verify(test1, |s: &str| s.starts_with("abcd"))(input)
}

#[cfg(feature = "alloc")]
fn test4(input: &str) -> ParseResult<&str, Vec<&str>, CustomError> {
  count(test1, 4)(input)
}
