extern crate nom;

use nom::error::ParserKind;
use nom::error::ParseContext;
use nom::Outcome::Error;
use nom::ParseResult;

#[derive(Debug, PartialEq)]
pub enum CustomError<I> {
  MyError,
  Nom(I, ParserKind),
}

impl<I> ParseContext<I> for CustomError<I> {
  fn from_parser_kind(input: I, kind: ParserKind) -> Self {
    CustomError::Nom(input, kind)
  }

  fn append(_: I, _: ParserKind, other: Self) -> Self {
    other
  }
}

fn parse(input: &str) -> ParseResult<&str, &str, CustomError<&str>> {
  Err(Error(CustomError::MyError))
}

#[cfg(test)]
mod tests {
  use super::parse;
  use super::CustomError;
  use nom::Outcome::Error;

  #[test]
  fn it_works() {
    let err = parse("").unwrap_err();
    match err {
      Error(e) => assert_eq!(e, CustomError::MyError),
      _ => panic!("Unexpected error: {:?}", err),
    }
  }
}
