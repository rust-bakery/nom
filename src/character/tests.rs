use super::streaming::*;
use crate::error::ParserKind;
use crate::internal::{Outcome, ParseResult};

#[test]
fn one_of_test() {
  fn f(i: &[u8]) -> ParseResult<&[u8], char> {
    one_of("ab")(i)
  }

  let a = &b"abcd"[..];
  assert_eq!(f(a), Ok((&b"bcd"[..], 'a')));

  let b = &b"cde"[..];
  assert_eq!(
    f(b),
    Err(Outcome::Failure(error_position!(b, ParserKind::OneOf)))
  );

  fn utf8(i: &str) -> ParseResult<&str, char> {
    one_of("+\u{FF0B}")(i)
  }

  assert!(utf8("+").is_ok());
  assert!(utf8("\u{FF0B}").is_ok());
}

#[test]
fn none_of_test() {
  fn f(i: &[u8]) -> ParseResult<&[u8], char> {
    none_of("ab")(i)
  }

  let a = &b"abcd"[..];
  assert_eq!(
    f(a),
    Err(Outcome::Failure(error_position!(a, ParserKind::NoneOf)))
  );

  let b = &b"cde"[..];
  assert_eq!(f(b), Ok((&b"de"[..], 'c')));
}

#[test]
fn char_byteslice() {
  fn f(i: &[u8]) -> ParseResult<&[u8], char> {
    char('c')(i)
  }

  let a = &b"abcd"[..];
  assert_eq!(
    f(a),
    Err(Outcome::Failure(error_position!(a, ParserKind::Char)))
  );

  let b = &b"cde"[..];
  assert_eq!(f(b), Ok((&b"de"[..], 'c')));
}

#[test]
fn char_str() {
  fn f(i: &str) -> ParseResult<&str, char> {
    char('c')(i)
  }

  let a = &"abcd"[..];
  assert_eq!(
    f(a),
    Err(Outcome::Failure(error_position!(a, ParserKind::Char)))
  );

  let b = &"cde"[..];
  assert_eq!(f(b), Ok((&"de"[..], 'c')));
}
