use nom::bytes::complete::escaped;
use nom::character::complete::digit1;
use nom::character::complete::one_of;
use nom::{error::ParserKind, Outcome, ParseResult};

fn esc(s: &str) -> ParseResult<&str, &str, (&str, ParserKind)> {
  escaped(digit1, '\\', one_of("\"n\\"))(s)
}

#[cfg(feature = "alloc")]
fn esc_trans(s: &str) -> ParseResult<&str, String, (&str, ParserKind)> {
  use nom::bytes::complete::{escaped_transform, tag};
  escaped_transform(digit1, '\\', tag("n"))(s)
}

#[test]
fn test_escaped() {
  assert_eq!(
    esc("abcd"),
    Err(Outcome::Failure(("abcd", ParserKind::Escaped)))
  );
}

#[test]
#[cfg(feature = "alloc")]
fn test_escaped_transform() {
  assert_eq!(
    esc_trans("abcd"),
    Err(Outcome::Failure(("abcd", ParserKind::EscapedTransform)))
  );
}
