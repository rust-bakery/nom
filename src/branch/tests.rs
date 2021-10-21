use crate::branch::{alt, permutation};
use crate::bytes::streaming::tag;
use crate::error::ParserKind;
use crate::internal::{Needed, Outcome, ParseResult};
#[cfg(feature = "alloc")]
use crate::{
  error::ParseContext,
  lib::std::{
    fmt::Debug,
    string::{String, ToString},
  },
};

#[cfg(feature = "alloc")]
#[derive(Debug, Clone, PartialEq)]
pub struct ErrorStr(String);

#[cfg(feature = "alloc")]
impl From<u32> for ErrorStr {
  fn from(i: u32) -> Self {
    ErrorStr(format!("custom error code: {}", i))
  }
}

#[cfg(feature = "alloc")]
impl<'a> From<&'a str> for ErrorStr {
  fn from(i: &'a str) -> Self {
    ErrorStr(format!("custom error message: {}", i))
  }
}

#[cfg(feature = "alloc")]
impl<I: Debug> ParseContext<I> for ErrorStr {
  fn from_parser_kind(input: I, kind: ParserKind) -> Self {
    ErrorStr(format!("custom error message: ({:?}, {:?})", input, kind))
  }

  fn append(input: I, kind: ParserKind, other: Self) -> Self {
    ErrorStr(format!(
      "custom error message: ({:?}, {:?}) - {:?}",
      input, kind, other
    ))
  }
}

#[cfg(feature = "alloc")]
#[test]
fn alt_test() {
  fn work(input: &[u8]) -> ParseResult<&[u8], &[u8], ErrorStr> {
    Ok((&b""[..], input))
  }

  #[allow(unused_variables)]
  fn dont_work(input: &[u8]) -> ParseResult<&[u8], &[u8], ErrorStr> {
    Err(Outcome::Failure(ErrorStr("abcd".to_string())))
  }

  fn work2(input: &[u8]) -> ParseResult<&[u8], &[u8], ErrorStr> {
    Ok((input, &b""[..]))
  }

  fn alt1(i: &[u8]) -> ParseResult<&[u8], &[u8], ErrorStr> {
    alt((dont_work, dont_work))(i)
  }
  fn alt2(i: &[u8]) -> ParseResult<&[u8], &[u8], ErrorStr> {
    alt((dont_work, work))(i)
  }
  fn alt3(i: &[u8]) -> ParseResult<&[u8], &[u8], ErrorStr> {
    alt((dont_work, dont_work, work2, dont_work))(i)
  }
  //named!(alt1, alt!(dont_work | dont_work));
  //named!(alt2, alt!(dont_work | work));
  //named!(alt3, alt!(dont_work | dont_work | work2 | dont_work));

  let a = &b"abcd"[..];
  assert_eq!(
    alt1(a),
    Err(Outcome::Failure(error_node_position!(
      a,
      ParserKind::Alt,
      ErrorStr("abcd".to_string())
    )))
  );
  assert_eq!(alt2(a), Ok((&b""[..], a)));
  assert_eq!(alt3(a), Ok((a, &b""[..])));

  fn alt4(i: &[u8]) -> ParseResult<&[u8], &[u8]> {
    alt((tag("abcd"), tag("efgh")))(i)
  }
  let b = &b"efgh"[..];
  assert_eq!(alt4(a), Ok((&b""[..], a)));
  assert_eq!(alt4(b), Ok((&b""[..], b)));
}

#[test]
fn alt_incomplete() {
  fn alt1(i: &[u8]) -> ParseResult<&[u8], &[u8]> {
    alt((tag("a"), tag("bc"), tag("def")))(i)
  }

  let a = &b""[..];
  assert_eq!(alt1(a), Err(Outcome::Incomplete(Needed::new(1))));
  let a = &b"b"[..];
  assert_eq!(alt1(a), Err(Outcome::Incomplete(Needed::new(1))));
  let a = &b"bcd"[..];
  assert_eq!(alt1(a), Ok((&b"d"[..], &b"bc"[..])));
  let a = &b"cde"[..];
  assert_eq!(
    alt1(a),
    Err(Outcome::Failure(error_position!(a, ParserKind::Tag)))
  );
  let a = &b"de"[..];
  assert_eq!(alt1(a), Err(Outcome::Incomplete(Needed::new(1))));
  let a = &b"defg"[..];
  assert_eq!(alt1(a), Ok((&b"g"[..], &b"def"[..])));
}

#[test]
fn permutation_test() {
  fn perm(i: &[u8]) -> ParseResult<&[u8], (&[u8], &[u8], &[u8])> {
    permutation((tag("abcd"), tag("efg"), tag("hi")))(i)
  }

  let expected = (&b"abcd"[..], &b"efg"[..], &b"hi"[..]);

  let a = &b"abcdefghijk"[..];
  assert_eq!(perm(a), Ok((&b"jk"[..], expected)));
  let b = &b"efgabcdhijk"[..];
  assert_eq!(perm(b), Ok((&b"jk"[..], expected)));
  let c = &b"hiefgabcdjk"[..];
  assert_eq!(perm(c), Ok((&b"jk"[..], expected)));

  let d = &b"efgxyzabcdefghi"[..];
  assert_eq!(
    perm(d),
    Err(Outcome::Failure(error_node_position!(
      &b"efgxyzabcdefghi"[..],
      ParserKind::Permutation,
      error_position!(&b"xyzabcdefghi"[..], ParserKind::Tag)
    )))
  );

  let e = &b"efgabc"[..];
  assert_eq!(perm(e), Err(Outcome::Incomplete(Needed::new(1))));
}
