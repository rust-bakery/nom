use super::streaming::*;
use crate::error::ErrorKind;
use crate::internal::{Err, IResult};

#[test]
fn one_of_test() {
  // Tip: matching a [u8] with a one_of(str) is probably an error, and won't handle multi-byte
  // UTF-8 sequences in the `list`, and may lead to unexpected behaviour.
  fn f(i: &[u8]) -> IResult<&[u8], char> {
    one_of("abç")(i)
  }

  let a = &b"abcd"[..];
  assert_eq!(f(a), Ok((&b"bcd"[..], 'a')));

  let b = &b"cde"[..];
  assert_eq!(f(b), Err(Err::Error(error_position!(b, ErrorKind::OneOf))));

  // This doesn't match because b"ç" == [0xC3, 0xA7] but 'ç' == 0xe7.
  let c = "çde".as_bytes();
  assert_eq!(f(c), Err(Err::Error(error_position!(c, ErrorKind::OneOf))));

  // ...but this will match.
  let d = &b"\xE7de"[..];
  assert_eq!(f(d), Ok((&d[1..], '\u{E7}')));

  // A one_of([u8]) should be used with [u8] inputs.
  fn f2(i: &[u8]) -> IResult<&[u8], char> {
    // abç
    one_of(&b"ab\xC3\xA7"[..])(i)
  }

  let a = &b"abcd"[..];
  assert_eq!(f2(a), Ok((&b"bcd"[..], 'a')));

  let b = &b"cde"[..];
  assert_eq!(f2(b), Err(Err::Error(error_position!(b, ErrorKind::OneOf))));

  // This will match, but only on the first byte of the ç sequence
  let c = &b"\xC3\xA7de"[..];
  assert_eq!(f2(c), Ok((&c[1..], '\u{C3}')));

  // Using from the second byte of the ç sequence should also match
  assert_eq!(f2(&c[1..]), Ok((&c[2..], '\u{A7}')));

  // A one_of(str) should match multi-byte sequences on str inputs.
  fn utf8_str(i: &str) -> IResult<&str, char> {
    one_of("+\u{FF0B}")(i)
  }
  assert_eq!(utf8_str("+"), Ok(("", '+')));
  assert_eq!(utf8_str("\u{FF0B}"), Ok(("", '\u{FF0B}')));

  // Don't match on multi-byte sequences with the same prefix
  let ff0c = "\u{FF0C}";
  assert_eq!(
    utf8_str(ff0c),
    Err(Err::Error(error_position!(ff0c, ErrorKind::OneOf)))
  );

  // Matching a [u8] with one_of(str) should only match for single-byte
  // codepoints. Using one_of in this way is probably an error.
  fn utf8_bytes_with_str_list(i: &[u8]) -> IResult<&[u8], char> {
    one_of("+\u{FF0B}")(i)
  }

  assert_eq!(utf8_bytes_with_str_list(&b"+"[..]), Ok((&b""[..], '+')));
  let ff0b = &b"\xEF\xBC\x8B"[..];
  assert_eq!(
    utf8_bytes_with_str_list(ff0b),
    Err(Err::Error(error_position!(ff0b, ErrorKind::OneOf)))
  );

  // one_of([u8]) should not match on UTF-8 sequences, and should allow invalid sequences
  fn utf8_bytes(i: &[u8]) -> IResult<&[u8], char> {
    one_of(&b"+\xDC\xEF\xBC\x8B\0\x8C"[..])(i)
  }

  assert_eq!(utf8_bytes(&b"+"[..]), Ok((&b""[..], '+')));
  assert_eq!(utf8_bytes(&b"\0"[..]), Ok((&b""[..], '\0')));
  // Because this is a one_of([u8]), we can match on bytes
  assert_eq!(utf8_bytes(ff0b), Ok((&ff0b[1..], '\u{EF}')));

  let dc00 = &b"\xDC\01234"[..];
  assert_eq!(utf8_bytes(dc00), Ok((&dc00[1..], '\u{DC}')));
}

#[test]
fn none_of_test() {
  // Tip: matching a [u8] with a none_of(str) is probably an error, and won't handle multi-byte
  // UTF-8 sequences in the `list`.
  fn f(i: &[u8]) -> IResult<&[u8], char> {
    none_of("ab\u{E7}")(i)
  }

  let a = &b"abcd"[..];
  assert_eq!(f(a), Err(Err::Error(error_position!(a, ErrorKind::NoneOf))));

  let b = &b"cde"[..];
  assert_eq!(f(b), Ok((&b"de"[..], 'c')));

  // This doesn't match none_of because b"ç" == [0xC3, 0xA7] but 'ç' == 0xe7.
  let c = "\u{E7}de".as_bytes();
  assert_eq!(f(c), Ok((&c[1..], '\u{C3}')));

  // This will match none_of because b"\u{7f00}" == [0xE7, 0xBC, 0x80].
  let d = "\u{7f00}".as_bytes();
  assert_eq!(f(d), Err(Err::Error(error_position!(d, ErrorKind::NoneOf))));

  // A one_of([u8]) should be used with [u8] inputs.
  fn f2(i: &[u8]) -> IResult<&[u8], char> {
    // abç
    none_of(&b"ab\xC3\xA7"[..])(i)
  }

  let a = &b"abcd"[..];
  assert_eq!(
    f2(a),
    Err(Err::Error(error_position!(a, ErrorKind::NoneOf)))
  );

  let b = &b"cde"[..];
  assert_eq!(f2(b), Ok((&b"de"[..], 'c')));

  let c = "\u{E7}de".as_bytes();
  assert_eq!(
    f2(c),
    Err(Err::Error(error_position!(c, ErrorKind::NoneOf)))
  );

  let d = &b"\xE7de"[..];
  assert_eq!(f(d), Err(Err::Error(error_position!(d, ErrorKind::NoneOf))));

  let e = "\u{A7}de".as_bytes();
  assert_eq!(f2(e), Ok((&e[1..], '\u{C2}')));

  // A none_of(str) should match multi-byte sequences on str inputs.
  fn utf8_str(i: &str) -> IResult<&str, char> {
    none_of("+\u{FF0B}")(i)
  }

  let a = "+";
  assert_eq!(
    utf8_str(a),
    Err(Err::Error(error_position!(a, ErrorKind::NoneOf)))
  );

  let b = "\u{FF0B}";
  assert_eq!(
    utf8_str(b),
    Err(Err::Error(error_position!(b, ErrorKind::NoneOf)))
  );

  // Multi-byte sequence with the same prefix
  let ff0c = "\u{FF0C}";
  assert_eq!(utf8_str(ff0c), Ok(("", '\u{FF0C}')));

  // Matching a [u8] with none_of(str) should only match for single-byte
  // codepoints. Using one_of in this way is probably an error.
  fn utf8_bytes_with_str_list(i: &[u8]) -> IResult<&[u8], char> {
    none_of("+\u{FF0B}")(i)
  }

  let a = &b"+"[..];
  assert_eq!(
    utf8_bytes_with_str_list(a),
    Err(Err::Error(error_position!(a, ErrorKind::NoneOf)))
  );

  let b = "\u{FF0B}".as_bytes();
  assert_eq!(utf8_bytes_with_str_list(b), Ok((&b[1..], '\u{EF}')));

  // one_of([u8]) should not match on UTF-8 sequences, and should allow invalid sequences
  fn utf8_bytes(i: &[u8]) -> IResult<&[u8], char> {
    none_of(&b"+\xDC\xEF\xBC\x8B\0\x8C"[..])(i)
  }

  let a = &b"+"[..];
  assert_eq!(
    utf8_bytes(a),
    Err(Err::Error(error_position!(a, ErrorKind::NoneOf)))
  );

  let b = &b"\0"[..];
  assert_eq!(
    utf8_bytes(b),
    Err(Err::Error(error_position!(b, ErrorKind::NoneOf)))
  );

  // b'\xBC' is in the none_of list, but '\u{BC}' is encoded as [0xC2, 0xBC].
  let c = "\u{BC}".as_bytes();
  assert_eq!(utf8_bytes(c), Ok((&c[1..], '\u{C2}')));

  let d = &b"\xDC\01234"[..];
  assert_eq!(
    utf8_bytes(d),
    Err(Err::Error(error_position!(d, ErrorKind::NoneOf)))
  );
}

#[test]
fn char_byteslice() {
  fn f(i: &[u8]) -> IResult<&[u8], char> {
    char('c')(i)
  }

  let a = &b"abcd"[..];
  assert_eq!(f(a), Err(Err::Error(error_position!(a, ErrorKind::Char))));

  let b = &b"cde"[..];
  assert_eq!(f(b), Ok((&b"de"[..], 'c')));
}

#[test]
fn char_str() {
  fn f(i: &str) -> IResult<&str, char> {
    char('c')(i)
  }

  let a = "abcd";
  assert_eq!(f(a), Err(Err::Error(error_position!(a, ErrorKind::Char))));

  let b = "cde";
  assert_eq!(f(b), Ok(("de", 'c')));
}
