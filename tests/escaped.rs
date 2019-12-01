use nom::{Err, error::ErrorKind, IResult};
use nom::character::complete::digit1;
use nom::bytes::complete::escaped;
use nom::character::complete::one_of;

fn esc(s: &str) -> IResult<&str, &str> {
    escaped(digit1, '\\', one_of("\"n\\"))(s)
}

#[cfg(feature="alloc")]
fn esc_trans(s: &str) -> IResult<&str, String> {
    use nom::bytes::complete::{escaped_transform, tag};
    escaped_transform(digit1, '\\', |i: &str| tag("n")(i))(s)
}

#[test]
fn test_escaped() {
    assert_eq!(esc("abcd"), Err(Err::Error(("abcd", ErrorKind::Escaped))));
}

#[test]
#[cfg(feature="alloc")]
fn test_escaped_transform() {
    assert_eq!(esc_trans("abcd"), Err(Err::Error(("abcd", ErrorKind::EscapedTransform))));
}

#[test]
fn test_escaped_empty() {
    assert_eq!(esc(""), Err(Err::Error(("", ErrorKind::Escaped))));
}

#[test]
#[cfg(feature="alloc")]
fn test_escaped_transform_empty() {
    assert_eq!(esc_trans(""), Err(Err::Error(("", ErrorKind::EscapedTransform))));
}
