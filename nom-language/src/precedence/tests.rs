use crate::precedence::{binary_op, unary_op, Assoc, Operation};
use nom::{
  branch::alt,
  bytes::complete::tag,
  character::complete::digit1,
  combinator::{fail, map_res},
  error::ErrorKind,
  error_node_position, error_position,
  sequence::delimited,
  Err, IResult,
};

use crate::precedence::precedence;

fn parser(i: &str) -> IResult<&str, i64> {
  precedence(
    unary_op(1, tag("-")),
    fail(),
    alt((
      binary_op(2, Assoc::Left, tag("*")),
      binary_op(2, Assoc::Left, tag("/")),
      binary_op(3, Assoc::Left, tag("+")),
      binary_op(3, Assoc::Left, tag("-")),
    )),
    alt((
      map_res(digit1, |s: &str| s.parse::<i64>()),
      delimited(tag("("), parser, tag(")")),
    )),
    |op: Operation<&str, (), &str, i64>| {
      use crate::precedence::Operation::*;
      match op {
        Prefix("-", o) => Ok(-o),
        Binary(lhs, "*", rhs) => Ok(lhs * rhs),
        Binary(lhs, "/", rhs) => Ok(lhs / rhs),
        Binary(lhs, "+", rhs) => Ok(lhs + rhs),
        Binary(lhs, "-", rhs) => Ok(lhs - rhs),
        _ => Err("Invalid combination"),
      }
    },
  )(i)
}

#[test]
fn precedence_test() {
  assert_eq!(parser("3"), Ok(("", 3)));
  assert_eq!(parser("-3"), Ok(("", -3)));
  assert_eq!(parser("4-(2*2)"), Ok(("", 0)));
  assert_eq!(parser("4-2*2"), Ok(("", 0)));
  assert_eq!(parser("(4-2)*2"), Ok(("", 4)));
  assert_eq!(parser("2*2/1"), Ok(("", 4)));

  let a = "a";

  assert_eq!(
    parser(a),
    Err(Err::Error(error_node_position!(
      &a[..],
      ErrorKind::Precedence,
      error_position!(&a[..], ErrorKind::Tag)
    )))
  );

  let b = "3+b";

  assert_eq!(
    parser(b),
    Err(Err::Error(error_node_position!(
      &b[2..],
      ErrorKind::Precedence,
      error_position!(&b[2..], ErrorKind::Tag)
    )))
  );
}
