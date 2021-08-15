use crate::precedence::{binary_op, unary_op, Assoc, Operation};
use crate::{
  branch::alt,
  bytes::complete::tag,
  character::complete::digit1,
  combinator::{map, verify},
  internal::IResult,
  sequence::delimited,
};

#[cfg(feature = "alloc")]
use crate::precedence::precedence;

#[cfg(feature = "alloc")]
fn parser(i: &str) -> IResult<&str, i64> {
  precedence(
    unary_op(tag("-"), 1),
    unary_op(verify(tag(""), |_: &str| false), 2), //TODO, fail parser
    alt((
      binary_op(tag("*"), 3, Assoc::Left),
      binary_op(tag("/"), 3, Assoc::Left),
      binary_op(tag("+"), 4, Assoc::Left),
      binary_op(tag("-"), 4, Assoc::Left),
    )),
    alt((
      map(digit1, |s: &str| s.parse::<i64>().unwrap()),
      delimited(tag("("), parser, tag(")")),
    )),
    |op: Operation<&str, i64>| {
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
#[cfg(feature = "alloc")]
fn precedence_test() {
  assert_eq!(parser("3"), Ok(("", 3)));
  assert_eq!(parser("-3"), Ok(("", -3)));
  assert_eq!(parser("4-(2*2)"), Ok(("", 0)));
  assert_eq!(parser("4-2*2"), Ok(("", 0)));
  assert_eq!(parser("(4-2)*2"), Ok(("", 4)));
  assert_eq!(parser("2*2/1"), Ok(("", 4)));
}
