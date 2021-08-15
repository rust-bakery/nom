//! Combinators to parse expression with operator precedence.

use crate::{IResult, Parser, Err};
use crate::error::{ErrorKind, ParseError, FromExternalError};

/// A single evaluation step.
pub enum Operation<P, O> {
	/// A prefix operation.
	Prefix(P, O),
	/// A postfix operation.
	Postfix(O, P),
	/// A binary operation.
	Binary(O, P, O),
}

/// Associativity for binary operators.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Assoc {
	/// Left associative.
	Left,
	/// Right associative.
	Right,
}

/// Element for operator stack.
enum Operator<P, Q: Ord + Copy> {
	Prefix(P, Q),
	Postfix(P, Q),
	Binary(P, Q, Assoc),
}

/// An unary operator.
pub struct Unary<V, Q: Ord + Copy> {
	value: V,
	precedence: Q,
}

/// A binary operator.
pub struct Binary<V, Q: Ord + Copy> {
	value: V,
	precedence: Q,
	assoc: Assoc,
}

/// Runs the inner parser and transforms the result into an unary operator with the given precedence.
/// 
/// Intended for use with [precedence].
/// # Arguments
/// * `parser` The parser to apply.
/// * `precedence` The precedence of the operator.
pub fn unary_op<I, O , E, P, Q>(mut parser: P, precedence: Q) -> impl FnMut(I) -> IResult<I, Unary<O, Q>, E>
where
	P: Parser<I, O, E>,
	Q: Ord + Copy,
{
	move |input| {
		match parser.parse(input) {
			Ok((i, out)) => Ok((i, Unary{value: out, precedence})),
			Err(e) => Err(e),
		}
	}
}

/// Runs the inner parser and transforms the result into a bianry operator with the given precedence and associativity.
/// 
/// Intended for use with [precedence].
/// # Arguments
/// * `parser` The parser to apply.
/// * `precedence` The precedence of the operator.
/// * `assoc` The associativity of the operator.
pub fn binary_op<I, O , E, P, Q>(mut parser: P, precedence: Q, assoc: Assoc) -> impl FnMut(I) -> IResult<I, Binary<O, Q>, E>
where
	P: Parser<I, O, E>,
	Q: Ord + Copy,
{
	move |input| {
		match parser.parse(input) {
			Ok((i, out)) => Ok((i, Binary{value: out, precedence, assoc})),
			Err(e) => Err(e),
		}
	}
}

impl<P, O> Operator<P, O>
where
	O: Ord + Copy,
{
	fn precedence(&self) -> O {
		match self {
			Operator::Prefix(_, p) => *p,
			Operator::Postfix(_, p) => *p,
			Operator::Binary(_, p, _) => *p,
		}
	}
	
	fn is_postfix(&self) -> bool {
		match self {
			Operator::Postfix(_, _) => true,
			_ => false,
		}
	}
}

/// Parses expression with operator precedence. Supports prefix, postfix and binary operators.
/// Operators are applied in ascending precedence.
/// 
/// The prefix and postfix parsers are called repedeatly until they fail.
/// 
/// Expressions are folded as soon as possible. The result will be reused as another operand.
/// After the expression has been read completely any remaining operations are folded and the
/// resulting, single operand is returned as the result.
/// 
/// It will return `Err(Err:Error((_, ErrorKind::Precedence)))` if:
/// * the `fold` function returns an `Err`.
/// * more than one operand remains after the expression has been read completely.
/// * the input does not match the regex: `prefix* operand postfix* (binary prefix* operand postfix*)*`
/// 
/// # Arguments
/// * `prefix` Parser to parse prefix unary operators.
/// * `postfix` Parser to parse postfix unary operators.
/// * `binary` Parser to parse binary operators.
/// * `operand` Parser to parse operands.
/// * `fold` Function that performs a single evaluation step and returns a result.
/// 
/// # Pitfalls
/// It is possible to specify operator precedences that allow inputs which are impossible to satisfy. This
/// parser does not guard against such cases and will parse the input successfully for as long as its
/// in the form of the above regex.
/// 
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, Needed, IResult};
/// # use nom::precedence::{precedence, unary_op, binary_op, Operation, Assoc, fail};
/// # use nom::character::complete::digit1;
/// # use nom::combinator::{map, verify};
/// # use nom::sequence::delimited;
/// # use nom::bytes::complete::tag;
/// # use nom::branch::alt;
/// fn parser(i: &str) -> IResult<&str, i64> {
///   precedence(
///     unary_op(tag("-"), 1),
///     unary_op(verify(tag(""), |s: &str| false), 2), //TODO, replace with a "fail" parser?
///     alt((
///       binary_op(tag("*"), 3, Assoc::Left),
///       binary_op(tag("/"), 3, Assoc::Left),
///       binary_op(tag("+"), 4, Assoc::Left),
///       binary_op(tag("-"), 4, Assoc::Left),
///     )),
///     alt((
///       map(digit1, |s: &str| s.parse::<i64>().unwrap()),
///       delimited(tag("("), parser, tag(")")),
///     )),
///     |op: Operation<&str, i64>| {
///       use nom::precedence::Operation::*;
///       match op {
///         Prefix("-", o) => Ok(-o),
///         Binary(lhs, "*", rhs) => Ok(lhs * rhs),
///         Binary(lhs, "/", rhs) => Ok(lhs / rhs),
///         Binary(lhs, "+", rhs) => Ok(lhs + rhs),
///         Binary(lhs, "-", rhs) => Ok(lhs - rhs),
///         _ => Err("Invalid combination"),
///       }
///     }
///   )(i)
/// }
/// 
/// assert_eq!(parser("8-2*2"), Ok(("", 4)));
/// assert_eq!(parser("4-(2+2)"), Ok(("", 0)));
/// ```
pub fn precedence<I, O, E, E2, F, G, H1, H3, H2, P, Q> (
	mut prefix: H1,
	mut postfix: H2,
	mut binary: H3,
	mut operand: F,
	mut fold: G,
) -> impl FnMut(I) -> IResult<I, O, E>
where
	I: Clone + PartialEq,
	E: ParseError<I> + FromExternalError<I, E2>,
	F: Parser<I, O, E>,
	G: FnMut(Operation<P, O>) -> Result<O, E2>,
	H1: Parser<I, Unary<P, Q>, E>,
	H2: Parser<I, Unary<P, Q>, E>,
	H3: Parser<I, Binary<P, Q>, E>,
	Q: Ord + Copy,
{
	move |mut i| {
		let mut operands = Vec::new();
		let mut operators = Vec::new();
		let mut i1 = i.clone();
		
		'main: loop {
			'prefix: loop {
				match prefix.parse(i1.clone()) {
					Err(Err::Error(_)) => break 'prefix,
					Err(e) => return Err(e),
					Ok((i2, o)) => {
						// infinite loop check: the parser must always consume
						if i2 == i1 {
							return Err(Err::Error(E::from_error_kind(i1, ErrorKind::Precedence)));
						}
						i1 = i2;
						operators.push(Operator::Prefix(o.value, o.precedence));
					},
				}
			}
			
			let (i2, o) = match operand.parse(i1.clone()) {
				Ok((i, o)) => (i, o),
				Err(e) => return Err(e),
			};
			i1 = i2;
			operands.push(o);
			
			'postfix: loop {
				match postfix.parse(i1.clone()) {
					Ok((i2, o)) => {
						// infinite loop check: the parser must always consume
						if i2 == i1 {
							return Err(Err::Error(E::from_error_kind(i1, ErrorKind::Precedence)));
						}
						
						while operators.last()
							.map(|op| op.precedence() <= o.precedence)
							.unwrap_or(false)
						{
							let value = operands.pop().unwrap();
							let operation = match operators.pop().unwrap() {
								Operator::Prefix(op, _) => Operation::Prefix(op, value),
								Operator::Postfix(op, _) => Operation::Postfix(value, op),
								Operator::Binary(op, _, _) => {
									match operands.pop() {
										Some(lhs) => Operation::Binary(lhs, op, value),
										None => return Err(Err::Error(E::from_error_kind(i1, ErrorKind::Precedence))),
									}
									
								},
							};
							let result = match fold(operation) {
								Err(e) => return Err(Err::Error(E::from_external_error(i, ErrorKind::Precedence, e))),
								Ok(r) => r,
							};
							operands.push(result);
						}
						i1 = i2;
						operators.push(Operator::Postfix(o.value, o.precedence));
					},
					Err(_) => break 'postfix,
				}
			}
			
			match binary.parse(i1.clone()) {
				Ok((i2, o)) => {
					while operators.last()
					.map(|op| op.precedence() < o.precedence ||
						(o.assoc == Assoc::Left && op.precedence() == o.precedence) ||
						(op.is_postfix())) //TODO cut out here to fix above behaviour f "3**3()"?
						//TODO do a precedence check here to error on "impossible precedence?"
					.unwrap_or(false) {
						let value = operands.pop().unwrap();
							let operation = match operators.pop().unwrap() {
								Operator::Prefix(op, _) => Operation::Prefix(op, value),
								Operator::Postfix(op, _) => Operation::Postfix(value, op),
								Operator::Binary(op, _, _) => {
									match operands.pop() {
										Some(lhs) => Operation::Binary(lhs, op, value),
										None => return Err(Err::Error(E::from_error_kind(i1, ErrorKind::Precedence))),
									}
								},
							};
							let result = match fold(operation) {
								Err(e) => return Err(Err::Error(E::from_external_error(i, ErrorKind::Precedence, e))),
								Ok(r) => r,
							};
							operands.push(result);
					}
					operators.push(Operator::Binary(o.value, o.precedence, o.assoc));
					i1 = i2;
				},
				Err(_) => break 'main,
			}
			
			// infinite loop check: either operand or operator must consume input
			if i == i1 {
				return Err(Err::Error(E::from_error_kind(i, ErrorKind::Precedence)));
			}
			i = i1.clone();
		}
		
		while operators.len() > 0 {
			let value = match operands.pop() {
				Some(o) => o,
				None => return Err(Err::Error(E::from_error_kind(i, ErrorKind::Precedence))),
			};
			let operation = match operators.pop().unwrap() {
				Operator::Prefix(op, _) => Operation::Prefix(op, value),
				Operator::Postfix(op, _) => Operation::Postfix(value, op),
				Operator::Binary(op, _, _) => {
					match operands.pop() {
						Some(lhs) => Operation::Binary(lhs, op, value),
						None => return Err(Err::Error(E::from_error_kind(i, ErrorKind::Precedence))),
					}
					
				},
			};
			let result = match fold(operation) {
				Ok(r) => r,
				Err(e) => return Err(Err::Error(E::from_external_error(i, ErrorKind::Precedence, e))),
			};
			operands.push(result);
		}
		
		if operands.len() == 1 {
			return Ok((i1, operands.pop().unwrap()));
		} else {
			return Err(Err::Error(E::from_error_kind(i, ErrorKind::Precedence)));
		}
	}
}