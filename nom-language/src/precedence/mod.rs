//! Combinators to parse expressions with operator precedence.

#[cfg(test)]
mod tests;

use nom::error::{ErrorKind, FromExternalError, ParseError};
use nom::{Check, Err, IResult, Input, Mode, OutputM, OutputMode, Parser};

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

/// A single evaluation step.
pub enum Operation<P1, P2, P3, O> {
  /// A prefix operation.
  Prefix(P1, O),
  /// A postfix operation.
  Postfix(O, P2),
  /// A binary operation.
  Binary(O, P3, O),
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
enum Operator<P1, P2, P3, Q: Ord + Copy> {
  Prefix(P1, Q),
  Postfix(P2, Q),
  Binary(P3, Q, Assoc),
}

impl<P1, P2, P3, Q> Operator<P1, P2, P3, Q>
where
  Q: Ord + Copy,
{
  fn precedence(&self) -> Q {
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

/// Runs the inner parser and transforms the result into an unary operator with the given precedence.
///
/// Intended for use with [precedence].
/// # Arguments
/// * `precedence` The precedence of the operator.
/// * `parser` The parser to apply.
pub fn unary_op<I, O, E, P, Q>(
  precedence: Q,
  mut parser: P,
) -> impl FnMut(I) -> IResult<I, Unary<O, Q>, E>
where
  P: Parser<I, Output = O, Error = E>,
  Q: Ord + Copy,
{
  move |input| match parser.parse(input) {
    Ok((i, value)) => Ok((i, Unary { value, precedence })),
    Err(e) => Err(e),
  }
}

/// Runs the inner parser and transforms the result into a binary operator with the given precedence and associativity.
///
/// Intended for use with [precedence].
/// # Arguments
/// * `precedence` The precedence of the operator.
/// * `assoc` The associativity of the operator.
/// * `parser` The parser to apply.
pub fn binary_op<I, O, E, P, Q>(
  precedence: Q,
  assoc: Assoc,
  mut parser: P,
) -> impl FnMut(I) -> IResult<I, Binary<O, Q>, E>
where
  P: Parser<I, Output = O, Error = E>,
  Q: Ord + Copy,
{
  move |input| match parser.parse(input) {
    Ok((i, value)) => Ok((
      i,
      Binary {
        value,
        precedence,
        assoc,
      },
    )),
    Err(e) => Err(e),
  }
}

/// Parses an expression with operator precedence.
///
/// Supports prefix, postfix and binary operators. Operators are applied in ascending precedence.
///
/// The parser will track its current position inside the expression and call the respective
/// operand/operator parsers. The prefix and postfix parsers are called repeatedly until they fail before
/// execution moves on to the operand or binary parser.
///
/// Expressions are folded as soon as possible. The result will be reused as another operand. After the
/// expression has been read completely any remaining operations are folded and the resulting, single
/// operand is returned as the result.
///
/// It will return `Err(Err:Error((_, ErrorKind::Precedence)))` if:
/// * the `fold` function returns an `Err`.
/// * more than one or no operands remain after the expression has been evaluated completely.
/// * the input does not match the pattern: `prefix* operand postfix* (binary prefix* operand postfix*)*`
///
/// # Arguments
/// * `prefix` Parser for prefix unary operators.
/// * `postfix` Parser for postfix unary operators.
/// * `binary` Parser for binary operators.
/// * `operand` Parser for operands.
/// * `fold` Function that evaluates a single operation and returns the result.
///
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, IResult};
/// use nom_language::precedence::{precedence, unary_op, binary_op, Assoc, Operation};
/// use nom::character::complete::digit1;
/// use nom::combinator::{map_res, fail};
/// use nom::sequence::delimited;
/// use nom::bytes::complete::tag;
/// use nom::branch::alt;
///
/// fn parser(i: &str) -> IResult<&str, i64> {
///   precedence(
///     unary_op(1, tag("-")),
///     fail(),
///     alt((
///       binary_op(2, Assoc::Left, tag("*")),
///       binary_op(2, Assoc::Left, tag("/")),
///       binary_op(3, Assoc::Left, tag("+")),
///       binary_op(3, Assoc::Left, tag("-")),
///     )),
///     alt((
///       map_res(digit1, |s: &str| s.parse::<i64>()),
///       delimited(tag("("), parser, tag(")")),
///     )),
///     |op: Operation<&str, &str, &str, i64>| {
///       use nom_language::precedence::Operation::*;
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
/// assert_eq!(parser("3-(2*3)+7+2*2-(2*(2+4))"), Ok(("", -4)));
/// ```
///
/// # Evaluation order
/// This parser reads expressions from left to right and folds operations as soon as possible. This
/// behaviour is only important when using an operator grammar that allows for ambigious expressions.
///
/// For example, the expression `-a++**b` is ambigious with the following precedence.
///
/// | Operator | Position | Precedence | Associativity |
/// |----------|----------|------------|---------------|
/// | **       | Binary   | 1          | Right         |
/// | -        | Prefix   | 2          | N/A           |
/// | ++       | Postfix  | 3          | N/A           |
///
/// The expression can be parsed in two ways: `-((a++)**b)` or `((-a)++)**b`. This parser will always
/// parse it as the latter because of how it evaluates expressions:
/// * It reads, left-to-right, the first two operators `-a++`.
/// * Because the minus takes precedence over the increment it is evaluated immediately `(-a)++`.
/// * It then reads the remaining input and evaluates the increment next in order to preserve its
/// position in the expression \
/// `((-a)++)**b`.
pub fn precedence<I, O, E, E2, F, G, H1, H3, H2, P1, P2, P3, Q>(
  mut prefix: H1,
  mut postfix: H2,
  mut binary: H3,
  mut operand: F,
  mut fold: G,
) -> impl FnMut(I) -> IResult<I, O, E>
where
  I: Clone + PartialEq,
  E: ParseError<I> + FromExternalError<I, E2>,
  F: Parser<I, Output = O, Error = E>,
  G: FnMut(Operation<P1, P2, P3, O>) -> Result<O, E2>,
  H1: Parser<I, Output = Unary<P1, Q>, Error = E>,
  H2: Parser<I, Output = Unary<P2, Q>, Error = E>,
  H3: Parser<I, Output = Binary<P3, Q>, Error = E>,
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
          }
        }
      }

      let (i2, o) = match operand.parse(i1.clone()) {
        Ok((i, o)) => (i, o),
        Err(Err::Error(e)) => return Err(Err::Error(E::append(i, ErrorKind::Precedence, e))),
        Err(e) => return Err(e),
      };
      i1 = i2;
      operands.push(o);

      'postfix: loop {
        match postfix.parse(i1.clone()) {
          Err(Err::Error(_)) => break 'postfix,
          Err(e) => return Err(e),
          Ok((i2, o)) => {
            // infinite loop check: the parser must always consume
            if i2 == i1 {
              return Err(Err::Error(E::from_error_kind(i1, ErrorKind::Precedence)));
            }

            while operators
              .last()
              .map(|op| op.precedence() <= o.precedence)
              .unwrap_or(false)
            {
              let value = operands.pop().unwrap();
              let operation = match operators.pop().unwrap() {
                Operator::Prefix(op, _) => Operation::Prefix(op, value),
                Operator::Postfix(op, _) => Operation::Postfix(value, op),
                Operator::Binary(op, _, _) => match operands.pop() {
                  Some(lhs) => Operation::Binary(lhs, op, value),
                  None => return Err(Err::Error(E::from_error_kind(i1, ErrorKind::Precedence))),
                },
              };
              let result = match fold(operation) {
                Err(e) => {
                  return Err(Err::Error(E::from_external_error(
                    i,
                    ErrorKind::Precedence,
                    e,
                  )))
                }
                Ok(r) => r,
              };
              operands.push(result);
            }
            i1 = i2;
            operators.push(Operator::Postfix(o.value, o.precedence));
          }
        }
      }

      match binary.parse(i1.clone()) {
        Err(Err::Error(_)) => break 'main,
        Err(e) => return Err(e),
        Ok((i2, o)) => {
          while operators
            .last()
            .map(|op| {
              op.precedence() < o.precedence
                || (o.assoc == Assoc::Left && op.precedence() == o.precedence)
                || (op.is_postfix())
            })
            .unwrap_or(false)
          {
            let value = operands.pop().unwrap();
            let operation = match operators.pop().unwrap() {
              Operator::Prefix(op, _) => Operation::Prefix(op, value),
              Operator::Postfix(op, _) => Operation::Postfix(value, op),
              Operator::Binary(op, _, _) => match operands.pop() {
                Some(lhs) => Operation::Binary(lhs, op, value),
                None => return Err(Err::Error(E::from_error_kind(i1, ErrorKind::Precedence))),
              },
            };
            let result = match fold(operation) {
              Err(e) => {
                return Err(Err::Error(E::from_external_error(
                  i,
                  ErrorKind::Precedence,
                  e,
                )))
              }
              Ok(r) => r,
            };
            operands.push(result);
          }
          operators.push(Operator::Binary(o.value, o.precedence, o.assoc));
          i1 = i2;
        }
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
        Operator::Binary(op, _, _) => match operands.pop() {
          Some(lhs) => Operation::Binary(lhs, op, value),
          None => return Err(Err::Error(E::from_error_kind(i, ErrorKind::Precedence))),
        },
      };
      let result = match fold(operation) {
        Ok(r) => r,
        Err(e) => {
          return Err(Err::Error(E::from_external_error(
            i,
            ErrorKind::Precedence,
            e,
          )))
        }
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

/// Applies a parser multiple times separated by another parser.
///
/// It is similar to [`separated_list1`][nom::multi::separated_list1] but instead of collecting
/// into a vector, you have a callback to build the output.
///
/// In a LALR grammar a left recursive operator is usually built with a rule syntax such as:
///  * A := A op B | B
///
/// If you try to parse that wth [`alt`][nom::branch::alt] it will fail with a stack overflow
/// because the recusion is unlimited. This function solves this problem by converting the recusion
/// into an iteration.
///
/// Compare with a right recursive operator, that in LALR would be:
///  * A := B op A | B
/// Or equivalently:
///  * A := B (op A)?
///
///  That can be written in `nom` trivially.
///
/// This stops when either parser returns an error and returns the last built value. to instead chain an error up, see
/// [`cut`][nom::combinator::cut].
///
/// # Arguments
/// * `child` The parser to apply.
/// * `operator` Parses the operator between argument.
/// * `init` A function returning the initial value.
/// * `fold` The function that combines a result of `f` with
///       the current accumulator.
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, error::ErrorKind, Needed, IResult, Parser};
/// use nom_language::precedence::left_assoc;
/// use nom::branch::alt;
/// use nom::sequence::delimited;
/// use nom::character::complete::{char, digit1};
///
/// fn add(i: &str) -> IResult<&str, String> {
///     left_assoc(mult, char('+'), |a, o, b| format!("{o}{a}{b}")).parse(i)
/// }
/// fn mult(i: &str) -> IResult<&str, String> {
///     left_assoc(single, char('*'), |a, o, b| format!("{o}{a}{b}")).parse(i)
/// }
/// fn single(i: &str) -> IResult<&str, String> {
///     alt((
///         digit1.map(|x: &str| x.to_string()),
///         delimited(char('('), add, char(')'))
///     )).parse(i)
/// }
///
/// assert_eq!(single("(1+2*3)"), Ok(("", String::from("+1*23"))));
/// assert_eq!(single("((1+2)*3)"), Ok(("", String::from("*+123"))));
/// assert_eq!(single("(1*2+3)"), Ok(("", String::from("+*123"))));
/// assert_eq!(single("((1+2*3)+4)"), Ok(("", String::from("++1*234"))));
/// assert_eq!(single("(1+(2*3+4))"), Ok(("", String::from("+1+*234"))));
/// ```
pub fn left_assoc<I, E, O, OP, G, F, B>(
  child: F,
  operator: G,
  builder: B,
) -> impl Parser<I, Output = O, Error = E>
where
  I: Clone + Input,
  E: ParseError<I>,
  F: Parser<I, Output = O, Error = E>,
  G: Parser<I, Output = OP, Error = E>,
  B: FnMut(O, OP, O) -> O,
{
  LeftAssoc {
    child,
    operator,
    builder,
  }
}

/// Parser implementation for the [`separated_list1`][nom::multi::separated_list1] combinator
pub struct LeftAssoc<F, G, B> {
  child: F,
  operator: G,
  builder: B,
}

impl<I, E, O, OP, G, F, B> Parser<I> for LeftAssoc<F, G, B>
where
  I: Clone + Input,
  E: ParseError<I>,
  F: Parser<I, Output = O, Error = E>,
  G: Parser<I, Output = OP, Error = E>,
  B: FnMut(O, OP, O) -> O,
{
  type Output = O;
  type Error = E;

  fn process<OM: OutputMode>(
    &mut self,
    mut i: I,
  ) -> nom::PResult<OM, I, Self::Output, Self::Error> {
    let (i1, mut res) = self.child.process::<OM>(i)?;
    i = i1;

    loop {
      let len = i.input_len();
      match self
        .operator
        .process::<OutputM<OM::Output, Check, OM::Incomplete>>(i.clone())
      {
        Err(Err::Error(_)) => return Ok((i, res)),
        Err(Err::Failure(e)) => return Err(Err::Failure(e)),
        Err(Err::Incomplete(e)) => return Err(Err::Incomplete(e)),
        Ok((i1, op)) => {
          match self
            .child
            .process::<OutputM<OM::Output, Check, OM::Incomplete>>(i1.clone())
          {
            Err(Err::Error(_)) => return Ok((i, res)),
            Err(Err::Failure(e)) => return Err(Err::Failure(e)),
            Err(Err::Incomplete(e)) => return Err(Err::Incomplete(e)),
            Ok((i2, rhs)) => {
              // infinite loop check: the parser must always consume
              if i2.input_len() == len {
                return Err(Err::Error(OM::Error::bind(|| {
                  <F as Parser<I>>::Error::from_error_kind(i, ErrorKind::SeparatedList)
                })));
              }
              // there is no combine() with 3 arguments, fake it with a tuple and two calls
              let op_rhs = OM::Output::combine(op, rhs, |op, rhs| (op, rhs));
              res = OM::Output::combine(res, op_rhs, |lhs, (op, rhs)| (self.builder)(lhs, op, rhs));
              i = i2;
            }
          }
        }
      }
    }
  }
}
