use nom::{
  branch::alt,
  bytes::complete::tag,
  character::complete::{digit1 as digit, alphanumeric1 as alphanumeric},
  combinator::{map_res, map},
  multi::separated_list0,
  sequence::delimited,
  IResult,
  precedence::{precedence, Assoc, binary_op, unary_op, Operation},
};

// Elements of the abstract syntax tree (ast) that represents an expression.
#[derive(Debug, Eq, PartialEq)]
pub enum Expr {
  // A number literal.
  Number(i64),
  // An identifier.
  Identifier(String),
  // Arithmetic operations. Each have a left hand side (lhs) and a right hand side (rhs).
  Add(Box<Expr>, Box<Expr>),
  Sub(Box<Expr>, Box<Expr>),
  Mul(Box<Expr>, Box<Expr>),
  Div(Box<Expr>, Box<Expr>),
  // The function call operation. Left is the expression the function is called on, right is the list of parameters.
  Call(Box<Expr>, Vec<Expr>),
}

// We need to be able to encode different types of operators. So we make the operator parser output one of the Operator enums.
enum Operator<'a> {
  // A "raw" operator. This encodes operators that have no additional information beyond their own representation (e.g. "+", "*", "-").
  Raw(&'a str),
  // The function call operator. In addition to its own representation "()" it carries additional information that we need to keep here.
  // Specifically the vector of expressions that make up the parameters.
  Call(Vec<Expr>),
}

// Convenience parser for operators without additional info.
fn token<'a>(t: &'a str) -> impl FnMut(&'a str) -> IResult<&'a str, Operator<'a>>
{
  move |input: &'a str| {
    map(tag(t), |s: &str| Operator::Raw(s))(input)
  }
}

// Parser for function calls.
fn function_call(i: &str) -> IResult<&str, Operator> {
  map(
    delimited(
      tag("("),
      // subexpressions are evaluated by recursing back into the expression parser.
      separated_list0(tag(","), expression),
      tag(")")
    ),
    |v: Vec<Expr>| Operator::Call(v)
  )(i)
}

// The actual expression parser .
fn expression(i: &str) -> IResult<&str, Expr> {
  precedence(
    unary_op(2, token("-")),
    // function calls are implemented as postfix unary operators.
    unary_op(1, function_call),
    alt((
      binary_op(3, Assoc::Left, alt((
        token("*"),
        token("/"),
      ))),
      binary_op(4, Assoc::Left, alt((
        token("+"),
        token("-"),
      )))
    )),
    alt((
      map_res(digit,
        |s: &str| match s.parse::<i64>() {
          Ok(s) => Ok(Expr::Number(s)),
          Err(e) => Err(e),
        }
      ),
      map(alphanumeric, |s: &str| Expr::Identifier(s.to_string())),
      delimited(tag("("), expression, tag(")")),
    )),
    |op: Operation<Operator, Expr>| {
      use nom::precedence::Operation::*;
      use Operator::*;
      match op {
        // Unary minus gets evaluated to the same representation as a multiplication with -1.
        Prefix(Raw("-"), e) => Ok(Expr::Mul(Expr::Number(-1).into(), e.into())),
        // The list of parameters are taken from the operator and placed into the ast.
        Postfix(e, Call(p)) => Ok(Expr::Call(e.into(), p)),
        // Raw operators get turned into their respective ast nodes.
        Binary(lhs, Raw("*"), rhs) => Ok(Expr::Mul(lhs.into(), rhs.into())),
        Binary(lhs, Raw("/"), rhs) => Ok(Expr::Div(lhs.into(), rhs.into())),
        Binary(lhs, Raw("+"), rhs) => Ok(Expr::Add(lhs.into(), rhs.into())),
        Binary(lhs, Raw("-"), rhs) => Ok(Expr::Sub(lhs.into(), rhs.into())),
        _ => Err("Invalid op combo."),
      }
    }
  )(i)
}

#[test]
fn expression_test() {
  assert_eq!(
    expression("-2*max(2,3)-2").map(|(i, x)| (i, format!("{:?}", x))),
    Ok(("", String::from("Sub(Mul(Mul(Number(-1), Number(2)), Call(Identifier(\"max\"), [Number(2), Number(3)])), Number(2))")))
  );
}