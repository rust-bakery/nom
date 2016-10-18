#[macro_use]
extern crate nom;

use std::fmt;
use std::fmt::{Display, Debug, Formatter};

use std::str;
use std::str::FromStr;

use nom::{IResult, digit, multispace};

pub enum Expr {
    Value(i64),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Paren(Box<Expr>),
}

pub enum Oper {
    Add,
    Sub,
    Mul,
    Div,
}

impl Display for Expr {
    fn fmt(&self, format: &mut Formatter) -> fmt::Result {
        use self::Expr::*;
        match *self {
            Value(val) => write!(format, "{}", val),
            Add(ref left, ref right) => write!(format, "{} + {}", left, right),
            Sub(ref left, ref right) => write!(format, "{} - {}", left, right),
            Mul(ref left, ref right) => write!(format, "{} * {}", left, right),
            Div(ref left, ref right) => write!(format, "{} / {}", left, right),
            Paren(ref expr) => write!(format, "({})", expr),
        }
    }
}

impl Debug for Expr {
    fn fmt(&self, format: &mut Formatter) -> fmt::Result {
        use self::Expr::*;
        match *self {
            Value(val) => write!(format, "{}", val),
            Add(ref left, ref right) => write!(format, "({:?} + {:?})", left, right),
            Sub(ref left, ref right) => write!(format, "({:?} - {:?})", left, right),
            Mul(ref left, ref right) => write!(format, "({:?} * {:?})", left, right),
            Div(ref left, ref right) => write!(format, "({:?} / {:?})", left, right),
            Paren(ref expr) => write!(format, "[{:?}]", expr),
        }
    }
}

named!(parens< Expr >, delimited!(
    delimited!(opt!(multispace), tag!("("), opt!(multispace)),
    map!(map!(expr, Box::new), Expr::Paren),
    delimited!(opt!(multispace), tag!(")"), opt!(multispace))
  )
);

named!(factor< Expr >, alt_complete!(
    map!(
      map_res!(
        map_res!(
          delimited!(opt!(multispace), digit, opt!(multispace)),
          str::from_utf8
        ),
      FromStr::from_str
    ),
    Expr::Value)
  | parens
  )
);

fn fold_exprs(initial: Expr, remainder: Vec<(Oper, Expr)>) -> Expr {
    remainder.into_iter().fold(initial, |acc, pair| {
        let (oper, expr) = pair;
        match oper {
            Oper::Add => Expr::Add(Box::new(acc), Box::new(expr)),
            Oper::Sub => Expr::Sub(Box::new(acc), Box::new(expr)),
            Oper::Mul => Expr::Mul(Box::new(acc), Box::new(expr)),
            Oper::Div => Expr::Div(Box::new(acc), Box::new(expr)),
        }
    })
}

named!(term< Expr >, do_parse!(
    initial: factor >>
    remainder: many0!(
           alt!(
             do_parse!(tag!("*") >> mul: factor >> (Oper::Mul, mul)) |
             do_parse!(tag!("/") >> div: factor >> (Oper::Div, div))
           )
         ) >>
    (fold_exprs(initial, remainder))
));

named!(expr< Expr >, do_parse!(
    initial: term >>
    remainder: many0!(
           alt!(
             do_parse!(tag!("+") >> add: term >> (Oper::Add, add)) |
             do_parse!(tag!("-") >> sub: term >> (Oper::Sub, sub))
           )
         ) >>
    (fold_exprs(initial, remainder))
));

#[test]
fn factor_test() {
    assert_eq!(factor(&b"  3  "[..]).map(|x| format!("{:?}", x)),
               IResult::Done(&b""[..], String::from("3")));
}

#[test]
fn term_test() {
    assert_eq!(term(&b" 3 *  5   "[..]).map(|x| format!("{:?}", x)),
               IResult::Done(&b""[..], String::from("(3 * 5)")));
}

#[test]
fn expr_test() {
    assert_eq!(expr(&b" 1 + 2 *  3 "[..]).map(|x| format!("{:?}", x)),
               IResult::Done(&b""[..], String::from("(1 + (2 * 3))")));
    assert_eq!(expr(&b" 1 + 2 *  3 / 4 - 5 "[..]).map(|x| format!("{:?}", x)),
               IResult::Done(&b""[..], String::from("((1 + ((2 * 3) / 4)) - 5)")));
    assert_eq!(expr(&b" 72 / 2 / 3 "[..]).map(|x| format!("{:?}", x)),
               IResult::Done(&b""[..], String::from("((72 / 2) / 3)")));
}

#[test]
fn parens_test() {
    assert_eq!(expr(&b" ( 1 + 2 ) *  3 "[..]).map(|x| format!("{:?}", x)),
               IResult::Done(&b""[..], String::from("([(1 + 2)] * 3)")));
}
