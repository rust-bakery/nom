#[macro_use]
extern crate nom;

use nom::types::CompleteStr;

use std::str::FromStr;

#[macro_export]
macro_rules! complete_named (
  ($name:ident, $submac:ident!( $($args:tt)* )) => (
    fn $name( i: CompleteStr ) -> nom::IResult<CompleteStr, CompleteStr, u32> {
      $submac!(i, $($args)*)
    }
  );
  ($name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
    fn $name( i: CompleteStr ) -> nom::IResult<CompleteStr, $o, u32> {
      $submac!(i, $($args)*)
    }
  );
);

complete_named!(digit, is_a!("0123456789"));

complete_named!(parens<i64>, ws!(delimited!(tag!("("), expr, tag!(")"))));

complete_named!(factor<i64>, alt!(map_res!(ws!(digit), to_i64) | parens));

complete_named!(
  term<i64>,
  do_parse!(
    init: factor
      >> res:
        fold_many0!(
          pair!(alt!(tag!("*") | tag!("/")), factor),
          init,
          |acc, (op, val): (CompleteStr, i64)| if (op.0.chars().next().unwrap() as char) == '*' {
            acc * val
          } else {
            acc / val
          }
        ) >> (res)
  )
);

complete_named!(
  expr<i64>,
  do_parse!(
    init: term
      >> res:
        fold_many0!(
          pair!(alt!(tag!("+") | tag!("-")), term),
          init,
          |acc, (op, val): (CompleteStr, i64)| if (op.0.chars().next().unwrap() as char) == '+' {
            acc + val
          } else {
            acc - val
          }
        ) >> (res)
  )
);

complete_named!(root_expr<i64>, terminated!(expr, eof!()));

fn to_i64(input: CompleteStr) -> Result<i64, ()> {
  match FromStr::from_str(input.0) {
    Err(_) => Err(()),
    Ok(i) => Ok(i),
  }
}

#[test]
fn factor_test() {
  let a = CompleteStr("3");
  println!("calculated: {:?}", factor(a));
}

#[test]
fn parens_test() {
  use nom::ErrorKind;

  let input1 = CompleteStr(" 2* (  3 + 4 ) ");
  assert_eq!(expr(input1), Ok((CompleteStr(""), 14)));

  let input2 = CompleteStr("  2*2 / ( 5 - 1) + 3");
  assert_eq!(expr(input2), Ok((CompleteStr(""), 4)));

  let input3 = CompleteStr("  2*2 / ( 5 - 1) +   ");
  assert_eq!(
    root_expr(input3),
    Err(nom::Err::Error(error_position!(
      CompleteStr("+   "),
      ErrorKind::Eof
    )))
  );
}
