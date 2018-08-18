#[macro_use]
extern crate nom;

use nom::digit;
use nom::types::CompleteStr;

// Parser definition

use std::str::FromStr;

// We parse any expr surrounded by parens, ignoring all whitespaces around those
named!(parens<CompleteStr, i64>, ws!(delimited!( tag!("("), expr, tag!(")") )) );

// We transform an integer string into a i64, ignoring surrounding whitespaces
// We look for a digit suite, and try to convert it.
// If either str::from_utf8 or FromStr::from_str fail,
// we fallback to the parens parser defined above
named!(factor<CompleteStr, i64>, alt!(
    map_res!(
      ws!(digit),
      |s:CompleteStr| { FromStr::from_str(s.0) }
    )
  | parens
  )
);

// We read an initial factor and for each time we find
// a * or / operator followed by another factor, we do
// the math by folding everything
named!(term <CompleteStr, i64>, do_parse!(
    init: factor >>
    res:  fold_many0!(
        pair!(alt!(char!('*') | char!('/')), factor),
        init,
        |acc, (op, val): (char, i64)| {
            if op  == '*' { acc * val } else { acc / val }
        }
    ) >>
    (res)
  )
);

named!(expr <CompleteStr, i64>, do_parse!(
    init: term >>
    res:  fold_many0!(
        pair!(alt!(char!('+') | char!('-')), term),
        init,
        |acc, (op, val): (char, i64)| {
            if op == '+' { acc + val } else { acc - val }
        }
    ) >>
    (res)
  )
);

#[test]
fn factor_test() {
  assert_eq!(factor(CompleteStr("3")), Ok((CompleteStr(""), 3)));
  assert_eq!(factor(CompleteStr(" 12")), Ok((CompleteStr(""), 12)));
  assert_eq!(factor(CompleteStr("537  ")), Ok((CompleteStr(""), 537)));
  assert_eq!(factor(CompleteStr("  24   ")), Ok((CompleteStr(""), 24)));
}

#[test]
fn term_test() {
  assert_eq!(term(CompleteStr(" 12 *2 /  3")), Ok((CompleteStr(""), 8)));
  assert_eq!(
    term(CompleteStr(" 2* 3  *2 *2 /  3")),
    Ok((CompleteStr(""), 8))
  );
  assert_eq!(term(CompleteStr(" 48 /  3/2")), Ok((CompleteStr(""), 8)));
}

#[test]
fn expr_test() {
  assert_eq!(expr(CompleteStr(" 1 +  2 ")), Ok((CompleteStr(""), 3)));
  assert_eq!(
    expr(CompleteStr(" 12 + 6 - 4+  3")),
    Ok((CompleteStr(""), 17))
  );
  assert_eq!(expr(CompleteStr(" 1 + 2*3 + 4")), Ok((CompleteStr(""), 11)));
}

#[test]
fn parens_test() {
  assert_eq!(expr(CompleteStr(" (  2 )")), Ok((CompleteStr(""), 2)));
  assert_eq!(
    expr(CompleteStr(" 2* (  3 + 4 ) ")),
    Ok((CompleteStr(""), 14))
  );
  assert_eq!(
    expr(CompleteStr("  2*2 / ( 5 - 1) + 3")),
    Ok((CompleteStr(""), 4))
  );
}
