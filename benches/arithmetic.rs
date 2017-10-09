#![feature(test)]
extern crate test;

#[macro_use]
extern crate nom;

use test::Bencher;
use nom::{IResult,digit};

// Parser definition

use std::str;
use std::str::FromStr;

// We parse any expr surrounded by parens, ignoring all whitespaces around those
named!(parens<i64>, ws!(delimited!( tag!("("), expr, tag!(")") )) );

// We transform an integer string into a i64, ignoring surrounding whitespaces
// We look for a digit suite, and try to convert it.
// If either str::from_utf8 or FromStr::from_str fail,
// we fallback to the parens parser defined above
named!(factor<i64>, alt!(
    map_res!(
      map_res!(
        ws!(digit),
        str::from_utf8
      ),
      FromStr::from_str
    )
  | parens
  )
);

// We read an initial factor and for each time we find
// a * or / operator followed by another factor, we do
// the math by folding everything
named!(term <i64>, do_parse!(
    init: factor >>
    res:  fold_many0!(
        pair!(alt!(tag!("*") | tag!("/")), factor),
        init,
        |acc, (op, val): (&[u8], i64)| {
            if (op[0] as char) == '*' { acc * val } else { acc / val }
        }
    ) >>
    (res)
  )
);

named!(expr <i64>, do_parse!(
    init: term >>
    res:  fold_many0!(
        pair!(alt!(tag!("+") | tag!("-")), term),
        init,
        |acc, (op, val): (&[u8], i64)| {
            if (op[0] as char) == '+' { acc + val } else { acc - val }
        }
    ) >>
    (res)
  )
);


#[bench]
fn arithmetic(b: &mut Bencher) {
  let data = &b"  2*2 / ( 5 - 1) + 3 / 4 * (2 - 7 + 567 *12 /2) + 3*(1+2*( 45 /2))";

  println!("parsed:\n{:?}", expr(&data[..]));
  b.iter(||{
    expr(&data[..])
  });
}

