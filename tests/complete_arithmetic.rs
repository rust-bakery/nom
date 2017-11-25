#[macro_use]
extern crate nom;

use nom::{AtEof,Compare,CompareResult,InputLength,InputIter,Slice,HexDisplay};

use std::str;
use std::str::{Chars,CharIndices,FromStr};
use std::ops::{Range,RangeTo,RangeFrom,RangeFull};
use std::iter::{Enumerate,Iterator};
use std::fmt;
use std::cmp::{min,PartialEq};

#[derive(Clone,Copy,Debug,PartialEq)]
pub struct CompleteStr<'a>(&'a str);

impl<'a> AtEof for CompleteStr<'a> {
  fn at_eof(&self) -> bool { true }
}

impl<'a> Slice<Range<usize>> for CompleteStr<'a> {
  fn slice(&self, range:Range<usize>) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> Slice<RangeTo<usize>> for CompleteStr<'a> {
  fn slice(&self, range:RangeTo<usize>) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> Slice<RangeFrom<usize>> for CompleteStr<'a> {
  fn slice(&self, range:RangeFrom<usize>) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> Slice<RangeFull> for CompleteStr<'a> {
  fn slice(&self, range:RangeFull) -> Self {
    CompleteStr(self.0.slice(range))
  }
}


impl<'a> InputIter for CompleteStr<'a> {
  type Item     = char;
  type RawItem  = char;
  type Iter     = CharIndices<'a>;
  type IterElem = Chars<'a>;

  fn iter_indices(&self)  -> Self::Iter {
    self.0.iter_indices()
  }
  fn iter_elements(&self) -> Self::IterElem {
    self.0.iter_elements()
  }
  fn position<P>(&self, predicate: P) -> Option<usize> where P: Fn(Self::RawItem) -> bool {
    self.0.position(predicate)
  }
  fn slice_index(&self, count:usize) -> Option<usize> {
    self.0.slice_index(count)
  }
}


impl<'a> InputLength for CompleteStr<'a> {
  fn input_len(&self) -> usize {
    self.0.input_len()
  }
}

impl<'a,'b> Compare<&'b str> for CompleteStr<'a> {
  fn compare(&self, t: &'b str) -> CompareResult {
    self.0.compare(t)
  }
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    self.0.compare_no_case(t)
  }
}

#[macro_export]
macro_rules! complete_named (
  ($name:ident, $submac:ident!( $($args:tt)* )) => (
    fn $name<'a>( i: CompleteStr<'a> ) -> nom::IResult<CompleteStr<'a>, CompleteStr<'a>, u32> {
      $submac!(i, $($args)*)
    }
  );
  ($name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
    fn $name<'a>( i: CompleteStr<'a> ) -> nom::IResult<CompleteStr<'a>, $o, u32> {
      $submac!(i, $($args)*)
    }
  );
);

complete_named!(digit, is_a!("0123456789"));

complete_named!(parens<i64>, ws!(delimited!( tag!("("), expr, tag!(")") )) );


complete_named!(factor<i64>, alt!(
      map_res!(
        ws!(digit),
        to_i64
    )
  | parens
  )
);

complete_named!(term <i64>, do_parse!(
    init: factor >>
    res:  fold_many0!(
        pair!(alt!(tag!("*") | tag!("/")), factor),
        init,
        |acc, (op, val): (CompleteStr, i64)| {
            if (op.0.chars().next().unwrap() as char) == '*' { acc * val } else { acc / val }
        }
    ) >>
    (res)
  )
);

complete_named!(expr <i64>, do_parse!(
    init: term >>
    res:  fold_many0!(
        pair!(alt!(tag!("+") | tag!("-")), term),
        init,
        |acc, (op, val): (CompleteStr, i64)| {
            if (op.0.chars().next().unwrap() as char) == '+' { acc + val } else { acc - val }
        }
    ) >>
    (res)
  )
);


fn to_i64<'a>(input: CompleteStr<'a>) -> Result<i64, ()> {
  match FromStr::from_str(input.0) {
    Err(_) => Err(()),
    Ok(i)  => Ok(i)
  }
}

#[test]
fn factor_test() {
  let a = CompleteStr("3");
  println!("calculated: {:?}", factor(a));
}

#[test]
fn parens_test() {
  let input1 = CompleteStr(" 2* (  3 + 4 ) ");
  assert_eq!(expr(input1), Ok((CompleteStr(""), 14)));

  let input2 = CompleteStr("  2*2 / ( 5 - 1) + 3");
  assert_eq!(expr(input2), Ok((CompleteStr(""), 4)));

  let input3 = CompleteStr("  2*2 / ( 5 - 1) +   ");
  assert_eq!(expr(input3), Ok((CompleteStr("+  "), 1)));
}
