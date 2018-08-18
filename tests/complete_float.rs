#[macro_use]
extern crate nom;

use nom::digit;
use nom::types::CompleteStr;

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

complete_named!(
  unsigned_float<f32>,
  flat_map!(
    recognize!(alt!(
      delimited!(digit, tag!("."), opt!(digit)) | delimited!(opt!(digit), tag!("."), digit)
    )),
    parse_to!(f32)
  )
);

complete_named!(
  float<f32>,
  map!(
    pair!(opt!(alt!(tag!("+") | tag!("-"))), unsigned_float),
    |(sign, value): (Option<CompleteStr>, f32)| sign
      .and_then(|s| s.0.chars().next())
      .and_then(|c| if c == '-' { Some(-1f32) } else { None })
      .unwrap_or(1f32) * value
  )
);

#[test]
fn unsigned_float_test() {
  assert_eq!(
    unsigned_float(CompleteStr("123.456")),
    Ok((CompleteStr(""), 123.456))
  );
  assert_eq!(
    unsigned_float(CompleteStr("0.123")),
    Ok((CompleteStr(""), 0.123))
  );
  assert_eq!(
    unsigned_float(CompleteStr("123.0")),
    Ok((CompleteStr(""), 123.0))
  );
  assert_eq!(
    unsigned_float(CompleteStr("123.")),
    Ok((CompleteStr(""), 123.0))
  );
  assert_eq!(
    unsigned_float(CompleteStr(".123")),
    Ok((CompleteStr(""), 0.123))
  );
}

#[test]
fn float_test() {
  assert_eq!(
    float(CompleteStr("123.456")),
    Ok((CompleteStr(""), 123.456))
  );
  assert_eq!(
    float(CompleteStr("+123.456")),
    Ok((CompleteStr(""), 123.456))
  );
  assert_eq!(
    float(CompleteStr("-123.456")),
    Ok((CompleteStr(""), -123.456))
  );
}
