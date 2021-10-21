use super::*;
use crate::bytes::streaming::{tag, take};
use crate::error::ParserKind;
use crate::internal::{Needed, Outcome, ParseResult};
use crate::number::streaming::be_u16;

#[test]
fn single_element_tuples() {
  use crate::character::complete::alpha1;
  use crate::{error::ParserKind, Outcome};

  let mut parser = tuple((alpha1,));
  assert_eq!(parser("abc123def"), Ok(("123def", ("abc",))));
  assert_eq!(
    parser("123def"),
    Err(Outcome::Failure(("123def", ParserKind::Alpha)))
  );
}

#[derive(PartialEq, Eq, Debug)]
struct B {
  a: u8,
  b: u8,
}

#[derive(PartialEq, Eq, Debug)]
struct C {
  a: u8,
  b: Option<u8>,
}

/*FIXME: convert code examples to new error management
use util::{add_error_pattern, error_to_list, print_error};

#[cfg(feature = "std")]
#[rustfmt::skip]
fn error_to_string<P: Clone + PartialEq>(e: &Context<P, u32>) -> &'static str {
  let v: Vec<(P, ParserKind<u32>)> = error_to_list(e);
  // do it this way if you can use slice patterns
  //match &v[..] {
  //  [ParserKind::Custom(42), ParserKind::Tag]                         => "missing `ijkl` tag",
  //  [ParserKind::Custom(42), ParserKind::Custom(128), ParserKind::Tag] => "missing `mnop` tag after `ijkl`",
  //  _            => "unrecognized error"
  //}

  let collected: Vec<ParserKind<u32>> = v.iter().map(|&(_, ref e)| e.clone()).collect();
  if &collected[..] == [ParserKind::Custom(42), ParserKind::Tag] {
    "missing `ijkl` tag"
  } else if &collected[..] == [ParserKind::Custom(42), ParserKind::Custom(128), ParserKind::Tag] {
    "missing `mnop` tag after `ijkl`"
  } else {
    "unrecognized error"
  }
}

// do it this way if you can use box patterns
//use $crate::lib::std::str;
//fn error_to_string(e:Err) -> String
//  match e {
//    NodePosition(ParserKind::Custom(42), i1, box Position(ParserKind::Tag, i2)) => {
//      format!("missing `ijkl` tag, found '{}' instead", str::from_utf8(i2).unwrap())
//    },
//    NodePosition(ParserKind::Custom(42), i1, box NodePosition(ParserKind::Custom(128), i2,  box Position(ParserKind::Tag, i3))) => {
//      format!("missing `mnop` tag after `ijkl`, found '{}' instead", str::from_utf8(i3).unwrap())
//    },
//    _ => "unrecognized error".to_string()
//  }
//}
*/

#[test]
fn complete() {
  use crate::bytes::complete::tag;
  fn err_test(i: &[u8]) -> ParseResult<&[u8], &[u8]> {
    let (i, _) = tag("ijkl")(i)?;
    tag("mnop")(i)
  }
  let a = &b"ijklmn"[..];

  let res_a = err_test(a);
  assert_eq!(
    res_a,
    Err(Outcome::Failure(error_position!(
      &b"mn"[..],
      ParserKind::Tag
    )))
  );
}

#[test]
fn pair_test() {
  fn pair_abc_def(i: &[u8]) -> ParseResult<&[u8], (&[u8], &[u8])> {
    pair(tag("abc"), tag("def"))(i)
  }

  assert_eq!(
    pair_abc_def(&b"abcdefghijkl"[..]),
    Ok((&b"ghijkl"[..], (&b"abc"[..], &b"def"[..])))
  );
  assert_eq!(
    pair_abc_def(&b"ab"[..]),
    Err(Outcome::Incomplete(Needed::new(1)))
  );
  assert_eq!(
    pair_abc_def(&b"abcd"[..]),
    Err(Outcome::Incomplete(Needed::new(2)))
  );
  assert_eq!(
    pair_abc_def(&b"xxx"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxx"[..],
      ParserKind::Tag
    )))
  );
  assert_eq!(
    pair_abc_def(&b"xxxdef"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxxdef"[..],
      ParserKind::Tag
    )))
  );
  assert_eq!(
    pair_abc_def(&b"abcxxx"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxx"[..],
      ParserKind::Tag
    )))
  );
}

#[test]
fn separated_pair_test() {
  fn sep_pair_abc_def(i: &[u8]) -> ParseResult<&[u8], (&[u8], &[u8])> {
    separated_pair(tag("abc"), tag(","), tag("def"))(i)
  }

  assert_eq!(
    sep_pair_abc_def(&b"abc,defghijkl"[..]),
    Ok((&b"ghijkl"[..], (&b"abc"[..], &b"def"[..])))
  );
  assert_eq!(
    sep_pair_abc_def(&b"ab"[..]),
    Err(Outcome::Incomplete(Needed::new(1)))
  );
  assert_eq!(
    sep_pair_abc_def(&b"abc,d"[..]),
    Err(Outcome::Incomplete(Needed::new(2)))
  );
  assert_eq!(
    sep_pair_abc_def(&b"xxx"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxx"[..],
      ParserKind::Tag
    )))
  );
  assert_eq!(
    sep_pair_abc_def(&b"xxx,def"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxx,def"[..],
      ParserKind::Tag
    )))
  );
  assert_eq!(
    sep_pair_abc_def(&b"abc,xxx"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxx"[..],
      ParserKind::Tag
    )))
  );
}

#[test]
fn preceded_test() {
  fn preceded_abcd_efgh(i: &[u8]) -> ParseResult<&[u8], &[u8]> {
    preceded(tag("abcd"), tag("efgh"))(i)
  }

  assert_eq!(
    preceded_abcd_efgh(&b"abcdefghijkl"[..]),
    Ok((&b"ijkl"[..], &b"efgh"[..]))
  );
  assert_eq!(
    preceded_abcd_efgh(&b"ab"[..]),
    Err(Outcome::Incomplete(Needed::new(2)))
  );
  assert_eq!(
    preceded_abcd_efgh(&b"abcde"[..]),
    Err(Outcome::Incomplete(Needed::new(3)))
  );
  assert_eq!(
    preceded_abcd_efgh(&b"xxx"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxx"[..],
      ParserKind::Tag
    )))
  );
  assert_eq!(
    preceded_abcd_efgh(&b"xxxxdef"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxxxdef"[..],
      ParserKind::Tag
    )))
  );
  assert_eq!(
    preceded_abcd_efgh(&b"abcdxxx"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxx"[..],
      ParserKind::Tag
    )))
  );
}

#[test]
fn terminated_test() {
  fn terminated_abcd_efgh(i: &[u8]) -> ParseResult<&[u8], &[u8]> {
    terminated(tag("abcd"), tag("efgh"))(i)
  }

  assert_eq!(
    terminated_abcd_efgh(&b"abcdefghijkl"[..]),
    Ok((&b"ijkl"[..], &b"abcd"[..]))
  );
  assert_eq!(
    terminated_abcd_efgh(&b"ab"[..]),
    Err(Outcome::Incomplete(Needed::new(2)))
  );
  assert_eq!(
    terminated_abcd_efgh(&b"abcde"[..]),
    Err(Outcome::Incomplete(Needed::new(3)))
  );
  assert_eq!(
    terminated_abcd_efgh(&b"xxx"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxx"[..],
      ParserKind::Tag
    )))
  );
  assert_eq!(
    terminated_abcd_efgh(&b"xxxxdef"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxxxdef"[..],
      ParserKind::Tag
    )))
  );
  assert_eq!(
    terminated_abcd_efgh(&b"abcdxxxx"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxxx"[..],
      ParserKind::Tag
    )))
  );
}

#[test]
fn delimited_test() {
  fn delimited_abc_def_ghi(i: &[u8]) -> ParseResult<&[u8], &[u8]> {
    delimited(tag("abc"), tag("def"), tag("ghi"))(i)
  }

  assert_eq!(
    delimited_abc_def_ghi(&b"abcdefghijkl"[..]),
    Ok((&b"jkl"[..], &b"def"[..]))
  );
  assert_eq!(
    delimited_abc_def_ghi(&b"ab"[..]),
    Err(Outcome::Incomplete(Needed::new(1)))
  );
  assert_eq!(
    delimited_abc_def_ghi(&b"abcde"[..]),
    Err(Outcome::Incomplete(Needed::new(1)))
  );
  assert_eq!(
    delimited_abc_def_ghi(&b"abcdefgh"[..]),
    Err(Outcome::Incomplete(Needed::new(1)))
  );
  assert_eq!(
    delimited_abc_def_ghi(&b"xxx"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxx"[..],
      ParserKind::Tag
    )))
  );
  assert_eq!(
    delimited_abc_def_ghi(&b"xxxdefghi"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxxdefghi"[..],
      ParserKind::Tag
    ),))
  );
  assert_eq!(
    delimited_abc_def_ghi(&b"abcxxxghi"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxxghi"[..],
      ParserKind::Tag
    )))
  );
  assert_eq!(
    delimited_abc_def_ghi(&b"abcdefxxx"[..]),
    Err(Outcome::Failure(error_position!(
      &b"xxx"[..],
      ParserKind::Tag
    )))
  );
}

#[test]
fn tuple_test() {
  fn tuple_3(i: &[u8]) -> ParseResult<&[u8], (u16, &[u8], &[u8])> {
    tuple((be_u16, take(3u8), tag("fg")))(i)
  }

  assert_eq!(
    tuple_3(&b"abcdefgh"[..]),
    Ok((&b"h"[..], (0x6162u16, &b"cde"[..], &b"fg"[..])))
  );
  assert_eq!(
    tuple_3(&b"abcd"[..]),
    Err(Outcome::Incomplete(Needed::new(1)))
  );
  assert_eq!(
    tuple_3(&b"abcde"[..]),
    Err(Outcome::Incomplete(Needed::new(2)))
  );
  assert_eq!(
    tuple_3(&b"abcdejk"[..]),
    Err(Outcome::Failure(error_position!(
      &b"jk"[..],
      ParserKind::Tag
    )))
  );
}
