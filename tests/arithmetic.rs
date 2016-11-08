#[macro_use]
extern crate nom;

use nom::{IResult,digit};

use std::str;
use std::str::FromStr;

named!(parens<i64>, ws!(delimited!( tag!("("), expr, tag!(")") )) );

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

fn term_1(i: &[u8], acc: i64) -> IResult<&[u8], i64> {
    alt!(i,
        map!(preceded!(tag!("*"), factor), |mul| acc * mul) |
        map!(preceded!(tag!("/"), factor), |div| acc / div)
    )
}

fn term_0(i: &[u8], ini: i64) -> IResult<&[u8], i64> {
    let mut acc   = ini;
    let mut input = i;
    while let IResult::Done(i, res) = term_1(input, acc) {
        input = i;
        acc   = res;
    }
    IResult::Done(input, acc)
}

named!(term <i64>, do_parse!(
    ini: factor              >>
    res: apply!(term_0, ini) >>
    (res)
));

fn expr_1(i: &[u8], acc: i64) -> IResult<&[u8], i64> {
    alt!(i,
        map!(preceded!(tag!("+"), term), |add| acc + add) |
        map!(preceded!(tag!("-"), term), |sub| acc - sub)
    )
}

fn expr_0(i: &[u8], ini: i64) -> IResult<&[u8], i64> {
    let mut acc   = ini;
    let mut input = i;
    while let IResult::Done(i, res) = expr_1(input, acc) {
        input = i;
        acc   = res;
    }
    IResult::Done(input, acc)
}

named!(expr <i64>, do_parse!(
    ini: term                >>
    res: apply!(expr_0, ini) >>
    (res)
));

#[test]
fn factor_test() {
  assert_eq!(factor(&b"3"[..]), IResult::Done(&b""[..], 3));
  assert_eq!(factor(&b" 12"[..]), IResult::Done(&b""[..], 12));
  assert_eq!(factor(&b"537  "[..]), IResult::Done(&b""[..], 537));
  assert_eq!(factor(&b"  24   "[..]), IResult::Done(&b""[..], 24));
}


#[test]
fn term_test() {
  assert_eq!(term(&b" 12 *2 /  3"[..]), IResult::Done(&b""[..], 8));
  assert_eq!(term(&b" 2* 3  *2 *2 /  3"[..]), IResult::Done(&b""[..], 8));
  assert_eq!(term(&b" 48 /  3/2"[..]), IResult::Done(&b""[..], 8));
}

#[test]
fn expr_test() {
  assert_eq!(expr(&b" 1 +  2 "[..]), IResult::Done(&b""[..], 3));
  assert_eq!(expr(&b" 12 + 6 - 4+  3"[..]), IResult::Done(&b""[..], 17));
  assert_eq!(expr(&b" 1 + 2*3 + 4"[..]), IResult::Done(&b""[..], 11));
}

#[test]
fn parens_test() {
  assert_eq!(expr(&b" (  2 )"[..]), IResult::Done(&b""[..], 2));
  assert_eq!(expr(&b" 2* (  3 + 4 ) "[..]), IResult::Done(&b""[..], 14));
  assert_eq!(expr(&b"  2*2 / ( 5 - 1) + 3"[..]), IResult::Done(&b""[..], 4));
}
