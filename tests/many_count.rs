#[macro_use]
extern crate nom;

use nom::digit;
use nom::types::CompleteStr;

named!(
    count0_digits(CompleteStr) -> usize,
    many0_count!(pair!(digit, tag!(",")))
);

#[test]
fn many0_count_test() {
  assert_eq!(count0_digits(CompleteStr("123,")), Ok((CompleteStr(""), 1)));
  assert_eq!(count0_digits(CompleteStr("123,45,")), Ok((CompleteStr(""), 2)));
  assert_eq!(count0_digits(CompleteStr("1,2,3,4,5,6,7,8,9,0,")), Ok((CompleteStr(""), 10)));
  assert_eq!(count0_digits(CompleteStr("hello")), Ok((CompleteStr("hello"), 0)));
}

named!(
    count1_digits(CompleteStr) -> usize,
    many1_count!(pair!(digit, tag!(",")))
);

#[test]
fn many1_count_test() {
  assert_eq!(count1_digits(CompleteStr("123,")), Ok((CompleteStr(""), 1)));
  assert_eq!(count1_digits(CompleteStr("123,45,")), Ok((CompleteStr(""), 2)));
  assert_eq!(count1_digits(CompleteStr("1,2,3,4,5,6,7,8,9,0,")), Ok((CompleteStr(""), 10)));
  assert_eq!(
    count1_digits(CompleteStr("hello")),
    Err(nom::Err::Error(nom::simple_errors::Context::Code(
      CompleteStr("hello"),
      nom::ErrorKind::Many1Count
    )))
  );
}
