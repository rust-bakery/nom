#[macro_use]
extern crate nom;

use nom::{IResult,Needed};

// Parser definition

// We request a length that would trigger an overflow if computing consumed + requested
named!(parser01<&[u8],()>,
    do_parse!(
        hdr: take!(1) >>
        data: take!(18446744073709551615) >>
        ( () )
    )
);

#[test]
fn overflow_incomplete_test() {
  assert_eq!(parser01(&b"3"[..]), IResult::Incomplete(Needed::Unknown));
}

