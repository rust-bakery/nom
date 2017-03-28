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

// We request a length that would trigger an overflow if computing consumed + requested
named!(parser02<&[u8],()>,
    chain!(
        hdr: take!(1) ~
        data: take!(18446744073709551615),
        || ()
    )
);

// We request a length that would trigger an overflow if computing consumed + requested
named!(parser03<&[u8],(&[u8],&[u8])>,
    tuple!(take!(1),take!(18446744073709551615))
);

#[test]
fn overflow_incomplete_test01() {
  assert_eq!(parser01(&b"3"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_test02() {
  assert_eq!(parser02(&b"3"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_test03() {
  assert_eq!(parser03(&b"3"[..]), IResult::Incomplete(Needed::Unknown));
}

