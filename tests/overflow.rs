#[macro_use]
extern crate nom;

use nom::{IResult,Needed,be_u8,be_u64};

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
named!(parser02<&[u8],(&[u8],&[u8])>,
    tuple!(take!(1),take!(18446744073709551615))
);

#[test]
fn overflow_incomplete_do_parse() {
  assert_eq!(parser01(&b"3"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_tuple() {
  assert_eq!(parser02(&b"3"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_length_bytes() {
 named!(multi<&[u8], Vec<&[u8]> >, many0!( length_bytes!(be_u64) ) );

 // Trigger an overflow in length_bytes
 assert_eq!(multi(&b"\x00\x00\x00\x00\x00\x00\x00\x01\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xaa"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_many0() {
 named!(multi<&[u8], Vec<&[u8]> >, many0!( length_bytes!(be_u64) ) );

 // Trigger an overflow in many0
 assert_eq!(multi(&b"\x00\x00\x00\x00\x00\x00\x00\x01\xaa\xff\xff\xff\xff\xff\xff\xff\xef\xaa"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
#[cfg(feature = "std")]
fn overflow_incomplete_many1() {
 named!(multi<&[u8], Vec<&[u8]> >, many1!( length_bytes!(be_u64) ) );

 // Trigger an overflow in many1
 assert_eq!(multi(&b"\x00\x00\x00\x00\x00\x00\x00\x01\xaa\xff\xff\xff\xff\xff\xff\xff\xef\xaa"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_many_till() {
 named!(multi<&[u8], (Vec<&[u8]>, &[u8]) >, many_till!( length_bytes!(be_u64), tag!("abc") ) );

 // Trigger an overflow in many_till
 assert_eq!(multi(&b"\x00\x00\x00\x00\x00\x00\x00\x01\xaa\xff\xff\xff\xff\xff\xff\xff\xef\xaa"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_many_m_n() {
 named!(multi<&[u8], Vec<&[u8]> >, many_m_n!(2, 4, length_bytes!(be_u64) ) );

 // Trigger an overflow in many_m_n
 assert_eq!(multi(&b"\x00\x00\x00\x00\x00\x00\x00\x01\xaa\xff\xff\xff\xff\xff\xff\xff\xef\xaa"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_count() {
 named!(counter<&[u8], Vec<&[u8]> >, count!( length_bytes!(be_u64), 2 ) );

 assert_eq!(counter(&b"\x00\x00\x00\x00\x00\x00\x00\x01\xaa\xff\xff\xff\xff\xff\xff\xff\xef\xaa"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_count_fixed() {
 named!(counter< [&[u8]; 2] >, count_fixed!( &[u8], length_bytes!(be_u64), 2 ) );

 assert_eq!(counter(&b"\x00\x00\x00\x00\x00\x00\x00\x01\xaa\xff\xff\xff\xff\xff\xff\xff\xef\xaa"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_length_count() {
 named!(multi<&[u8], Vec<&[u8]> >, length_count!( be_u8, length_bytes!(be_u64) ) );

 assert_eq!(multi(&b"\x04\x00\x00\x00\x00\x00\x00\x00\x01\xaa\xff\xff\xff\xff\xff\xff\xff\xee\xaa"[..]), IResult::Incomplete(Needed::Unknown));
}

#[test]
fn overflow_incomplete_length_data() {
 named!(multi<&[u8], Vec<&[u8]> >, many0!( length_data!(be_u64) ) );

 assert_eq!(multi(&b"\x00\x00\x00\x00\x00\x00\x00\x01\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xaa"[..]), IResult::Incomplete(Needed::Unknown));
}
