#![feature(trace_macros)]
#[macro_use]
extern crate nom;

use nom::{IResult,Needed};

#[allow(dead_code)]
struct Range {
  start: char,
  end:   char
}

pub fn take_char(input: &[u8]) -> IResult<&[u8], char> {
  if input.len() > 0 {
    IResult::Done(&input[1..], input[0] as char)
  } else {
    IResult::Incomplete(Needed::Size(1))
  }
}

//trace_macros!(true);

#[allow(dead_code)]
named!(range<&[u8], Range>,
    alt!(
        chain!(
            start: take_char ~
            tag!("-") ~
            end: take_char,
            || {
                Range {
                    start: start,
                    end: end,
                }
            }
        ) |
        map!(
            take_char,
            |c| {
                Range {
                    start: c,
                    end: c,
                }
            }
        )
    )
);


#[allow(dead_code)]
named!(literal<&[u8], Vec<char> >,
    map!(
        many1!(take_char),
        |cs| {
          cs
        }
    )
);

#[test]
fn issue_58() {
  range(&b"abcd"[..]);
  literal(&b"abcd"[..]);
}

//trace_macros!(false);
