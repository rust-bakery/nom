//#![feature(trace_macros)]
#![allow(dead_code)]

#[macro_use]
extern crate nom;

use nom::{IResult,Needed,space,be_u16,le_u64};

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
        do_parse!(
            start: take_char >>
            tag!("-")        >>
            end: take_char   >>
            (Range {
                start: start,
                end:   end,
            })
        ) |
        map!(
            take_char,
            |c| {
                Range {
                    start: c,
                    end:   c,
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

#[cfg(feature = "std")]
mod parse_int {
  use nom::HexDisplay;
  use nom::{IResult,space,digit};
  use std::str;

  named!(parse_ints< Vec<i32> >, many0!(spaces_or_int));

  fn spaces_or_int(input: &[u8]) -> IResult<&[u8], i32>{
    println!("{}", input.to_hex(8));
    do_parse!(input,
      opt!(complete!(space)) >>
      res: map!(complete!(digit),
      |x| {
        println!("x: {:?}", x);
        let result = str::from_utf8(x).unwrap();
        println!("Result: {}", result);
        println!("int is empty?: {}", x.is_empty());
        match result.parse(){
          Ok(i) => i,
          Err(_) =>  panic!("UH OH! NOT A DIGIT!")
        }
      }) >>
      (res)
    )
  }

  #[test]
  fn issue_142(){
     let subject = parse_ints(&b"12 34 5689"[..]);
     let expected = IResult::Done(&b""[..], vec![12, 34, 5689]);
     assert_eq!(subject, expected);

     let subject = parse_ints(&b"12 34 5689 "[..]);
     let expected = IResult::Done(&b" "[..], vec![12, 34, 5689]);
     assert_eq!(subject, expected)
  }
}

#[test]
fn usize_length_bytes_issue(){
  length_bytes!(b"012346", be_u16);
}

/*
 DOES NOT COMPILE
#[test]
fn issue_152() {
  named!(take4, take!(4));
  named!(xyz, tag!("XYZ"));
  named!(abc, tag!("abc"));


  named!(sw,
    switch!(take4,
      b"abcd" => xyz |
      b"efgh" => abc
    )
  );
}
*/

#[test]
fn take_till_issue() {
    named!(nothing,
        take_till!(call!(|_| true))
    );

    assert_eq!(nothing(b""), IResult::Done(&b""[..], &b""[..]));
    assert_eq!(nothing(b"abc"), IResult::Done(&b"abc"[..], &b""[..]));
}

named!(issue_498< Vec<&[u8]> >, separated_nonempty_list!( opt!(space), tag!("abcd") ));

named!(issue_308(&str) -> bool,
    do_parse! (
        tag_s! ("foo") >>
        b: alt_complete! (
            map! (tag_s! ("1"), |_: &str|->bool {true}) |
            value! (false)
        ) >>
        (b) ));


fn issue_302(input: &[u8]) -> IResult<&[u8], Option<Vec<u64>> > {
    do_parse!(input,
        entries: cond!(true, count!(le_u64, 3)) >>
        ( entries )
    )
}
