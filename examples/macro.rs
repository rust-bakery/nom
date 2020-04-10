#[macro_use]
extern crate nom;

use nom::{character::complete::digit0, number::complete::be_u32};


named!(first<u32>, flat_map!(digit0, parse_to!(u32)));
named!(second<u32>, call!(be_u32));

named!(parser<u32>, alt!(first | second));

fn main() {
  let data = b"1234;";

  let res = parser(&data[..]);
  println!("res: {:?}", res);
}
