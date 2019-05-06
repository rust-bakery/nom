#[macro_use]
extern crate nom;

use nom::IResult;
use nom::bytes::complete::tag;

fn main() {
  let mut data = "abcabcabcabc";

  fn parser(i: &str) -> IResult<&str, &str> {
    tag("abc")(i)
  }

  let mut it = std::iter::from_fn(move|| {
    match parser(data) {
      Ok((i, o)) => {
        data = i;
        Some(o)
      },
      _ => None
    }
  });

  for value in it {
    println!("parser returned: {}", value);
  }
}
