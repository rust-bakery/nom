extern crate nom;

use nom::IResult;
use nom::bytes::complete::tag;
use nom::sequence::{separated_pair, terminated};
use nom::character::complete::alphanumeric1;
use nom::combinator::iterator;
use std::iter::Iterator;
use std::collections::HashMap;

fn main() {
  let mut data = "abcabcabcabc";
  let data2 = data.clone();

  fn parser(i: &str) -> IResult<&str, &str> {
    tag("abc")(i)
  }

  let it = std::iter::from_fn(move|| {
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

  println!("\n********************\n");

  println!("data is now: {:?}", data2);

  let data = "abcabcabcabc";
  let res = std::iter::repeat(parser).take(3).try_fold((data, Vec::new()), |(data, mut acc), parser| {
    parser(data).map(|(i, o)| {
      acc.push(o);
      (i, acc)
    })
  });

  // will print "parser iterator returned: Ok(("abc", ["abc", "abc", "abc"]))"
  println!("\nparser iterator returned: {:?}", res);

  println!("\n********************\n");

  let data = "key1:value1,key2:value2,key3:value3,;";

  let mut nom_it = iterator(data, terminated(separated_pair(alphanumeric1, tag(":"), alphanumeric1), tag(",")));

  let res = nom_it.map(|(k, v)| (k.to_uppercase(), v)).collect::<HashMap<_, _>>();

  let parser_result: IResult<_, _> = nom_it.finish();
  let (remaining_input, ()) = parser_result.unwrap();

  // will print "iterator returned {"key1": "value1", "key3": "value3", "key2": "value2"}, remaining input is ';'"
  println!("iterator returned {:?}, remaining input is '{}'", res, remaining_input);
}
