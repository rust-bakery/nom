use std::collections::HashMap;
use std::iter::Iterator;

use nom::bytes::complete::tag;
use nom::character::complete::alphanumeric1;
use nom::combinator::iterator;
use nom::sequence::{separated_pair, terminated};
use nom::IResult;

fn main() {
  let mut data = "abcabcabcabc";

  fn parser(i: &str) -> IResult<&str, &str> {
    tag("abc")(i)
  }

  // `from_fn` (available from Rust 1.34) can create an iterator
  // from a closure
  let it = std::iter::from_fn(move || {
    match parser(data) {
      // when successful, a nom parser returns a tuple of
      // the remaining input and the output value.
      // So we replace the captured input data with the
      // remaining input, to be parsed on the next call
      Ok((i, o)) => {
        data = i;
        Some(o)
      }
      _ => None,
    }
  });

  for value in it {
    println!("parser returned: {}", value);
  }

  println!("\n********************\n");

  let data = "abcabcabcabc";

  // if `from_fn` is not available, it is possible to fold
  // over an iterator of functions
  let res =
    std::iter::repeat(parser)
      .take(3)
      .try_fold((data, Vec::new()), |(data, mut acc), parser| {
        parser(data).map(|(i, o)| {
          acc.push(o);
          (i, acc)
        })
      });

  // will print "parser iterator returned: Ok(("abc", ["abc", "abc", "abc"]))"
  println!("\nparser iterator returned: {:?}", res);

  println!("\n********************\n");

  let data = "key1:value1,key2:value2,key3:value3,;";

  // `nom::combinator::iterator` will return an iterator
  // producing the parsed values. Compared to the previous
  // solutions:
  // - we can work with a normal iterator like `from_fn`
  // - we can get the remaining input afterwards, like with the `try_fold` trick
  let mut nom_it = iterator(
    data,
    terminated(
      separated_pair(alphanumeric1, tag(":"), alphanumeric1),
      tag(","),
    ),
  );

  let res = nom_it
    .map(|(k, v)| (k.to_uppercase(), v))
    .collect::<HashMap<_, _>>();

  let parser_result: IResult<_, _> = nom_it.finish();
  let (remaining_input, ()) = parser_result.unwrap();

  // will print "iterator returned {"key1": "value1", "key3": "value3", "key2": "value2"}, remaining input is ';'"
  println!(
    "iterator returned {:?}, remaining input is '{}'",
    res, remaining_input
  );
}
