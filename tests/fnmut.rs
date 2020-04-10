extern crate nom;

use nom::{
  error::ErrorKind,
  number::streaming::le_u64,
  multi::many0,
  bytes::complete::tag,
  Err, IResult, Needed,
};

#[test]
fn parse() {
  let mut counter = 0;

  let res = {
      let mut parser = many0::<_, _, (), _>(|i| {
          counter += 1;
          tag("abc")(i)
      });

      parser("abcabcabcabc").unwrap()
  };

  println!("res: {:?}", res);
  assert_eq!(counter, 5);
}
