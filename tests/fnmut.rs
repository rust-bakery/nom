extern crate nom;

use nom::{
  bytes::complete::tag,
  error::ErrorKind,
  multi::{many0, many0_count},
  number::streaming::le_u64,
  Err, IResult, Needed, Parser,
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

#[test]
fn accumulate() {
  let mut v = Vec::new();

  let (i, count) = {
    let mut parser = many0_count::<_, _, (), _>(|i| {
      let (i, o) = tag("abc")(i)?;
      v.push(o);
      Ok((i, ()))
    });
    parser("abcabcabcabc").unwrap()
  };

  println!("v: {:?}", v);
  assert_eq!(v.len(), 4);
}
