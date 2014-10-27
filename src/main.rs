#![feature(macro_rules)]
use nom::{feed, parse, Error, Done, Incomplete};

mod nom;

fn main() {
  println!("Hello world!");
  let v = vec![3, 2, 1];
  match parse(v.as_slice()) {
    Error(_, e)   => println!("error: {}", e),
    Done(i, o)    => println!("done: {}, rest: {}", o, i),
    Incomplete(_) => println!("incomplete")
  }

  feed();
}
