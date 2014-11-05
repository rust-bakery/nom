#![feature(macro_rules)]
use nom::{feed, parse, FileProducer, print, Error, Done, Incomplete};
use std::str;

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
  let v2 = "abc";
  print(&v2);

  FileProducer::new("links.txt", 1024).map(|producer| {
    let mut p = producer;
    loop {
      match p.produce() {
        Error(_, e)   => {
          println!("error: {}", e);
          break;
        },
        Done(i, o)    => println!("done: {}, rest: {}", str::from_utf8(o.as_slice()), i),
        Incomplete(f) => {
          println!("incomplete");
        }
      }
    }
  });

}
