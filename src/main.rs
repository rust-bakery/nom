#![feature(macro_rules)]
#![feature(unboxed_closures)]
use nom::{FileProducer, Parser, begin, print, Error, accline, Done, parse};
use std::str;

mod nom;

fn main() {
  println!("Hello world!");
  let v = vec![3, 2, 1];
  match parse(v.as_slice()) {
    Error(e)   => println!("error: {}", e),
    Done(i, o)    => println!("done: {}, rest: {}", o, i),
    //Incomplete(_) => println!("incomplete")
  }
  //feed();
  let v2 = "abc";
  print(&v2);

  FileProducer::new("links.txt", 1024).map(|producer: FileProducer| {
    let mut p = producer;
    p.push(|par| par.mapf(|v2| str::from_utf8(v2.as_slice())).map(print));
    ()
  });

}
