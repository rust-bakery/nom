#![feature(globs,macro_rules)]
use nom::{FileProducer, Mapper, Parser, print};
use nom::Parser::*;
use std::str;

mod nom;

fn main() {
  println!("Hello world!");

  fn pr(par: Parser<(),&[u8]>) -> Parser<&[u8], ()> {
    //par.m2(print)
    Error(0)
  }

  FileProducer::new("links.txt", 1024).map(|producer: FileProducer| {
    let mut p = producer;
    //p.push(|par| par.map(accline).mapf(|v2: &[u8]| str::from_utf8(v2.as_slice())).map(print));
    /*p.push(|par| {
      //let p2:Parser<&[u8],&str> = par.mapf(|v2: &[u8]| str::from_utf8(v2.as_slice()));
      Done((), ())
    });*/
    p.push(|par| { par.flat_map(print) });
    //p.push(|par| {println!("par: {}", par); par});
    //p.push(pr);
    //p.push(|par| { par.map(tag!("https://".as_bytes())).map(print) });
  });

}
