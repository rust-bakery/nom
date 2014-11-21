#![feature(globs,macro_rules)]
use nom::{Producer, FileProducer, Mapper, Ender, Parser, print, accline};
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
    //p.push(|par| par.m3(accline).mapf(|v2: &[u8]| str::from_utf8(v2.as_slice())).map(print));
    p.push(|par| {
      //let p2:Parser<&[u8],&str> = par.mapf(|v2: &[u8]| str::from_utf8(v2.as_slice()));
      //p2.m4(print)
      //p2.m4(|s:&str| {println!("str: {}", s); Done(s, ())})
      //p2.end(|s:&str| { println!("str: {}", s); ()});Done((),())
      Done((), ())
    });
    p.push(|par| { par.m2(print) });
    p.push(|par| { par.map(print) });
    p.push(|par| {println!("par: {}", par); par});
    //p.push(pr);
  });

}
