#![feature(macro_rules)]
use nom::{Error, FileProducer, Mapper, Ender, Parser, print, accline, Done};
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
    ()
  });

  let v1 = vec![1, 2, 3];
  let v2 = vec![4, 5, 6];
  //let d: Parser<(), &[u8]> = Done((), v.as_slice());
  let d = Done(v1.as_slice(), v2.as_slice());
  d.map(print);
  d.end(|s:&[u8]| { println!("str: {}", s); ()})
}
