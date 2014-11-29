#![feature(globs,macro_rules)]
use nom::{Producer, FileProducer, Mapper, IResult, print};
use nom::IResult::*;
use nom::ProducerState::*;

mod nom;

fn main() {
  println!("Hello world!");

  fn pr<'a>(res: IResult<(),&'a[u8]>) -> IResult<&'a[u8], ()> {
    //par.m2(print)
    Error(0)
  }

  FileProducer::new("links.txt", 1024).map(|producer: FileProducer| {
    let mut p = producer;
    //p.push(|par| par.map(accline).mapf(|v2: &[u8]| str::from_utf8(v2.as_slice())).map(print));
    /*p.push(|res| {
      //let p2:IResult<&[u8],&str> = res.mapf(|v2: &[u8]| str::from_utf8(v2.as_slice()));
      Done((), ())
    });*/
    fn pr2(par: IResult<(),&[u8]>) -> IResult<&[u8],()> {
      par.flat_map(print)
    }
    pusher!(ps, pr)
    ps(&mut p);
    //p.push(|res| { res.flat_map(print) });
    //p.push(|par| {println!("par: {}", par); par});
    //p.push(pr);
    //p.push(|par| { par.map(tag!("https://".as_bytes())).map(print) });
  });

}
