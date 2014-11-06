#![feature(unboxed_closures)]
#![desc = "Omnomnom incremental byte parser"]
#![license = "MIT"]

extern crate collections;


use std::fmt::Show;
use std::io;
use std::io::fs::File;
use std::io::IoResult;

type Err = uint;
type ParserClosure<'a,I,O> = |I|:'a -> Parser<'a,I,O>;
//type ParserClosure<'a,I,O> = Fn<I, Parser<'a,I,O>>;
pub enum Parser<'a,I,O> {
  Done(I,O),
  Error(Err),
  Incomplete(ParserClosure<'a,I,O>)
  //Incomplete(|I|:'a -> Parser<'a,I,O>)
  //Incomplete(fn(I) -> Parser<'a,I,O>)
}

impl<'a,I,O> Parser<'a,I,O> {
  pub fn map<'a,N>(&'a self, f: ParserClosure<'a,&'a O, N>) -> Parser<'a, &'a O, N> {
    match(self) {
      &Error(ref e) => Error(*e),
      &Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(o)
    }
  }

  pub fn mapf<'a,N>(&'a self, f: |&'a O|:'a -> Option<N>) -> Parser<'a, &'a O, N> {
    match(self) {
      &Error(ref e) => Error(*e),
      &Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, ref o) => match f(o) {
        Some(output) => Done(o, output),
        None         => Error(0)
      }
    }
  }

  pub fn then<'a,N>(&'a self, f: ParserClosure<'a,&'a I,N>) -> Parser<'a, &'a I, N> {
    match(self) {
      &Error(ref e) => Error(*e),
      &Incomplete(ref cl) => Incomplete(f),
      &Done(ref i, _) => f(i)
    }

  }
}
/*
pub fn parse<'a,I,O>(input: I) -> Option<O> {

}
*/
/*pub fn parseString(input: String) -> Option<int> {
  parse(vec![0]) match {
    
  }
}*/


pub fn feed() -> () {
  let v = vec![1, 2, 3, 4, 5];
  let mut acc = v.slice(0, 1);
  let mut idx = 0;
  let mut parser = Incomplete(parse);
  loop {
    match parser {
      Error(e) => {
        println!("error: {}", e);
        break;
      },
      Done(i, o)  => {
        println!("done: {}, rest: {}", o, i);
        break;
      },
      Incomplete(f) => {
        idx = idx + 1;
        println!("incomplete");
        parser = f(v.slice(0, idx));
      }
    }
  }
}

pub fn parse<'a>(input: &'a [u8]) -> Parser<'a, &'a [u8], &'a [u8]> {

  match input.len() {
    0 => Error(0),
    1 => Incomplete(parse),
    _ => Done(input.slice_from(2), input.slice(0,2))
  }
}

pub fn accline<'a>(input: &'a [u8]) -> Parser<'a, &'a [u8], &'a [u8]> {
  match input.iter().position(|&c| c == '\n' as u8) {
    None      => Incomplete(accline),
    Some(pos) => Done(input.slice_from(pos), input.slice(0, pos))
  }
}

pub fn print<'a, T: Show>(input: &'a T) -> Parser<'a, &'a T, ()> {
  println!("{}", input);
  Done(input, ())
}

pub struct FileProducer {
  size: uint,
  file: File
}

impl FileProducer {
  pub fn new(filename: &str, buffer_size: uint) -> IoResult<FileProducer> {
    File::open(&Path::new(filename)).map(|f| { FileProducer {size: buffer_size, file: f} })
  }

  pub fn produce<'a>(&mut self) -> Parser<'a, (), Vec<u8>> {
    let mut v = Vec::with_capacity(self.size);
    match self.file.push(self.size, &mut v) {
      Err(e) => match e.kind {
        /*EndOfFile => {
          Done((), v)
        },
        NoProgress => {
          Done((), v)
        },*/
        _ => Error(0)
      },
      Ok(i)  => {
        println!("read {} bytes", i);
        Done((), v)
      }
    }
  }
}

