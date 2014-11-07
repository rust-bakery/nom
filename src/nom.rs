#![feature(unboxed_closures)]
#![desc = "Omnomnom incremental byte parser"]
#![license = "MIT"]

extern crate collections;


use std::fmt::Show;
use std::io;
use std::io::fs::File;
use std::io::{IoError, IoResult, IoErrorKind};

type Err = uint;
type ParserClosure<'a, I,O> = |I|:'a -> Parser<I,O>;

//type ParserClosure<'a,I,O> = |I|:'a -> Parser<'a,I,O>;
//type ParserClosure<'a,I,O> = Fn<I, Parser<'a,I,O>>;
pub enum Parser<I,O> {
  Done(I,O),
  Error(Err),
  //Incomplete(ParserClosure<'a,I,O>)
  //Incomplete(|I|:'a -> Parser<'a,I,O>)
  //Incomplete(fn(I) -> Parser<'a,I,O>)
}

impl<'a,I,O> Parser<I,O> {
  //this is flatmap
  pub fn map<'a,N>(&'a self, f: ParserClosure<&'a O, N>) -> Parser<&'a O, N> {
    match(self) {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(o)
    }
  }

  pub fn mapf<'a,N>(&'a self, f: |&'a O|:'a -> Option<N>) -> Parser<&'a O, N> {
    match(self) {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, ref o) => match f(o) {
        Some(output) => Done(o, output),
        None         => Error(0)
      }
    }
  }

  pub fn then<'a,N>(&'a self, f: ParserClosure<&'a I,N>) -> Parser<&'a I, N> {
    match(self) {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Incomplete(f),
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

/*
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
*/
pub fn parse<'a>(input: &'a [u8]) -> Parser<&'a [u8], &'a [u8]> {

  match input.len() {
    0 => Error(0),
    //1 => Incomplete(parse),
    _ => Done(input.slice_from(2), input.slice(0,2))
  }
}

pub fn accline<'a>(input: &'a [u8]) -> Parser<&'a [u8], &'a [u8]> {
  match input.iter().position(|&c| c == '\n' as u8) {
    None      => Error(0),//Incomplete(accline),
    Some(pos) => Done(input.slice_from(pos), input.slice(0, pos))
  }
}

pub fn print<'a, T: Show>(input: &'a T) -> Parser<&'a T, ()> {
  println!("{}", input);
  Done(input, ())
}


pub struct FileProducer {
  size: uint,
  file: File
}

pub enum ProducerState<O> {
  Eof(O),
  Continue,
  Data(O),
  ProducerError(Err),
}

pub fn begin<'a>(input: &'a [u8]) -> Parser<(), &'a [u8]> {
  Done((), input)
}

type ParserStarterClosure<'a,I,T,O> = |Parser<(),I>|:'a -> Parser<T,O>;

impl FileProducer {
  pub fn new(filename: &str, buffer_size: uint) -> IoResult<FileProducer> {
    File::open(&Path::new(filename)).map(|f| { FileProducer {size: buffer_size, file: f} })
  }

  pub fn produce(&mut self) -> ProducerState<Vec<u8>> {
    let mut v = Vec::with_capacity(self.size);
    match self.file.push(self.size, &mut v) {
      Err(e) => {
        match e.kind {
          IoErrorKind::NoProgress => Continue,
          IoErrorKind::EndOfFile  => Eof(v),
          _          => ProducerError(0)
        }
      },
      Ok(i)  => {
        println!("read {} bytes", i);
        Data(v)
      }
    }
  }

  //pub fn push<'a,'b,'c,T,O>(&'a mut self, f: |Parser<(),&'a[u8]>|:'c -> Parser<T,O>) { //ParserStarterClosure<'b, &'c[u8], T, O>) {
  pub fn push<T,O>(&mut self, f: |Parser<(),&[u8]>| -> Parser<T,O>) { //ParserStarterClosure<'b, &'c[u8], T, O>) {
    let mut v2 = Vec::new();
    loop {
      if self.file.eof() {
        println!("end");
        break;
      }
      let state = self.produce();
      let mut acc: Vec<u8> = Vec::new();
      match state {
        ProducerError(e)  => println!("error: {}", e),
        Continue => {},
        Data(v) => {
          v2.push_all(acc.as_slice());
          v2.push_all(v.as_slice());
          //acc.push_all(v.as_slice());
          //let r: &'a[u8] = acc.as_slice();
          //let data = if acc.len() == 0 { v } else { acc.push_all(v.as_slice()); acc };
          let p = Done((), v2.as_slice());
          match f(p) {
          //match f(begin(v2.as_slice())) {
            Error(e)      => println!("error, stopping: {}", e),
            //Incomplete(_) => println!("incomplete, continue"),
            Done(t, o)    => {
              //println!("end, done");
              acc.clear();
            }
          }
        },
        Eof(v) => {
          println!("GOT EOF");
          v2.push_all(acc.as_slice());
          v2.push_all(v.as_slice());
          //acc.push_all(v.as_slice());
          //let r: &'a[u8] = acc.as_slice();
          //let data = if acc.len() == 0 { v } else { acc.push_all(v.as_slice()); acc };
          let p = Done((), v2.as_slice());
          match f(p) {
          //match f(begin(v2.as_slice())) {
            Error(e)      => println!("error, stopping: {}", e),
            //Incomplete(_) => println!("incomplete, continue"),
            Done(t, o)    => {
              println!("end, done");
              acc.clear();
            }
          };
          break;
        }
      }
      v2.clear();
    }
    println!("end push");
  }
}

