#![desc = "Omnomnom incremental byte parser"]
#![license = "MIT"]

extern crate collections;

use std::fmt::Show;
use std::io;
use std::io::fs::File;
use std::io::IoResult;

type Err = uint;
pub enum Parser<'a,I,O> {
  Done(I,O),
  Error(I, Err),
  //Incomplete(|I|:'a -> Parser<I,O>)
  Incomplete(fn(I) -> Parser<'a,I,O>)
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
      Error(i, e) => {
        println!("error: {} input: {}", e, i);
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
    0 => Error(input, 0),
    1 => Incomplete(parse),
    _ => Done(input.slice_from(2), input.slice(0,2))
  }
}

pub fn print<'a, T: Show>(input: &'a T) -> Parser<'a, (), ()> {
  println!("{}", input);
  Done((), ())
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
        _ => Error((), 0)
      },
      Ok(i)  => {
        println!("read {} bytes", i);
        Done((), v)
      }
    }
  }
}

