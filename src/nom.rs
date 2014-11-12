#![desc = "Omnomnom incremental byte parser"]
#![license = "MIT"]

extern crate collections;


use std::fmt::Show;
use std::str;
use std::io::fs::File;
use std::io::{IoResult, IoErrorKind};

type Err = uint;
type ParserClosure<'a,I,O> = |I|:'a -> Parser<I,O>;

//type ParserClosure<'a,I,O> = |I|:'a -> Parser<'a,I,O>;
//type ParserClosure<'a,I,O> = Fn<I, Parser<'a,I,O>>;
#[deriving(Show,PartialEq,Eq)]
pub enum Parser<I,O> {
  Done(I,O),
  Error(Err),
  //Incomplete(ParserClosure<'a,I,O>)
  //Incomplete(|I|:'a -> Parser<'a,I,O>)
  //Incomplete(fn(I) -> Parser<'a,I,O>)
}

pub trait Mapper<O,N> {
  fn map(&self, f: |O| -> Parser<O,N>) -> Parser<O,N>;
  fn mapf(&self, f: |O| -> Option<N>) -> Parser<O,N>;
}

impl<'a,N> Mapper<&'a [u8], &'a [u8]> for Parser<N,&'a [u8]> {
  fn map<'b,'c>(&'b self, f: |&'a [u8]| -> Parser<&'c [u8], &'a [u8]>) -> Parser<&'c [u8], &'a [u8]> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }

  fn mapf(&self, f: |&'a [u8]| -> Option<&'a [u8]>) -> Parser<&'a [u8], &'a [u8]> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, ref o) => match f(*o) {
        Some(output) => Done(*o, output),
        None         => Error(0)
      }
    }
  }
}

impl<'a,N> Mapper<&'a [u8],()> for Parser<N,&'a [u8]> {
  fn map<'b,'c>(&'b self, f: |&'a [u8]| -> Parser<&'c [u8],()>) -> Parser<&'c [u8], ()> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }

  fn mapf(&self, f: |&'a [u8]| -> Option<()>) -> Parser<&'a [u8], ()> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, ref o) => match f(*o) {
        Some(output) => Done(*o, output),
        None         => Error(0)
      }
    }
  }
}

impl<'a,N> Mapper<&'a [u8],&'a str> for Parser<N,&'a [u8]> {
  fn map<'b,'c>(&'b self, f: |&'a [u8]| -> Parser<&'c [u8],&'c str>) -> Parser<&'c [u8], &'c str> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }

  fn mapf(&self, f: |&'a [u8]| -> Option<&'a str>) -> Parser<&'a [u8], &'a str> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, ref o) => match f(*o) {
        Some(output) => Done(*o, output),
        None         => Error(0)
      }
    }
  }
}

impl<'a,N> Mapper<&'a str,()> for Parser<N,&'a str> {
  fn map<'b,'c>(&'b self, f: |&'a str| -> Parser<&'c str,()>) -> Parser<&'c str, ()> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }

  fn mapf(&self, f: |&'a str| -> Option<()>) -> Parser<&'a str, ()> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, ref o) => match f(*o) {
        Some(output) => Done(*o, output),
        None         => Error(0)
      }
    }
  }
}

impl<'a,N> Mapper<(),()> for Parser<N,()> {
  fn map<'b,'c>(&'b self, f: |()| -> Parser<(),()>) -> Parser<(), ()> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }

  fn mapf(&self, f: |()| -> Option<()>) -> Parser<(), ()> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, ref o) => match f(*o) {
        Some(output) => Done(*o, output),
        None         => Error(0)
      }
    }
  }
}

pub trait Ender<O> {
  fn end(&self, f: |O| -> ()) -> ();
}

impl<'a> Ender<&'a [u8]> for Parser<&'a [u8],&'a [u8]> {
  fn end(&self, f: |&'a [u8]| -> ()) -> () {
    match self {
      &Error(_) => (),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => {
        f(*o)
      }
    }
  }
}
impl<'a> Ender<&'a str> for Parser<&'a [u8],&'a str> {
  fn end(&self, f: |&'a str| -> ()) -> () {
    match self {
      &Error(_) => (),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => {
        f(*o)
      }
    }
  }
}

impl<'a> Ender<&'a [u8]> for Parser<(),&'a [u8]> {
  fn end(&self, f: |&'a [u8]| -> ()) -> () {
    match self {
      &Error(_) => (),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => {
        f(*o)
      }
    }
  }
}

/***/
impl<'a>  Parser<(),&'a [u8]> {
  pub fn m2<'b,'c>(&'b self, f: |&'a [u8]| -> Parser<&'c [u8],()>) -> Parser<&'c [u8], ()> {
    match self {
      &Error(ref e) => Error(*e),
      &Done(_, ref o) => f(*o)
    }
  }
  pub fn m3<'b,'c>(&'b self, f: |&'a [u8]| -> Parser<&'c [u8],&'c [u8]>) -> Parser<&'c [u8], &'c [u8]> {
    match self {
      &Error(ref e) => Error(*e),
      &Done(_, ref o) => f(*o)
    }
  }
}
impl<'a>  Parser<&'a [u8],&'a str> {
  pub fn m4<'b,'c>(&'b self, f: |&'a str| -> Parser<&'c str,()>) -> Parser<&'c str, ()> {
    match self {
      &Error(ref e) => Error(*e),
      &Done(_, ref o) => f(*o)
    }
  }
}
/***/

pub fn accline<'a>(input: &'a [u8]) -> Parser<&'a [u8], &'a [u8]> {
  match input.iter().position(|&c| c == '\n' as u8) {
    None      => Error(0),//Incomplete(accline),
    Some(pos) => Done(input.slice_from(pos), input.slice(0, pos))
  }
}

pub fn print<T: Show>(input: T) -> Parser<T, ()> {
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

  pub fn push<T,O>(&mut self, f: |Parser<(),&[u8]>| -> Parser<T,O>) {
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
            Done(_, _)    => {
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
            Done(_, _)    => {
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

#[test]
fn map_fn() {
  Done((),()).map(print);
}

#[test]
fn map_closure() {
  Done((),()).map(|data| { println!("data: {}", data); Done(data,())});
  //assert_eq!(decoded.number, 10);
}

#[test]
fn t1() {
  let v1:Vec<u8> = vec![1,2,3];
  let v2 = vec![4,5,6];
  let d = Done(v1.as_slice(), v2.as_slice());
  let res = d.map(print);
  assert_eq!(res, Done(v2.as_slice(), ()));
}

#[test]
fn end_test() {
  let v1:Vec<u8> = vec![1,2,3];
  let v2 = vec![4,5,6];
  let d = Done(v1.as_slice(), v2.as_slice());
  let mut res: Vec<u8> = Vec::new();
  d.end(|v:&[u8]| res.push_all(v));
  assert_eq!(res.as_slice(), v2.as_slice());
}

#[test]
fn file_test() {
  FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
    let mut p = producer;
    p.push(|par| {println!("parsed file: {}", par); par});
    p.push(|par| par.map(print));
  });
}

/*
#[test]
fn file_chain_test() {
  FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
    let mut p = producer;
    p.push(|par| par.map(accline).mapf(|v2: &[u8]| str::from_utf8(v2.as_slice())).map(print));
  });
}*/
