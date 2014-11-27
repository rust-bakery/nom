#![feature(globs,macro_rules)]
#![desc = "Omnomnom incremental byte parser"]
#![license = "MIT"]

extern crate collections;


use std::fmt::Show;
use std::io::fs::File;
use std::io::{IoResult, IoErrorKind};
use self::IResult::*;
use self::ProducerState::*;
use std::kinds::Sized;

pub type Err = uint;
type IResultClosure<'a,I,O> = |I|:'a -> IResult<I,O>;

//type IResultClosure<'a,I,O> = |I|:'a -> IResult<'a,I,O>;
//type IResultClosure<'a,I,O> = Fn<I, IResult<'a,I,O>>;
#[deriving(Show,PartialEq,Eq)]
pub enum IResult<I,O> {
  Done(I,O),
  Error(Err),
  //Incomplete(IResultClosure<'a,I,O>)
  //Incomplete(|I|:'a -> IResult<'a,I,O>)
  //Incomplete(fn(I) -> IResult<'a,I,O>)
}


pub trait Mapper<O,N> for Sized? {
  fn flat_map(& self, f: |O| -> IResult<O,N>) -> IResult<O,N>;
  fn map_opt(& self, f: |O| -> Option<N>) -> IResult<O,N>;
}

impl<'a,R,S,T> Mapper<&'a[S], T> for IResult<R,&'a [S]> {
  fn flat_map(&self, f: |&'a[S]| -> IResult<&'a[S],T>) -> IResult<&'a[S],T> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }

  fn map_opt(&self, f: |&'a[S]| -> Option<T>) -> IResult<&'a[S],T> {
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

impl<R,T> Mapper<(), T> for IResult<R,()> {
  fn flat_map(&self, f: |()| -> IResult<(),T>) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, _) => f(())
    }
  }

  fn map_opt(&self, f: |()| -> Option<T>) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, __) => match f(()) {
        Some(output) => Done((), output),
        None         => Error(0)
      }
    }
  }
}

pub fn print<T: Show>(input: T) -> IResult<T, ()> {
  println!("{}", input);
  Done(input, ())
}

pub fn begin<'a>(input: &'a [u8]) -> IResult<(), &'a [u8]> {
  Done((), input)
}

#[macro_export]
macro_rules! tag(
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      if i.len() >= $inp.len() && i.slice(0, $inp.len()) == $inp {
        Done(i.slice_from($inp.len()), i.slice(0, 0))
      } else {
        Error(0)
      }
    }
  )
)

macro_rules! o (
  ($name:ident<$i:ty,$o:ty> $f1:expr $($rest:tt)*) => (
    fn $name(input:$i) -> IResult<$i, $o>{
      match $f1(input) {
        Error(e)  => Error(e),
        Done(i,o) => {
          o_parser!(i o $($rest)*)
        }
      }
    }
  );
)

macro_rules! o_parser (
  ($i:expr $o:expr) => (Done($i,$o));

  ($i:expr $o:expr ~ $e:expr ~ $($rest:tt)*) => (
    match $e($i) {
      Error(e)  => Error(e),
      Done(i,o) => {
        o_parser!(i o $($rest)*)
      }
    }

   );
  ($i:expr $o:expr $e:expr $($rest:tt)*) => (
    match $e($i) {
      Error(e)  => Error(e),
      Done(i,_) => {
        o_parser!(i $o $($rest)*)
      }
    }
   );
)

macro_rules! chain (
  ($name:ident<$i:ty,$o:ty>, $assemble:expr, $($rest:tt)*) => (
    fn $name(i:$i) -> IResult<$i,$o>{
      chaining_parser!(i, $assemble, $($rest)*)
    }
  );
)

macro_rules! chaining_parser (
  ($i:expr, $assemble:expr, $field:ident : $e:expr, $($rest:tt)*) => (
    match $e($i) {
      Error(e)  => Error(e),
      Done(i,o) => {
        let $field = o;
        chaining_parser!(i, $assemble, $($rest)*)
      }
    }
  );

  ($i:expr, $assemble:expr, ) => (
    Done($i, $assemble())
  )
)

#[deriving(Show,PartialEq,Eq)]
pub enum ProducerState<O> {
  Eof(O),
  Continue,
  Data(O),
  ProducerError(Err),
}

type IResultStarterClosure<'a,I,T,O> = |IResult<(),I>|:'a -> IResult<T,O>;

pub struct FileProducer {
  size: uint,
  file: File
}

impl FileProducer {
  pub fn new(filename: &str, buffer_size: uint) -> IoResult<FileProducer> {
    File::open(&Path::new(filename)).map(|f| { FileProducer {size: buffer_size, file: f} })
  }

  fn produce(&mut self) -> ProducerState<Vec<u8>> {
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
/*}

impl Producer for FileProducer {
*/
  pub fn push<'y,O>(&mut self, f: |IResult<(),&[u8]>| -> IResult<&'y[u8],O>) {
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
          let mut v2 = Vec::new();
          v2.push_all(acc.as_slice());
          v2.push_all(v.as_slice());
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
          let mut v3 = Vec::new();
          v3.push_all(acc.as_slice());
          v3.push_all(v.as_slice());
          let p = Done((), v3.as_slice());
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
      //v2.clear();
    }
    println!("end push");
  }
}

pub struct MemProducer<'x> {
  buffer: &'x [u8],
  chunk_size: uint,
  length: uint,
  index: uint
}

impl<'x> MemProducer<'x> {
  pub fn new(buffer: &'x[u8], chunk_size: uint) -> MemProducer {
    MemProducer {
      buffer:     buffer,
      chunk_size: chunk_size,
      length:     buffer.len(),
      index:      0
    }
  }

  fn produce(&mut self) -> ProducerState<&'x[u8]> {
    if self.index + self.chunk_size < self.length {
      println!("self.index + {} < self.length", self.chunk_size);
      let new_index = self.index+self.chunk_size;
      let res = Data(self.buffer.slice(self.index, new_index));
      self.index = new_index;
      res
    } else if self.index < self.length {
      println!("self.index < self.length - 1");
      let res = Eof(self.buffer.slice(self.index, self.length));
      self.index = self.length;
      res
    } else {
      ProducerError(0)
    }
  }

  /*
}

impl<'x> Producer for MemProducer<'x> {
*/
  fn push<'b,O>(&mut self, f: |IResult<(),&'b[u8]>| -> IResult<&'b[u8],O>) {
    loop {
      let state = self.produce();
      match state {
        ProducerError(e)  => {println!("error: {}", e);break;},
        Continue => {println!("continue should not happen");break;},
        Data(v) => {
          let p = Done((), v);
          match f(p) {
            Error(e)      => println!("error, stopping: {}", e),
            Done(_, _)    => {
              println!("data, done");
            }
          }
        },
        Eof(v) => {
          let p = Done((), v);
          match f(p) {
            Error(e)      => println!("error, stopping: {}", e),
            Done(_, _)    => {
              println!("eof, done");
            }
          }
          break;
        }
      }
    }
  }
}

#[test]
fn flat_map_fn_test() {
  Done((),()).flat_map(print);
}

#[test]
fn flat_map_closure_test() {
  Done((),()).flat_map(|data| { println!("data: {}", data); Done(data,())});
  //assert_eq!(decoded.number, 10);
}

#[test]
fn t1() {
  let v1:Vec<u8> = vec![1,2,3];
  let v2:Vec<u8> = vec![4,5,6];
  let d = Done(v1.as_slice(), v2.as_slice());
  let res = d.flat_map(print);
  assert_eq!(res, Done(v2.as_slice(), ()));
}

#[test]
fn mem_producer_test() {
  let mut p = MemProducer::new("abcdefgh".as_bytes(), 4);
  assert_eq!(p.produce(), Data("abcd".as_bytes()));
}

#[test]
fn mem_producer_test_2() {
  let mut p = MemProducer::new("abcdefgh".as_bytes(), 8);
  p.push(|par| par.flat_map(print));
  let mut iterations: uint = 0;
  let mut p = MemProducer::new("abcdefghi".as_bytes(), 4);
  p.push(|par| {iterations = iterations + 1; par.flat_map(print)});
  assert_eq!(iterations, 3);
}

#[test]
fn file_test() {
  FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
    let mut p = producer;
    //p.push(|par| {println!("parsed file: {}", par); par});
    p.push(|par| par.flat_map(print));
  });
}

#[test]
fn tag_test() {
  FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
    let mut p = producer;
    tag!(f "https://".as_bytes());
    p.push(|par| par.flat_map(f).flat_map(print));
  });
}

#[deriving(PartialEq,Eq,Show)]
struct B {
  a: int,
  b: int
}

#[test]
fn chain_and_ignore_test() {
  tag!(x "abcd".as_bytes());
  tag!(y "efgh".as_bytes());
  fn retInt(i:&[u8]) -> IResult<&[u8], int> { Done(i,1) };
  //o!(z<&[u8], int>  x S x S retInt Z y);
  o!(z<&[u8], int>  x  x ~retInt~ y);

  let r = Done((), "abcdabcdefgh".as_bytes()).flat_map(z);
  assert_eq!(r, Done("".as_bytes(), 1));
}


#[test]
fn chain_test() {
  tag!(x "abcd".as_bytes());
  fn tempRetInt1(i:&[u8]) -> IResult<&[u8], int> { Done(i,1) };
  o!(retInt1<&[u8],int> x ~ tempRetInt1 ~);
  fn retInt2(i:&[u8]) -> IResult<&[u8], int> { Done(i,2) };
  chain!(f<&[u8],B>, ||{B{a: aa, b: bb}}, aa: retInt1, bb: retInt2,);

  let r = Done((), "abcde".as_bytes()).flat_map(f);
  assert_eq!(r, Done("e".as_bytes(), B{a: 1, b: 2}));
}


/* FIXME: this makes rustc weep
fn pr(par: IResult<(),&[u8]>) -> IResult<&[u8], ()> {
  Error(0)
}

#[test]
fn rustc_panic_test() {
  FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
    let mut p = producer;
    p.push(pr);
  });
}*/
