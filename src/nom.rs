#![desc = "Omnomnom incremental byte parser"]
#![license = "MIT"]

extern crate collections;


use std::fmt::Show;
use std::io::fs::File;
use std::io::{IoResult, IoErrorKind};
use self::IResult::*;
use self::ProducerState::*;
use std::kinds::Sized;
use std::str;

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

pub trait Mapper2<O,N,I> for Sized? {
  fn map(& self, f: |O| -> N) -> IResult<I,N>;
}

impl<'a,R,S,T> Mapper2<&'a[S], T, &'a R> for IResult<&'a R,&'a [S]> {
  fn map(&self, f: |&'a[S]| -> T) -> IResult<&'a R,T> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,R,S,T> Mapper2<&'a[S], T, &'a [R]> for IResult<&'a [R],&'a [S]> {
  fn map(&self, f: |&'a[S]| -> T) -> IResult<&'a [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,R,T> Mapper2<(), T, &'a R> for IResult<&'a R,()> {
  fn map(&self, f: |()| -> T) -> IResult<&'a R,T> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,S,T> Mapper2<&'a[S], T, ()> for IResult<(),&'a [S]> {
  fn map(&self, f: |&'a[S]| -> T) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => Done((),f(*o))
    }
  }
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

macro_rules! alt (
  ($name:ident<$i:ty,$o:ty>, $($rest:tt)*) => (
    fn $name(i:$i) -> IResult<$i,$o>{
      alt_parser!(i, $($rest)*)
    }
  );
)

macro_rules! alt_parser (
  ($i:expr, $e:expr $($rest:tt)*) => (
    match $e($i) {
      Error(_)  => alt_parser!($i, $($rest)*),
      Done(i,o) => Done(i,o)
    }
  );

  ($i:expr, ) => (
    Error(1)
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

pub fn print<T: Show>(input: T) -> IResult<T, ()> {
  println!("{}", input);
  Done(input, ())
}

pub fn begin<'a>(input: &'a [u8]) -> IResult<(), &'a [u8]> {
  Done((), input)
}

#[macro_export]
macro_rules! is_not(
  ($name:ident $arr:expr) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      for idx in range(0, input.len()) {
        for &i in $arr.iter() {
          if input[idx] == i {
            return Done(input.slice_from(idx), input.slice(0, idx))
          }
        }
      }
      Done("".as_bytes(), input)
    }
  )
)

#[macro_export]
macro_rules! is_a(
  ($name:ident $arr:expr) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      for idx in range(0, input.len()) {
        var res = false
        for &i in $arr.iter() {
          if input[idx] == i {
            res = true
          }
        }
        if !res {
          return Done(input.slice_from(idx), input.slice(0, idx))
        }
      }
      Done("".as_bytes(), input)
    }
  )
)

#[macro_export]
macro_rules! filter(
  ($name:ident $f:ident) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      for idx in range(0, input.len()) {
        if !$f(input[idx]) {
          return Done(input.slice_from(idx), input.slice(0, idx))
        }
      }
      Done("".as_bytes(), input)
    }
  )
)

is_not!(line_ending "\r\n".as_bytes())

fn is_alphabetic(chr:u8) -> bool {
  (chr >= 0x41 && chr <= 0x5A) || (chr >= 0x61 && chr <= 0x7A)
}

fn is_digit(chr: u8) -> bool {
  chr >= 0x30 && chr <= 0x39
}
fn is_alphanumeric(chr: u8) -> bool {
  is_alphabetic(chr) || is_digit(chr)
}

filter!(alpha is_alphabetic)
filter!(digit is_digit)
filter!(alphanumeric is_alphanumeric)

fn sized_buffer(input:&[u8]) -> IResult<&[u8], &[u8]> {
  if input.len() == 0 {
    //FIXME: should return Incomplete
    return Error(0)
  }

  let len = input[0] as uint;

  if input.len() >= len + 1 {
    return Done(input.slice_from(len+1), input.slice(1, len+1))
  } else {
    //FIXME: should return Incomplete
    return Error(0)
  }
}

#[test]
fn character_test() {
  let empty = "".as_bytes();
  let a = "abcd".as_bytes();
  let b = "1234".as_bytes();
  let c = "a123".as_bytes();
  let d = "azé12".as_bytes();
  assert_eq!(Done((),a).flat_map(alpha), Done(empty, a))
  assert_eq!(Done((),b).flat_map(alpha), Done(b, empty))
  assert_eq!(Done((),c).flat_map(alpha), Done(c.slice_from(1), "a".as_bytes()))
  assert_eq!(Done((),d).flat_map(alpha), Done("é12".as_bytes(), "az".as_bytes()))
  assert_eq!(Done((),a).flat_map(digit), Done(a, empty))
  assert_eq!(Done((),b).flat_map(digit), Done(empty, b))
  assert_eq!(Done((),c).flat_map(digit), Done(c, empty))
  assert_eq!(Done((),d).flat_map(digit), Done(d, empty))
  assert_eq!(Done((),a).flat_map(alphanumeric), Done(empty, a))
  assert_eq!(Done((),b).flat_map(alphanumeric), Done(empty, b))
  assert_eq!(Done((),c).flat_map(alphanumeric), Done(empty, c))
  assert_eq!(Done((),d).flat_map(alphanumeric), Done("é12".as_bytes(), "az".as_bytes()))
}

#[test]
fn is_not_test() {
  let a = "ab12cd\nefgh".as_bytes();
  assert_eq!(Done((), a).flat_map(line_ending), Done("\nefgh".as_bytes(), "ab12cd".as_bytes()))
}

#[test]
fn sized_buffer_test() {
  let arr:[u8, ..6] = [3, 4, 5, 6, 7, 8];
  let res = Done((), arr.as_slice()).flat_map(sized_buffer);
  let i = [7,8];
  let o = [4,5,6];
  assert_eq!(res, Done(i.as_slice(), o.as_slice()))
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
fn map_test() {
  let res = Done((),"abcd".as_bytes()).map(|data| { str::from_utf8(data).unwrap() });
  assert_eq!(res, Done((), "abcd"));
}

#[test]
fn map_test_2() {
  let res = Done("abcd".as_bytes(),"efgh".as_bytes()).map(|data| { str::from_utf8(data).unwrap() });
  assert_eq!(res, Done("abcd".as_bytes(), "efgh"));
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
  fn ret_int(i:&[u8]) -> IResult<&[u8], int> { Done(i,1) };
  //o!(z<&[u8], int>  x S x S retInt Z y);
  o!(z<&[u8], int>  x  x ~ret_int~ y);

  let r = Done((), "abcdabcdefgh".as_bytes()).flat_map(z);
  assert_eq!(r, Done("".as_bytes(), 1));
}


#[test]
fn chain_test() {
  tag!(x "abcd".as_bytes());
  fn temp_ret_int1(i:&[u8]) -> IResult<&[u8], int> { Done(i,1) };
  o!(ret_int1<&[u8],int> x ~ temp_ret_int1 ~);
  fn ret_int2(i:&[u8]) -> IResult<&[u8], int> { Done(i,2) };
  chain!(f<&[u8],B>, ||{B{a: aa, b: bb}}, aa: ret_int1, bb: ret_int2,);

  let r = Done((), "abcde".as_bytes()).flat_map(f);
  assert_eq!(r, Done("e".as_bytes(), B{a: 1, b: 2}));
}

#[test]
fn alt_test() {
  fn work(input: &[u8]) -> IResult<&[u8],&[u8]> {
    Done("".as_bytes(), input)
  }
  fn dont_work(input: &[u8]) -> IResult<&[u8],&[u8]> {
    Error(3)
  }
  fn work2(input: &[u8]) -> IResult<&[u8],&[u8]> {
    Done(input, "".as_bytes())
  }

  alt!(alt1<&[u8],&[u8]>, dont_work dont_work)
  alt!(alt2<&[u8],&[u8]>, dont_work work)
  alt!(alt3<&[u8],&[u8]>, dont_work dont_work work2 dont_work)

  let a = "abcd".as_bytes();
  assert_eq!(Done((), a).flat_map(alt1), Error(1))
  assert_eq!(Done((), a).flat_map(alt2), Done("".as_bytes(), a))
  assert_eq!(Done((), a).flat_map(alt3), Done(a, "".as_bytes()))
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
