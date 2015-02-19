//! Data producers
//!
//! The goal of data producers is to parse data as soon as it is generated.
//!
//! # Example
//!
//! ```ignore
//!  use std::str;
//!  fn local_print<'a,T: Debug>(input: T) -> IResult<T, ()> {
//!    println!("{:?}", input);
//!    Done(input, ())
//!  }
//!  // create a data producer from a file
//!  FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
//!    let mut p = producer;
//!
//!    // create the parsing function
//!    fn parser(par: IResult<(),&[u8]>) -> IResult<&[u8],()> {
//!      par.map_res(str::from_utf8).flat_map(local_print);
//!      Done("".as_bytes(), ())
//!    }
//!
//!    // adapt the parsing function to the producer
//!    pusher!(push, parser);
//!    // get started
//!    push(&mut p);
//!  });
//! ```

use internal::*;
use self::ProducerState::*;

use std::fs::File;
use std::path::Path;
use std::num::Int;
use std::io;
use std::io::{Read,Seek,SeekFrom};

/// Holds the data producer's current state
///
/// * Eof indicates all data has been parsed, and contains the parser's result
///
/// * Continue indicates that more data is needed and should be available,
/// but not right now. Parsing should resume at some point.
///
/// * Data contains already parsed data
///
/// * ProducerError indicates something went wrong
#[derive(Debug,PartialEq,Eq)]
pub enum ProducerState<O> {
  Eof(O),
  Continue,
  Data(O),
  ProducerError(Err),
}

/// A producer implements the produce method, currently working with u8 arrays
pub trait Producer {
  fn produce(&mut self)                   -> ProducerState<&[u8]>;
  fn seek_to(&mut self,     position:u64) -> Option<u64>;
  fn seek_offset(&mut self, offset:i64)   -> Option<u64>;
}

/// Can produce data from a file
///
/// the size field is the size of v, the internal buffer
pub struct FileProducer {
  size: usize,
  file: File,
  v:    Vec<u8>
}

impl FileProducer {
  pub fn new(filename: &str, buffer_size: usize) -> io::Result<FileProducer> {
    File::open(&Path::new(filename)).map(|f| {
      FileProducer {size: buffer_size, file: f, v: Vec::with_capacity(buffer_size)}
    })
  }
}

impl Producer for FileProducer {
  fn produce(&mut self) -> ProducerState<&[u8]> {
    //let mut v = Vec::with_capacity(self.size);
    //self.v.clear();
    self.v.resize(self.size, 0);
    match self.file.read(&mut self.v) {
      Err(e) => {
        println!("producer error: {:?}", e);
        match e.kind() {
          //ErrorKind::NoProgress => Continue,
          //ErrorKind::EndOfFile  => Eof(&self.v[]),
          _          => ProducerError(0)
        }
      },
      Ok(n)  => {
        //println!("read: {} bytes\ndata:\n{}", n, (&self.v).to_hex(8));
        self.v.truncate(n);
        if n == 0 {
          Eof(&self.v[])
        } else {
          Data(&self.v[])
        }
      }
    }
  }

  fn seek_to(&mut self, position: u64) -> Option<u64> {
    self.file.seek(SeekFrom::Start(position)).ok()
  }

  fn seek_offset(&mut self, offset: i64) -> Option<u64> {
    self.file.seek(SeekFrom::Current(offset)).ok()
  }
}

/// Can parse data from an already in memory byte array
///
/// * buffer holds the reference to the data that must be parsed
///
/// * length is the length of that buffer
///
/// * index is the position in the buffer
///
/// * chunk_size is the quantity of data sent at once
pub struct MemProducer<'x> {
  buffer: &'x [u8],
  chunk_size: usize,
  length: usize,
  index: usize
}

impl<'x> MemProducer<'x> {
  pub fn new(buffer: &'x[u8], chunk_size: usize) -> MemProducer {
    MemProducer {
      buffer:     buffer,
      chunk_size: chunk_size,
      length:     buffer.len(),
      index:      0
    }
  }
}

impl<'x> Producer for MemProducer<'x> {
  fn produce(&mut self) -> ProducerState<&[u8]> {
    if self.index + self.chunk_size < self.length {
      println!("self.index + {} < self.length", self.chunk_size);
      let new_index = self.index+self.chunk_size;
      let res = Data(&self.buffer[self.index..new_index]);
      self.index = new_index;
      res
    } else if self.index < self.length {
      println!("self.index < self.length - 1");
      let res = Eof(&self.buffer[self.index..self.length]);
      self.index = self.length;
      res
    } else {
      ProducerError(0)
    }
  }

  fn seek_to(&mut self, position: u64) -> Option<u64> {
    if position as usize > self.length {
      self.index = self.length
    } else {
      self.index = position as usize
    }
    Some(self.index as u64)
  }

  fn seek_offset(&mut self, offset: i64) -> Option<u64> {
    let next = if offset >= 0 {
      (self.index as u64).checked_add(offset as u64)
    } else {
      (self.index as u64).checked_sub(-offset as u64)
    };

    match next {
      None    => None,
      Some(u) => {
        if u as usize > self.length {
          self.index = self.length
        } else {
          self.index = u as usize
        }
        Some(self.index as u64)
      }
    }
  }
}

/// Prepares a parser function for a push pipeline
///
/// It creates a function that accepts a producer and immediately starts parsing the data sent
///
/// # Example
///
/// ```ignore
/// fn pr(par: IResult<(),&[u8]>) -> IResult<&[u8],()> {
///   par.flat_map(local_print)
/// }
/// let mut p = MemProducer::new("abcdefgh".as_bytes(), 8);
///
/// pusher!(ps, pr);
/// ps(&mut p);
/// ```
#[macro_export]
macro_rules! pusher (
  ($name:ident, $f:expr) => (
    #[allow(unused_variables)]
    fn $name(producer: &mut Producer) {
      let mut acc: Vec<u8> = Vec::new();
      loop {
        let state = producer.produce();
        match state {
          ProducerState::Data(v) => {
            //println!("got data");
            acc.push_all(v)
          },
          ProducerState::Eof([])  => {
            //println!("eof empty, acc contains {} bytes: {:?}", acc.len(), acc);
            break;
          }
          ProducerState::Eof(v) => {
            //println!("eof with {} bytes", v.len());
            acc.push_all(v)
          }
          _ => {break;}
        }
        let mut v2: Vec<u8>  = Vec::new();
        v2.push_all(acc.as_slice());
        //let p = IResult::Done("".as_bytes(), v2.as_slice());
        match $f(v2.as_slice()) {
          IResult::Error(e)      => {
            //println!("error, stopping: {}", e);
            break;
          },
          IResult::Incomplete(_) => {
            //println!("incomplete");
          },
          IResult::Done(i, _)    => {
            //println!("data, done");
            acc.clear();
            acc.push_all(i);
          }
        }
      }
    }
  );
);

#[cfg(test)]
mod tests {
  use super::*;
  use internal::IResult;
  use internal::IResult::*;
  use std::fmt::Debug;
  use std::str;
  use map::*;

  fn local_print<'a,T: Debug>(input: T) -> IResult<'a,T, ()> {
    println!("{:?}", input);
    Done(input, ())
  }
  #[test]
  fn mem_producer() {
    let mut p = MemProducer::new("abcdefgh".as_bytes(), 4);
    assert_eq!(p.produce(), ProducerState::Data("abcd".as_bytes()));
  }

  #[test]
  fn mem_producer_2() {
    let mut p = MemProducer::new("abcdefgh".as_bytes(), 8);
    fn pr<'a,'b>(data: &'a [u8]) -> IResult<'b,&'a [u8],()> {
      local_print(data)
    }
    pusher!(ps, pr);
    ps(&mut p);
    //let mut iterations: uint = 0;
    //let mut p = MemProducer::new("abcdefghi".as_bytes(), 4);
    //p.push(|par| {iterations = iterations + 1; par.flat_map(print)});
    //assert_eq!(iterations, 3);
  }

  #[test]
  #[allow(unused_must_use)]
  fn file() {
    FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
      let mut p = producer;
      //p.push(|par| {println!("parsed file: {}", par); par});
      //p.push(|par| par.flat_map(print));
      fn pr<'a,'b,'c>(data: &[u8]) -> IResult<'b,&[u8], &[u8]> {
        Done("".as_bytes(), data).map_res(str::from_utf8); //.flat_map(local_print);
        Done("".as_bytes(),"".as_bytes())
      }
      pusher!(ps, pr);
      ps(&mut p);
      //assert!(false);
    });
  }

  #[test]
  fn accu() {
    fn f(input:&[u8]) -> IResult<&[u8],&[u8]> {
      if input.len() <= 4 {
        Incomplete(0)
      } else {
        Done("".as_bytes(), input)
      }
    }

    let mut p = MemProducer::new("abcdefgh".as_bytes(), 4);
    fn pr<'a,'b>(data: &'b [u8]) -> IResult<'b,&'b [u8],&'b [u8]> {
      let r = f(data);
      println!("f: {:?}", r);
      r
    }
    pusher!(ps, pr );
    ps(&mut p);
    //assert!(false);
  }

  #[test]
  fn accu_2() {
    fn f(input:&[u8]) -> IResult<&[u8],&[u8]> {
      if input.len() <= 4 || &input[0..5] != "abcde".as_bytes() {
        Incomplete(0)
      } else {
        Done(&input[5..], &input[0..5])
      }
    }

    let mut p = MemProducer::new("abcdefgh".as_bytes(), 4);
    fn pr<'a,'b,'c>(data: &'b [u8]) -> IResult<'b,&'b [u8],&'b [u8]> {
      let r = f(data);
      println!("f: {:?}", r);
      r
    }
    pusher!(ps, pr );
    ps(&mut p);
    //assert!(false);
  }
}
