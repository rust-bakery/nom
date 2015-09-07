//! Data producers
//!
//! The goal of data producers is to parse data as soon as it is generated.
//!
//! # Example
//!
//! ```
//! # #[macro_use] extern crate nom;
//! # use std::fmt::Debug;
//! # use nom::IResult;
//! # use nom::IResult::*;
//! # use nom::{Producer,ProducerState,FileProducer};
//! # fn main() {
//!  use std::str;
//!  fn local_print<'a, T: Debug>(input: T) -> IResult<'a, T, ()> {
//!    println!("{:?}", input);
//!    Done(input, ())
//!  }
//!
//!  // create a data producer from a file
//!  FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
//!    let mut p = producer;
//!
//!    // adapt the parsing function to the producer
//!    pusher!(push, local_print);
//!    // get started
//!    push(&mut p);
//!  });
//! # }
//! ```

use self::ProducerState::*;

use std::fs::File;
use std::path::Path;
use std::io;
use std::io::{Read,Seek,SeekFrom};
use std::iter::repeat;

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
  ProducerError(u32),
}

/// A producer implements the produce method, currently working with u8 arrays
pub trait Producer {
  fn produce(&mut self)                   -> ProducerState<&[u8]>;
  fn seek(&mut self,   position:SeekFrom) -> Option<u64>;
}

/// Can produce data from a file
///
/// the size field is the size of v, the internal buffer
#[allow(dead_code)]
pub struct FileProducer {
  size: usize,
  file: File,
  v:    Vec<u8>
}

impl FileProducer {
  pub fn new(filename: &str, buffer_size: usize) -> io::Result<FileProducer> {
    File::open(&Path::new(filename)).map(|f| {
      let mut v = Vec::with_capacity(buffer_size);
      v.extend(repeat(0).take(buffer_size));
      FileProducer {size: buffer_size, file: f, v: v}
    })
  }
}

impl Producer for FileProducer {
  fn produce(&mut self) -> ProducerState<&[u8]> {
    match self.file.read(&mut self.v) {
      Err(e) => {
        //println!("producer error: {:?}", e);
        match e.kind() {
          //ErrorKind::NoProgress => Continue,
          //ErrorKind::EndOfFile  => Eof(&self.v[..]),
          _          => ProducerError(0)
        }
      },
      Ok(n)  => {
        //println!("read: {} bytes\ndata:\n{}", n, (&self.v).to_hex(8));
        if n == 0 {
          Eof(&self.v[..n])
        } else {
          Data(&self.v[..n])
        }
      }
    }
  }

  fn seek(&mut self, position: SeekFrom) -> Option<u64> {
    self.file.seek(position).ok()
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
      //println!("self.index({}) + {} < self.length({})", self.index, self.chunk_size, self.length);
      let new_index = self.index+self.chunk_size;
      let res = Data(&self.buffer[self.index..new_index]);
      self.index = new_index;
      res
    } else if self.index < self.length {
      //println!("self.index < self.length - 1");
      let res = Eof(&self.buffer[self.index..self.length]);
      self.index = self.length;
      res
    } else {
      Eof(&b""[..])
    }
  }

  fn seek(&mut self, position: SeekFrom) -> Option<u64> {
    match position {
      SeekFrom::Start(pos) => {
        if pos as usize > self.length {
          self.index = self.length
        } else {
          self.index = pos as usize
        }
        Some(self.index as u64)
      },
      SeekFrom::Current(offset) => {
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
      },
      SeekFrom::End(i) => {
          let next = if i < 0 {
              (self.length as u64).checked_sub(-i as u64)
          } else {
              // std::io::SeekFrom documentation explicitly allows
              // seeking beyond the end of the stream, so we seek
              // to the end of the content if the offset is 0 or
              // greater.
              Some(self.length as u64)
          };
          match next {
              // std::io:SeekFrom documentation states that it `is an
              // error to seek before byte 0.' So it's the sensible
              // thing to refuse to seek on underflow.
              None => None,
              Some(u) => {
                  self.index = u as usize;
                  Some(u)
              }
          }
      }
    }
  }

}

/// Can produce data from a struct implementing Read
///
/// the size field is the size of v, the internal buffer
#[allow(dead_code)]
pub struct ReadProducer<T: Read> {
  size:   usize,
  reader: T,
  v:      Vec<u8>
}

impl<T: Read> ReadProducer<T> {
  pub fn new(reader: T, buffer_size: usize) -> ReadProducer<T> {
    let mut v = Vec::with_capacity(buffer_size);
    v.extend(repeat(0).take(buffer_size));
    ReadProducer {size: buffer_size, reader: reader, v: v}
  }
}

impl<T: Read> Producer for ReadProducer<T> {
  fn produce(&mut self) -> ProducerState<&[u8]> {
    match self.reader.read(&mut self.v) {
      Err(e) => {
        match e.kind() {
          _  => ProducerError(0)
        }
      },
      Ok(n)  => {
        if n == 0 {
          Eof(&self.v[..n])
        } else {
          Data(&self.v[..n])
        }
      }
    }
  }

  #[allow(unused_variables)]
  fn seek(&mut self, position: SeekFrom) -> Option<u64> {
    None
  }
}
/// Prepares a parser function for a push pipeline
///
/// It creates a function that accepts a producer and immediately starts parsing the data sent
///
/// # Example
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::Needed;
/// # use std::fmt::Debug;
/// # use nom::IResult;
/// # use nom::IResult::*;
/// # use nom::{ProducerState,Producer,MemProducer};
/// # fn main() {
/// fn local_print<'a, T: Debug>(input: T) -> IResult<'a, T, ()> {
///   println!("{:?}", input);
///   Done(input, ())
/// }
/// let mut p = MemProducer::new(b"abcdefgh", 8);
///
/// pusher!(ps, local_print);
/// ps(&mut p);
/// # }
/// ```
#[macro_export]
macro_rules! pusher (
  ($name:ident, $f:expr) => (
    #[allow(unused_variables)]
    fn $name(producer: &mut $crate::Producer) {
      let mut acc: Vec<u8> = Vec::new();
      loop {
        let state = producer.produce();
        match state {
          $crate::ProducerState::Data(v) => {
            //println!("got data");
            acc.extend(v.iter().cloned())
          },
          $crate::ProducerState::Eof(v) => {
            if v.is_empty() {
              //println!("eof empty, acc contains {} bytes: {:?}", acc.len(), acc);
              break;
            } else {
              //println!("eof with {} bytes", v.len());
              acc.extend(v.iter().cloned())
            }
          }
          _ => {break;}
        }
        let mut v2: Vec<u8>  = Vec::new();
        v2.extend(acc[..].iter().cloned());
        //let p = IResult::Done(b"", v2.as_slice());
        match $f(&v2[..]) {
          $crate::IResult::Error(e)      => {
            //println!("error, stopping: {}", e);
            break;
          },
          $crate::IResult::Incomplete(_) => {
            //println!("incomplete");
          },
          $crate::IResult::Done(i, _)    => {
            //println!("data, done");
            acc.clear();
            acc.extend(i.iter().cloned());
          }
        }
      }
    }
  );
);

#[derive(Debug,PartialEq,Eq)]
pub enum StepperState<'a,O> {
  Eof,
  Value(O),
  ProducerError(u32),
  Continue,
  ParserError(super::Err<'a>),
}

pub struct Stepper<T: Producer> {
  acc:       Vec<u8>,
  remaining: Vec<u8>,
  producer: T,
}

impl<T: Producer> Stepper<T> {
  pub fn new(producer: T) -> Stepper<T> {
    Stepper { acc: Vec::new(), remaining: Vec::new(), producer: producer }
  }


  pub fn step<'a, F, O>(&'a mut self, parser: F) -> StepperState<'a, O>
                      where F: Fn(&'a [u8]) -> super::IResult<&'a [u8],O> {
    self.acc.clear();
    self.acc.extend(self.remaining.iter().cloned());
    let state = self.producer.produce();
    match state {
      ProducerState::Data(v) => {
        self.acc.extend(v.iter().cloned())
      },
      ProducerState::Eof(v) => {
        self.acc.extend(v.iter().cloned())
      },
      ProducerState::Continue => {
        return StepperState::Continue;
      },
      ProducerState::ProducerError(u) => {
        return StepperState::ProducerError(u);
      }
    }

    if self.acc.is_empty() {
      return StepperState::Eof;
    }

    match parser(&(self.acc)[..]) {
      super::IResult::Error(e)      => {
        self.remaining.clear();
        self.remaining.extend(self.acc.iter().cloned());
        StepperState::ParserError(e)
      },
      super::IResult::Incomplete(_) => {
        self.remaining.clear();
        self.remaining.extend(self.acc.iter().cloned());
        StepperState::Continue
      },
      super::IResult::Done(i, o)    => {
        self.remaining.clear();
        self.remaining.extend(i.iter().cloned());
        StepperState::Value(o)
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Needed,IResult};
  use std::fmt::Debug;
  use std::io::SeekFrom;

  fn local_print<'a,T: Debug>(input: T) -> IResult<'a,T, ()> {
    println!("{:?}", input);
    IResult::Done(input, ())
  }

  #[test]
  fn mem_producer() {
    let mut p = MemProducer::new(&b"abcdefgh"[..], 4);
    assert_eq!(p.produce(), ProducerState::Data(&b"abcd"[..]));
  }

  #[test]
  fn mem_producer_2() {
    let mut p = MemProducer::new(&b"abcdefgh"[..], 8);
    fn pr<'a,'b>(data: &'a [u8]) -> IResult<&'a [u8],()> {
      local_print(data)
    }
    pusher!(ps, pr);
    ps(&mut p);
    //let mut iterations: uint = 0;
    //let mut p = MemProducer::new(b"abcdefghi", 4);
    //p.push(|par| {iterations = iterations + 1; par.flat_map(print)});
    //assert_eq!(iterations, 3);
  }


  #[test]
  fn mem_producer_seek_from_end() {
      let mut p = MemProducer::new(&b"abcdefg"[..], 1);
      p.seek(SeekFrom::End(-4));
      assert_eq!(p.produce(), ProducerState::Data(&b"d"[..]));
  }

  #[test]
  fn mem_producer_seek_beyond_end() {
      let mut p = MemProducer::new(&b"abcdefg"[..], 1);
      p.seek(SeekFrom::End(1));
      assert_eq!(p.produce(), ProducerState::Eof(&b""[..]));
  }

  #[test]
  fn mem_producer_seek_before_start() {
      let mut p = MemProducer::new(&b"abcdefg"[..], 1);
      // Let's seek a bit forward in the input to ensure that
      // we don't just seek to the start when we do an
      // invalid seek operation.
      p.seek(SeekFrom::Start(1));
      let seek_result = p.seek(SeekFrom::End(-8));
      // It shouldn't do any seeking
      assert_eq!(seek_result, None);
      // And the position should still be at the second byte
      assert_eq!(p.produce(), ProducerState::Data(&b"b"[..]));
  }


  #[test]
  #[allow(unused_must_use)]
  fn file() {
    FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
      let mut p = producer;
      //p.push(|par| {println!("parsed file: {}", par); par});
      //p.push(|par| par.flat_map(print));

      pusher!(ps, local_print);
      ps(&mut p);
      //assert!(false);
    });
  }

  #[test]
  fn accu() {
    fn f(input:&[u8]) -> IResult<&[u8],&[u8]> {
      if input.len() <= 4 {
        IResult::Incomplete(Needed::Size(4))
      } else {
        IResult::Done(b"", input)
      }
    }

    let mut p = MemProducer::new(b"abcdefgh", 4);
    fn pr<'a,'b>(data: &'b [u8]) -> IResult<&'b [u8],&'b [u8]> {
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
      if input.len() <= 4 || &input[0..5] != b"abcde" {
        IResult::Incomplete(Needed::Size(4))
      } else {
        IResult::Done(&input[5..], &input[0..5])
      }
    }

    let mut p = MemProducer::new(b"abcdefgh", 4);
    fn pr<'a,'b,'c>(data: &'b [u8]) -> IResult<&'b [u8],&'b [u8]> {
      let r = f(data);
      println!("f: {:?}", r);
      r
    }
    pusher!(ps, pr );
    ps(&mut p);
    //assert!(false);
  }

  #[test]
  fn stepper() {
    let p = MemProducer::new(&b"abcdabcd"[..], 3);
    fn pr<'a>(input: &'a [u8]) -> IResult<&'a [u8],&[u8]> {
      if input.len() >= 4 {
        IResult::Done(&input[4..], &input[0..4])
      } else {
        IResult::Incomplete(Needed::Size(4 - input.len()))
      }
    }

    let mut s = Stepper::new(p);
    for i in 0..3 {
      let res = s.step(|x| pr(x));
      match i {
        0     => assert_eq!(res, StepperState::Continue),
        1 | 2 => assert_eq!(res, StepperState::Value(&b"abcd"[..])),
        _     => assert!(false)
      }
    }
    let res2 = s.step(|x| pr(x));
    assert_eq!(res2, StepperState::Eof);
  }
}
