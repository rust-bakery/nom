use std::io;
use std::io::{Read,BufRead};
use std::iter::{repeat,Iterator};
use std::fmt;
use std::cmp;
use std::iter;
use super::util::HexDisplay;
use super::internal::IResult;
use std::marker::PhantomData;

pub struct AccReader<R> {
    inner: R,
    buf: Vec<u8>,
    pos: usize,
    cap: usize,
}

impl<R: Read> AccReader<R> {
  pub fn new(inner: R) -> AccReader<R> {
    AccReader::with_capacity(10, inner)
  }

  pub fn with_capacity(cap: usize, inner: R) -> AccReader<R> {
    let mut buf = Vec::with_capacity(cap);
    buf.extend(iter::repeat(0).take(cap));
    AccReader {
      inner: inner,
      buf: buf,
      pos: 0,
      cap: 0,
    }
  }

  /// Gets a reference to the underlying reader.
  pub fn get_ref(&self) -> &R { &self.inner }

  /// Gets a mutable reference to the underlying reader.
  pub fn get_mut(&mut self) -> &mut R { &mut self.inner }

  /// Unwraps this `AccReader`, returning the underlying reader.
  ///
  /// Note that any leftover data in the internal buffer is lost.
  pub fn into_inner(self) -> R { self.inner }

  pub fn reset_buffer_position(&mut self) {
    println!("resetting buffer at pos: {} capacity: {}", self.pos, self.cap);
    if self.cap > 0 {
      for i in 0..(self.cap - self.pos - 1) {
        println!("buf[{}] = buf[{}]", i, self.pos + i);
        self.buf[i] = self.buf[self.pos + i];
      }
    }
    self.cap = self.cap - self.pos;
    self.pos = 0;
  }

  pub fn current_slice(&self) -> &[u8] {
    println!("current slice pos: {}, cap: {}", self.pos, self.cap);
    &self.buf[self.pos..self.cap]
  }

  pub fn capacity(&self) -> usize {
    self.cap - self.pos
  }
}

impl<R: Read> Read for AccReader<R> {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    println!("read pos: {} cap: {} buflen: {}", self.pos, self.cap, buf.len());
    if buf.len() < self.cap - self.pos {
      match (&self.buf[self.pos..(self.pos+buf.len())]).read(buf) {
        Ok(len) => {
          self.consume(len);
          Ok(len)
        },
        Err(e) => Err(e)
      }
    } else {
      // If we don't have any buffered data and we're doing a massive read
      // (larger than our internal buffer), bypass our internal buffer
      // entirely.
      if buf.len() > self.buf.len() {
        match (&self.buf[self.pos..self.cap]).read(buf) {
          Ok(len) => {
            self.consume(len);
            self.inner.read(&mut buf[self.cap..])
          },
          Err(e) => Err(e)
        }
      } else {
        let nread = {
          let mut rem = try!(self.fill_buf());
          try!(rem.read(buf))
        };
        self.consume(nread);
        Ok(nread)
      }
    }
  }
}

impl<R: Read> BufRead for AccReader<R> {
  fn fill_buf(&mut self) -> io::Result<&[u8]> {
      println!("fillbuf");
    if self.pos == 0 && self.cap == self.buf.len() {
      Err(io::Error::new(io::ErrorKind::Interrupted, "buffer completely filled"))
    } else {
      self.reset_buffer_position();
      println!("buffer reset ended");
      let read = try!(self.inner.read(&mut self.buf[self.cap..]));
      self.cap += read;
      println!("new pos: {} and cap: {}", self.pos, self.cap);
      Ok(&self.buf[self.pos..self.cap])
    }
  }

  fn consume(&mut self, amt: usize) {
    self.pos = cmp::min(self.pos + amt, self.cap);
  }
}

impl<R> fmt::Debug for AccReader<R> where R: fmt::Debug {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    fmt.debug_struct("AccReader")
      .field("reader", &self.inner)
      .field("buffer", &format_args!("{}/{}", self.cap - self.pos, self.buf.len()))
      .finish()
  }
}

pub struct ParsingIterator<R:Read,F> {
  reader: AccReader<R>,
  f:      F,
  //phantom: PhantomData<O>
}

//impl<'a, R:Read,O:'a ,F> ParsingIterator<R,F> where  F: FnMut(&'a [u8]) -> super::IResult<&'a [u8],O> {
impl<R:Read,F> ParsingIterator<R,F> {
  pub fn new(reader: R, f: F) -> ParsingIterator<R,F> {
    let mut r = AccReader::new(reader);
    r.fill_buf();
    ParsingIterator {
      reader: r,
      f: f,
      //phantom: PhantomData
    }
  }
}

impl<R: Read, O: fmt::Debug, F> Iterator for ParsingIterator<R,F> where F: FnMut(&[u8]) -> super::IResult<&[u8],O> {
  type Item = O;
  fn next(&mut self) -> Option<O> {
    let ref mut f = self.f;
    let capacity = self.reader.capacity();
    let mut res: Option<O> = None;
    let mut consumed = 0;

    println!("next");
    match f(self.reader.current_slice()) {
      IResult::Error(_)   => return None,
      IResult::Done(i, o) => {
        println!("i: {:?}", i);
        println!("o: {:?}", o);
        consumed = capacity - i.len();
        res = Some(o);
      }
      _ => { }
    }

    println!("next1: consumed: {} res: {:?}", consumed, res);
    if res.is_some() {
      self.reader.consume(consumed);
      return res;
    } else {
      let fill_res = self.reader.fill_buf();
      println!("fill_res: {:?}", fill_res);
      match fill_res {
        Err(_) => return None,
        Ok(s)  => {
          if s.len() == 0 {
            println!("s.len() == 0");
            return None
          } else {
            match f(s) {
              IResult::Done(i, o) => {
                consumed = s.offset(i);
                res = Some(o);
              },
              // if it des not work with full buffer, abort
              _                   => return None
            }
          }
        }
      }
    }
    println!("next2: consumed: {} res: {:?}", consumed, res);
    self.reader.consume(consumed);
    res
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Needed,IResult};
  use std::fmt::Debug;
  use std::io::{Cursor,Read,BufRead};
  use std::str;
  use std::iter::Iterator;

  #[test]
  fn acc_reader_test() {
    //let buf = b"abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd";
    let buf = b"abcd\nabcdabcdabcdabcdabcdabcd\nabcdabcdabcdabcdabcdabc\ndabcdabcdabcdab\ncdabcdabcdabcd\nabcdabcdabcdabcdabcda\nbcdabcdabcdabcdabcdabcdabcd";
    let c = Cursor::new(&buf[..]);

    fn take_4<'x>(input:&'x[u8]) -> IResult<&'x[u8],&'x[u8]> {
      if input.len() <= 4 {
        IResult::Incomplete(Needed::Size(4))
      } else {
        //IResult::Done(&input[4..], &input[0..4])
        IResult::Incomplete(Needed::Unknown)
      }
    }

    /*
    let acc = AccReader::new(c);
    for l in acc.lines() {
      println!("l: {:?}", l);
    }*/

    //let it = ParsingIterator::new(c, take_4);
    let mut it = ParsingIterator::new(c, (|input| { take_4(  input  ) }) as FnMut(&[u8]) -> IResult<&[u8],&[u8]>);
    /*
    let it = ParsingIterator::new(c, |input| {
      println!("input: {:?}", &input);
      if input.len() >= 4 {
        //IResult::Done(&input[4..], &b""[..])
        //let clo = input.clone();
        //IResult::Done(&input[4..], &clo[0..4])
        IResult::Done(&input[4..], &input[4..])
      } else {
        //IResult::Done(&b""[..], &b""[..])
        IResult::Incomplete(Needed::Unknown)
      }
    });
    */

    let mut count = 0;
    /*for el in it {
      println!("el: {}", str::from_utf8(el).unwrap());
      count +=1;
      if count > 5 { break; }
    }*/

    let el1 = it.next();
    println!("el1: {:?}", el1);
    let el2 = it.next();
    println!("el2: {:?}", el2);
    let el3 = it.next();
    println!("el3: {:?}", el3);
    let el4 = it.next();
    println!("el4: {:?}", el4);
    assert!(false);
  }
}
