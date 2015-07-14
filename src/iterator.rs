use std::io;
use std::io::{Read,BufRead};
use std::iter::{repeat,Iterator};
use std::fmt;
use std::cmp;
use std::iter;
use super::util::HexDisplay;
use super::internal::IResult;

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
    for i in 0..self.cap {
      self.buf[i] = self.buf[self.pos + i];
    }
    self.pos = 0;
  }

  pub fn current_slice(&self) -> &[u8] {
    &self.buf[self.pos..self.cap]
  }

  pub fn capacity(&self) -> usize {
    self.cap
  }
}

impl<R: Read> Read for AccReader<R> {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    if buf.len() < self.cap {
      match (&self.buf[self.pos..buf.len()]).read(buf) {
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
    if self.pos == 0 && self.cap == self.buf.len() {
      Err(io::Error::new(io::ErrorKind::Interrupted, "buffer completely filled"))
    } else {
      self.reset_buffer_position();
      let read = try!(self.inner.read(&mut self.buf[self.cap..]));
      self.cap += read;
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
  f:      F
}

impl<R:Read,O,F> ParsingIterator<R,F> where  F: FnMut(&[u8]) -> super::IResult<&[u8],O> {
  pub fn new(reader: R, f: F) -> ParsingIterator<R,F> {
    ParsingIterator {
      reader: AccReader::new(reader),
      f: f
    }
  }
}

impl<R: Read, O, F> Iterator for ParsingIterator<R,F> where F: FnMut(&[u8]) -> super::IResult<&[u8],O> {
  type Item = O;
  fn next(&mut self) -> Option<O> {
    let ref mut f = self.f;
    let capacity = self.reader.capacity();
    let mut res: Option<O> = None;
    let mut consumed = 0;

    match f(self.reader.current_slice()) {
      IResult::Error(_)   => return None,
      IResult::Done(i, o) => {
        consumed = capacity - i.len();
        res = Some(o);
      }
      _ => { }
    }

    if res.is_some() {
      self.reader.consume(consumed);
      return res;
    } else {
      let fill_res = self.reader.fill_buf();
      match fill_res {
        Err(_) => return None,
        Ok(s)  => match f(s) {
          IResult::Done(i, o) => {
            consumed = s.offset(i);
            res = Some(o);
          },
          // if it des not work with full buffer, abort
          _                   => return None
        }
      }
    }
    self.reader.consume(consumed);
    res
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Needed,IResult};
  use std::fmt::Debug;
  use std::io::{Cursor,Read};
  use std::str;

  #[test]
  fn acc_reader_test() {
    let buf = b"abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd";
    let c = Cursor::new(&buf[..]);
    //let acc = AccReader::new(c);

    fn take_4<'x>(input:&'x[u8]) -> IResult<&'x[u8],&'x[u8]> {
      if input.len() <= 4 {
        IResult::Incomplete(Needed::Size(4))
      } else {
        IResult::Done(&input[4..], &input[0..4])
      }
    }

    //let it = ParsingIterator::new(c, take_4);
    let it = ParsingIterator::new(c, move |input| { take_4(  &input  ) });
    //let it = ParsingIterator::new(c, |input| { IResult::Done(input, &b""[..]) });

    for el in it {
      println!("el: {}", str::from_utf8(el).unwrap());
    }
  }
}
