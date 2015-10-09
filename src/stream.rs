/// Context:
/// * Rust does not have tail call optimization, so we cannot recurse wildly
/// * data lifetimes makes sure that the result of a function applied to a producer cannot live longer than the producer's data (unless there is cloning)
/// * previous implementation of Producer and Consumer spent its time copying buffers
/// * the old Consumer was handling everything and buffering data. The new design has the producer handle data, but the consumer makes seeking decision
use std::io::{self,Read,SeekFrom};
use std::fs::File;
use std::path::Path;
use std::ptr;

//pub type Computation<I,O,S,E> = Box<Fn(S, Input<I>) -> (I,Consumer<I,O,S,E>)>;

#[derive(Debug,Clone)]
pub enum Input<I> {
  Element(I),
  Empty,
  Eof(Option<I>)
}

/// Stores a consumer's current computation state
#[derive(Debug,Clone)]
pub enum ConsumerState<O,E=(),M=()> {
  /// A value pf type O has been produced
  Done(O),
  /// An error of type E has been encountered
  Error(E),
  /// Continue applying, and pass a message of type M to the data source
  Continue(M)
}

/// The Consumer trait wraps a computation and its state
///
/// it depends on the input type I, the produced value's type O, the error type E, and the message type M
pub trait Consumer<I,O,E,M> {

  /// implement hndle for the current computation, returning the new state of the consumer
  fn handle(&mut self, input: Input<I>) -> &ConsumerState<O,E,M>;
  /// returns the current state
  fn state(&self) -> &ConsumerState<O,E,M>;

  /// return the computed value if it was generated
  fn run(&self) -> Option<&O> {
    if let &ConsumerState::Done(ref o) = self.state() {
      Some(o)
    } else {
      None
    }
  }
}

/// The producer wraps a data source, like file or network, and applies a consumer on it
///
/// it handles buffer copying and reallocation, to provide streaming patterns.
/// it depends on the input type I, and the message type M.
/// the consumer can change the way data is produced (for example, to seek in the source) by sending a message of type M.
pub trait Producer<I,M> {
  /// Applies a consumer once on the produced data, and return the consumer's state
  ///
  /// a new producer has to implement this method
  fn apply<'a, O,E>(& mut self, consumer: &'a mut Consumer<I,O,E,M>) -> &'a ConsumerState<O,E,M>;

  /// Applies a consumer once on the produced data, and returns the generated value if there is one
  fn run<'a,O,E>(&'a mut self, consumer: &'a mut Consumer<I,O,E,M>)   -> Option<&O> {
    if let &ConsumerState::Done(ref o) = self.apply(consumer) {
      Some(o)
    } else {
      None
    }
  }
  // fn fromFile, FromSocket, fromRead
}

/// ProducerRepeat takes a single value, and generates it at each step
pub struct ProducerRepeat<I:Copy> {
  value: I
}

impl<I:Copy,M> Producer<I,M> for ProducerRepeat<I> {
  fn apply<'a,O,E>(& mut self, consumer: &'a mut Consumer<I,O,E,M>) -> &'a ConsumerState<O,E,M> {
    if {
      if let &ConsumerState::Continue(_) = consumer.state() {
        true
      } else {
        false
      }
    }
    {
      consumer.handle(Input::Element(self.value))
    } else {
      consumer.state()
    }
  }
}

/// A MemProducer generates values from an in memory byte buffer
///
/// it generates data by chunks, and keeps track of how much was consumed.
/// It can receive messages of type `Move` to handle consumption and seeking
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

#[derive(Debug,Clone,PartialEq,Eq)]
pub enum Move {
  /// indcates how much data was consumed
  Consume(usize),
  /// indicates where in the input the consumer must seek
  Seek(SeekFrom)
}

impl<'x> Producer<&'x[u8],Move> for MemProducer<'x> {
  fn apply<'a,O,E>(& mut self, consumer: &'a mut Consumer<&'x[u8],O,E,Move>) -> &'a ConsumerState<O,E,Move> {
    if {
      if let &ConsumerState::Continue(ref m) = consumer.state() {
        match *m {
          Move::Consume(s) => {
            if self.length - self.index > s {
              self.index += s
            } else {
              panic!("cannot consume past the end of the buffer");
            }
          },
          Move::Seek(SeekFrom::Start(position)) => {
            if position as usize > self.length {
              self.index = self.length
            } else {
              self.index = position as usize
            }
          },
          Move::Seek(SeekFrom::Current(offset)) => {
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
            };
          },
          Move::Seek(SeekFrom::End(i)) => {
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
            };
          }
        }
        true
      } else {
        false
      }
    }
    {
      consumer.handle(Input::Element(&self.buffer[self.index..(self.index + self.chunk_size)]))
    } else {
      consumer.state()
    }
  }
}

enum FileProducerState {
  Normal,
  Error,
  Eof
}

pub struct FileProducer {//<'x> {
  size:  usize,
  file:  File,
  v:     Vec<u8>,
  start: usize,
  end:   usize,
  state: FileProducerState,
  //ph:    PhantomData<&'x[u8]>
}

impl FileProducer {
//impl<'x> FileProducer<'x> {
  pub fn new(filename: &str, buffer_size: usize) -> io::Result<FileProducer> {
    File::open(&Path::new(filename)).map(|f| {
      let mut v = Vec::with_capacity(buffer_size);
      //v.extend(repeat(0).take(buffer_size));
      FileProducer {size: buffer_size, file: f, v: v, start: 0, end: 0, state: FileProducerState::Normal }//, ph: PhantomData }
    })
  }

  fn refill(&mut self, sz: usize) -> Option<usize> {
    shift(&mut self.v, self.start, self.end);
    self.end = self.end - self.start;
    self.start = 0;
    match self.file.read(&mut self.v[self.end..]) {
      Err(_) => {
        self.state = FileProducerState::Error;
        None
      },
      Ok(n)  => {
        //println!("read: {} bytes\ndata:\n{}", n, (&self.v).to_hex(8));
        /*if n == 0 { 
          Eof(&self.v[..n])
        } else {
          Data(&self.v[..n])
        }*/
        if n == 0 {
          self.state = FileProducerState::Eof;
        }
        self.end += n;
        Some(0)
      }
    }
  }

  fn my_apply<'a,'x,O,E>(&'x mut self, consumer: &'a mut Consumer<&'x[u8],O,E,Move>) -> &'a ConsumerState<O,E,Move> {
    if {
      if let &ConsumerState::Continue(ref m) = consumer.state() {
        match *m {
          Move::Consume(s) => {
            if self.end - self.start > s {
              self.start += s
            } else {
              panic!("cannot consume past the end of the buffer");
            }
          },
          // FIXME: must seek in the file
          Move::Seek(SeekFrom::Start(position)) => {
            if position as usize > self.end {
              self.start = self.end
            } else {
              self.start = position as usize
            }
          },
          // FIXME: must seek in the file
          Move::Seek(SeekFrom::Current(offset)) => {
            let next = if offset >= 0 {
              (self.start as u64).checked_add(offset as u64)
            } else {
              (self.start as u64).checked_sub(-offset as u64)
            };
            match next {
              None    => None,
              Some(u) => {
                if u as usize > self.end {
                  self.start = self.end
                } else {
                  self.start = u as usize
                }
                Some(self.start as u64)
              }
            };
          },
          // FIXME: must seek in the file
          Move::Seek(SeekFrom::End(i)) => {
            let next = if i < 0 {
              (self.end as u64).checked_sub(-i as u64)
            } else {
              // std::io::SeekFrom documentation explicitly allows
              // seeking beyond the end of the stream, so we seek
              // to the end of the content if the offset is 0 or
              // greater.
              Some(self.end as u64)
            };
            match next {
              // std::io:SeekFrom documentation states that it `is an
              // error to seek before byte 0.' So it's the sensible
              // thing to refuse to seek on underflow.
              None => None,
              Some(u) => {
                self.start = u as usize;
                Some(u)
              }
            };
          }
        }
        true
      } else {
        false
      }
    }
    {
      consumer.handle(Input::Element(&self.v[self.start..self.end]))
    } else {
      consumer.state()
    }
  }
}

pub fn shift(s: &mut[u8], start: usize, end: usize) {
  if start > 0 {
    unsafe {
      let length = end - start;
      ptr::copy( (&s[start..end]).as_ptr(), (&mut s[..length]).as_mut_ptr(), length);
    }
  }
}


impl<'x> Producer<&'x [u8],Move> for FileProducer {

  fn apply<'a,O,E>(&mut self, consumer: &'a mut Consumer<&'x[u8],O,E,Move>) -> &'a ConsumerState<O,E,Move> {
    //self.my_apply(consumer)
    if {
      if let &ConsumerState::Continue(ref m) = consumer.state() {
        match *m {
          Move::Consume(s) => {
            if self.end - self.start > s {
              self.start += s
            } else {
              panic!("cannot consume past the end of the buffer");
            }
          },
          // FIXME: must seek in the file
          Move::Seek(SeekFrom::Start(position)) => {
            if position as usize > self.end {
              self.start = self.end
            } else {
              self.start = position as usize
            }
          },
          // FIXME: must seek in the file
          Move::Seek(SeekFrom::Current(offset)) => {
            let next = if offset >= 0 {
              (self.start as u64).checked_add(offset as u64)
            } else {
              (self.start as u64).checked_sub(-offset as u64)
            };
            match next {
              None    => None,
              Some(u) => {
                if u as usize > self.end {
                  self.start = self.end
                } else {
                  self.start = u as usize
                }
                Some(self.start as u64)
              }
            };
          },
          // FIXME: must seek in the file
          Move::Seek(SeekFrom::End(i)) => {
            let next = if i < 0 {
              (self.end as u64).checked_sub(-i as u64)
            } else {
              // std::io::SeekFrom documentation explicitly allows
              // seeking beyond the end of the stream, so we seek
              // to the end of the content if the offset is 0 or
              // greater.
              Some(self.end as u64)
            };
            match next {
              // std::io:SeekFrom documentation states that it `is an
              // error to seek before byte 0.' So it's the sensible
              // thing to refuse to seek on underflow.
              None => None,
              Some(u) => {
                self.start = u as usize;
                Some(u)
              }
            };
          }
        }
        true
      } else {
        false
      }
    }
    {
      consumer.handle(Input::Element(&self.v[self.start..self.end]))
    } else {
      consumer.state()
    }
  }
}


use std::marker::PhantomData;

/// MapConsumer takes a function S -> T and applies it on a consumer producing values of type S
pub struct MapConsumer<'a, C:'a ,R,S,T,E,M> {
  state:    ConsumerState<T,E,M>,
  consumer: &'a mut C,
  f:        Box<Fn(S) -> T>,
  input_type: PhantomData<R>
}

impl<'a,R,S:Clone,T,E:Clone,M:Clone,C:Consumer<R,S,E,M>> MapConsumer<'a,C,R,S,T,E,M> {
  fn new(c: &'a mut C, f: Box<Fn(S) -> T>) -> MapConsumer<'a,C,R,S,T,E,M> {
    //let state = c.state();
    let initial = match c.state() {
      &ConsumerState::Done(ref o)     => ConsumerState::Done(f(o.clone())),
      &ConsumerState::Error(ref e)    => ConsumerState::Error(e.clone()),
      &ConsumerState::Continue(ref m) => ConsumerState::Continue(m.clone())
    };

    MapConsumer {
      state:    initial,
      consumer: c,
      f:        f,
      input_type: PhantomData
    }
  }
}

impl<'a,R,S:Clone,T,E:Clone,M:Clone,C:Consumer<R,S,E,M>> Consumer<R,T,E,M> for MapConsumer<'a,C,R,S,T,E,M> {
  fn handle(&mut self, input: Input<R>) -> &ConsumerState<T,E,M> {
    let res:&ConsumerState<S,E,M> = self.consumer.handle(input);
    self.state = match res {
        &ConsumerState::Done(ref o)     => ConsumerState::Done((*self.f)(o.clone())),
        &ConsumerState::Error(ref e)    => ConsumerState::Error(e.clone()),
        &ConsumerState::Continue(ref m) => ConsumerState::Continue(m.clone())
      };
    &self.state
  }

  fn state(&self) -> &ConsumerState<T,E,M> {
    &self.state
  }
}

/// ChainConsumer takes a consumer C1 R -> S, and a consumer C2 S -> T, and makes a consumer R -> T by applying C2 on C1's result
pub struct ChainConsumer<'a,'b, C1:'a,C2:'b,R,S,T,E,M> {
  state:    ConsumerState<T,E,M>,
  consumer1: &'a mut C1,
  consumer2: &'b mut C2,
  input_type: PhantomData<R>,
  temp_type:  PhantomData<S>
}

impl<'a,'b,R,S:Clone,T:Clone,E:Clone,M:Clone,C1:Consumer<R,S,E,M>, C2:Consumer<S,T,E,M>> ChainConsumer<'a,'b,C1,C2,R,S,T,E,M> {
  fn new(c1: &'a mut C1, c2: &'b mut C2) -> ChainConsumer<'a,'b,C1,C2,R,S,T,E,M> {
    let initial = match c1.state() {
      &ConsumerState::Error(ref e)    => ConsumerState::Error(e.clone()),
      &ConsumerState::Continue(ref m) => ConsumerState::Continue(m.clone()),
      &ConsumerState::Done(ref o)     => match c2.handle(Input::Element(o.clone())) {
        &ConsumerState::Error(ref e)    => ConsumerState::Error(e.clone()),
        &ConsumerState::Continue(ref m) => ConsumerState::Continue(m.clone()),
        &ConsumerState::Done(ref o2)    => ConsumerState::Done(o2.clone())
      }
    };

    ChainConsumer {
      state:    initial,
      consumer1: c1,
      consumer2: c2,
      input_type: PhantomData,
      temp_type:  PhantomData
    }
  }
}

impl<'a,'b,R,S:Clone,T:Clone,E:Clone,M:Clone,C1:Consumer<R,S,E,M>, C2:Consumer<S,T,E,M>> Consumer<R,T,E,M> for ChainConsumer<'a,'b,C1,C2,R,S,T,E,M> {
  fn handle(&mut self, input: Input<R>) -> &ConsumerState<T,E,M> {
    let res:&ConsumerState<S,E,M> = self.consumer1.handle(input);
    self.state = match res {
        &ConsumerState::Error(ref e)    => ConsumerState::Error(e.clone()),
        &ConsumerState::Continue(ref m) => ConsumerState::Continue(m.clone()),
        &ConsumerState::Done(ref o)     => match (*self.consumer2).handle(Input::Element(o.clone())) {
          &ConsumerState::Error(ref e)    => ConsumerState::Error(e.clone()),
          &ConsumerState::Continue(ref m) => ConsumerState::Continue(m.clone()),
          &ConsumerState::Done(ref o2)    => ConsumerState::Done(o2.clone())
        }
      };
    &self.state
  }

  fn state(&self) -> &ConsumerState<T,E,M> {
    &self.state
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::IResult;
  use util::HexDisplay;
  use std::fmt::Debug;
  use std::io::SeekFrom;
  use std::str::from_utf8;

  #[derive(Debug)]
  struct AbcdConsumer<'a> {
    state: ConsumerState<&'a [u8], (), Move>
  }

  named!(abcd, tag!("abcd"));
  impl<'a> Consumer<&'a [u8], &'a [u8], (), Move> for AbcdConsumer<'a> {
    fn handle(&mut self, input: Input<&'a [u8]>) -> &ConsumerState<&'a [u8],(),Move> {
      match input {
        Input::Empty | Input::Eof(None) => &self.state,
        Input::Element(sl)              => {
          match abcd(sl) {
            IResult::Error(_) => {
              self.state = ConsumerState::Error(())
            },
            IResult::Incomplete(_) => {
              self.state = ConsumerState::Continue(Move::Consume(0))
            },
            IResult::Done(_,o) => {
              self.state = ConsumerState::Done(o)
            }
          };
          &self.state
        }
        Input::Eof(Some(sl))            => {
          match abcd(sl) {
            IResult::Error(_) => {
              self.state = ConsumerState::Error(())
            },
            IResult::Incomplete(_) => {
              // we cannot return incomplete on Eof
              self.state = ConsumerState::Error(())
            },
            IResult::Done(_,o) => {
              self.state = ConsumerState::Done(o)
            }
          };
          &self.state
        }
      }

    }

    fn state(&self) -> &ConsumerState<&'a [u8], (), Move> {
      &self.state
    }
  }

  #[test]
  fn mem() {
    let mut m = MemProducer::new(&b"abcdabcdabcdabcdabcd"[..], 8);

    let mut a  = AbcdConsumer { state: ConsumerState::Continue(Move::Consume(0)) };

    println!("apply {:?}", m.apply(&mut a));
    println!("apply {:?}", m.apply(&mut a));
    println!("apply {:?}", m.apply(&mut a));
    println!("apply {:?}", m.apply(&mut a));
    //assert!(false);
  }

  named!(efgh, tag!("efgh"));
  named!(ijkl, tag!("ijkl"));
  #[derive(Debug)]
  enum State {
    Initial,
    A,
    B,
    End,
    Error
  }
  #[derive(Debug)]
  struct StateConsumer<'a> {
    state: ConsumerState<&'a [u8], (), Move>,
    parsing_state: State
  }

  impl<'a> Consumer<&'a [u8], &'a [u8], (), Move> for StateConsumer<'a> {
    fn handle(&mut self, input: Input<&'a [u8]>) -> &ConsumerState<&'a [u8], (), Move> {
      match input {
        Input::Empty | Input::Eof(None) => &self.state,
        Input::Element(sl)              => {
          match self.parsing_state {
            State::Initial => match abcd(sl) {
              IResult::Error(_) => {
                self.parsing_state = State::Error;
                self.state = ConsumerState::Error(())
              },
              IResult::Incomplete(_) => {
                self.state = ConsumerState::Continue(Move::Consume(0))
              },
              IResult::Done(i,o) => {
                self.parsing_state = State::A;
                self.state = ConsumerState::Continue(Move::Consume(sl.offset(i)))
              }
            },
            State::A => match efgh(sl) {
              IResult::Error(_) => {
                self.parsing_state = State::Error;
                self.state = ConsumerState::Error(())
              },
              IResult::Incomplete(_) => {
                self.state = ConsumerState::Continue(Move::Consume(0))
              },
              IResult::Done(i,o) => {
                self.parsing_state = State::B;
                self.state = ConsumerState::Continue(Move::Consume(sl.offset(i)))
              }
            },
            State::B => match ijkl(sl) {
              IResult::Error(_) => {
                self.parsing_state = State::Error;
                self.state = ConsumerState::Error(())
              },
              IResult::Incomplete(_) => {
                self.state = ConsumerState::Continue(Move::Consume(0))
              },
              IResult::Done(_,o) => {
                self.parsing_state = State::End;
                self.state = ConsumerState::Done(o)
              }
            },
            _ => {
              self.parsing_state = State::Error;
              self.state = ConsumerState::Error(())
            }
          }
          &self.state
        }
        Input::Eof(Some(sl))           => {
          match self.parsing_state {
            State::Initial => match abcd(sl) {
              IResult::Error(_) => {
                self.parsing_state = State::Error;
                self.state = ConsumerState::Error(())
              },
              IResult::Incomplete(_) => {
                self.parsing_state = State::Error;
                self.state = ConsumerState::Error(())
              },
              IResult::Done(i,o) => {
                self.parsing_state = State::A;
                self.state = ConsumerState::Error(())
              }
            },
            State::A => match efgh(sl) {
              IResult::Error(_) => {
                self.parsing_state = State::Error;
                self.state = ConsumerState::Error(())
              },
              IResult::Incomplete(_) => {
                self.parsing_state = State::Error;
                self.state = ConsumerState::Error(())
              },
              IResult::Done(i,o) => {
                self.parsing_state = State::B;
                self.state = ConsumerState::Error(())
              }
            },
            State::B => match ijkl(sl) {
              IResult::Error(_) => {
                self.parsing_state = State::Error;
                self.state = ConsumerState::Error(())
              },
              IResult::Incomplete(_) => {
                self.parsing_state = State::Error;
                self.state = ConsumerState::Error(())
              },
              IResult::Done(_,o) => {
                self.parsing_state = State::End;
                self.state = ConsumerState::Done(o)
              }
            },
            _ => {
              self.parsing_state = State::Error;
              self.state = ConsumerState::Error(())
            }
          }
          &self.state
        }
      }

    }

    fn state(&self) -> &ConsumerState<&'a [u8], (), Move> {
      &self.state
    }
  }
  impl<'a> StateConsumer<'a> {
    fn parsing(&self) -> &State {
      &self.parsing_state
    }
  }

  #[test]
  fn mem2() {
    let mut m = MemProducer::new(&b"abcdefghijklabcdabcd"[..], 8);

    let mut a  = StateConsumer { state: ConsumerState::Continue(Move::Consume(0)), parsing_state: State::Initial };

    println!("apply {:?}", m.apply(&mut a));
    println!("state {:?}", a.parsing());
    println!("apply {:?}", m.apply(&mut a));
    println!("state {:?}", a.parsing());
    println!("apply {:?}", m.apply(&mut a));
    println!("state {:?}", a.parsing());
    println!("apply {:?}", m.apply(&mut a));
    println!("state {:?}", a.parsing());
    //assert!(false);
  }


  #[test]
  fn map() {
    let mut m = MemProducer::new(&b"abcdefghijklabcdabcd"[..], 8);

    let mut s = StateConsumer { state: ConsumerState::Continue(Move::Consume(0)), parsing_state: State::Initial };
    let mut a = MapConsumer::new(&mut s, Box::new(from_utf8));

    println!("apply {:?}", m.apply(&mut a));
    println!("apply {:?}", m.apply(&mut a));
    println!("apply {:?}", m.apply(&mut a));
    println!("apply {:?}", m.apply(&mut a));
    //assert!(false);
  }

  #[derive(Debug)]
  struct StrConsumer<'a> {
    state: ConsumerState<&'a str, (), Move>
  }

  impl<'a> Consumer<&'a [u8], &'a str, (), Move> for StrConsumer<'a> {
    fn handle(&mut self, input: Input<&'a [u8]>) -> &ConsumerState<&'a str, (), Move> {
      match input {
        Input::Empty | Input::Eof(None)           => &self.state,
        Input::Element(sl) | Input::Eof(Some(sl)) => {
          self.state = ConsumerState::Done(from_utf8(sl).unwrap());
          &self.state
        }
      }

    }

    fn state(&self) -> &ConsumerState<&'a str, (), Move> {
      &self.state
    }
  }

  #[test]
  fn chain() {
    let mut m = MemProducer::new(&b"abcdefghijklabcdabcd"[..], 8);

    let mut s1 = StateConsumer { state: ConsumerState::Continue(Move::Consume(0)), parsing_state: State::Initial };
    let mut s2 = StrConsumer { state: ConsumerState::Continue(Move::Consume(0)) };
    let mut a = ChainConsumer::new(&mut s1, &mut s2);

    println!("apply {:?}", m.apply(&mut a));
    println!("apply {:?}", m.apply(&mut a));
    println!("apply {:?}", m.apply(&mut a));
    println!("apply {:?}", m.apply(&mut a));
    //assert!(false);
  }

}
