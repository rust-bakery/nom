// Context:
// * Rust n'a pas de TCO, donc on ne peut pas faire de récursion facilement
// * la gestion de l'ownership fait que le résultat d'une passe sur le
//     contenu du Producer ne vivra pas plus longtemps que son buffer (sauf si on cpone les données)
// * les Producers et Consumers actuels passent leur temps à copier des buffers,
//     je veux limiter ça au Producer

use std::io::SeekFrom;

pub type Computation<I,O,S,E> = Box<Fn(S, Input<I>) -> (I,Consumer<I,O,S,E>)>;

pub enum Input<I> {
  Element(I),
  Empty,
  Eof
}

// I pour input, O pour output, S pour State, E pour Error
// S et E ont des types par défaut, donc on n'est pasobligé de les préciser
#[derive(Debug)]
pub enum ConsumerState<O,E=(),M=()> {
  Done(O),     // output
  Error(E),
  Continue(M) // on passe un état au lieu de passer une closure
  //Continue(S, Computation<I,O,S,E>) // on passe un état au lieu de passer une closure
}

pub trait Consumer<I,O,E,M> {

  fn handle(&mut self, input: Input<I>) -> &ConsumerState<O,E,M>;
  fn state(&self) -> &ConsumerState<O,E,M>;

  fn run(&self) -> Option<&O> {
    if let &ConsumerState::Done(ref o) = self.state() {
      Some(o)
    } else {
      None
    }
  }
}

pub trait Producer<I,M> {
  fn apply<'a,O,E>(&'a mut self, consumer: &'a mut Consumer<I,O,E,M>) -> &ConsumerState<O,E,M>; // applique le consumer sur la donnée contenue actuellement dans le producer
  fn run<'a, O,E>(&'a mut self, consumer: &'a mut Consumer<I,O,E,M>)   -> Option<&O> {
    if let &ConsumerState::Done(ref o) = self.apply(consumer) {
      Some(o)
    } else {
      None
    }
  }
  // fn fromFile, FromSocket, fromRead
}

pub struct ProducerRepeat<I:Copy> {
  value: I
}

impl<I:Copy,M> Producer<I,M> for ProducerRepeat<I> {
  fn apply<'a, O,E>(&'a mut self, consumer: &'a mut Consumer<I,O,E,M>) -> & ConsumerState<O,E,M> {
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
  Consume(usize),
  Seek(SeekFrom)
}

impl<'x> Producer<&'x[u8],Move> for MemProducer<'x> {
  fn apply<'a, O,E>(&'a mut self, consumer: &'a mut Consumer<&'x[u8],O,E,Move>) -> & ConsumerState<O,E,Move> {
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

#[cfg(test)]
mod tests {
  use super::*;
  use internal::IResult;
  use util::HexDisplay;
  use std::fmt::Debug;
  use std::io::SeekFrom;

  #[derive(Debug)]
  struct AbcdConsumer<'a> {
    state: ConsumerState<&'a [u8], (), Move>
  }

  named!(abcd, tag!("abcd"));
  impl<'a> Consumer<&'a [u8], &'a [u8], (), Move> for AbcdConsumer<'a> {
    fn handle(&mut self, input: Input<&'a [u8]>) -> &ConsumerState<&'a [u8],(),Move> {
      match input {
        Input::Empty | Input::Eof => &self.state,
        Input::Element(sl)        => {
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
    assert!(false);
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
        Input::Empty | Input::Eof => &self.state,
        Input::Element(sl)        => {
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
    assert!(false);
  }
}
/*
macro_rules! consumer (
  ($name:ident<$i:ty,$o:ty,$s:ty,$e:ty>, $f:ident, $initial:expr) => {
    struct $name {
      state: ConsumerState<$i, $o, $s, $e>
    }

    impl $name {
      fn state(&self) -> ConsumerState<
    }

  };
    ($name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: $i ) -> $crate::IResult<$i,$o> {
            $submac!(i, $($args)*)
        }
    );
);
*/
