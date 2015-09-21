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
#[derive(Debug,Clone)]
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

use std::marker::PhantomData;

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
        Input::Empty | Input::Eof => &self.state,
        Input::Element(sl)        => {
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
