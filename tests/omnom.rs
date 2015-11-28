#![cfg(feature = "stream")]

#[macro_use]
extern crate nom;

use nom::{Producer,Consumer,ConsumerState,Input,Move,MemProducer,IResult,HexDisplay};

#[derive(PartialEq,Eq,Debug)]
enum State {
  Beginning,
  Middle,
  End,
  Done,
  Error
}

struct TestConsumer {
  state:   State,
  c_state: ConsumerState<usize,(),Move>,
  counter: usize,
}

named!(om_parser,                        tag!("om"));
named!(nomnom_parser<&[u8],Vec<&[u8]> >, many1!(tag!("nom")));
named!(end_parser,                       tag!("kthxbye"));

impl<'a> Consumer<&'a[u8], usize, (), Move> for TestConsumer {
  fn state(&self) -> &ConsumerState<usize,(),Move> {
    &self.c_state
  }

  fn handle(&mut self, input: Input<&'a [u8]>) -> &ConsumerState<usize,(),Move> {
    match self.state {
      State::Beginning => {
        match input {
          Input::Empty | Input::Eof(None) => {
            self.state   = State::Error;
            self.c_state = ConsumerState::Error(());
          },
          Input::Element(sl) | Input::Eof(Some(sl)) => {
            match om_parser(sl) {
              IResult::Error(_)      => {
                self.state   = State::Error;
                self.c_state = ConsumerState::Error(());
              },
              IResult::Incomplete(n) => {
                self.c_state = ConsumerState::Continue(Move::Await(n));
              },
              IResult::Done(i,_)     => {
                self.state = State::Middle;
                self.c_state = ConsumerState::Continue(Move::Consume(sl.offset(i)));
              }
            }
          }
        }
      },
      State::Middle    => {
        match input {
          Input::Empty | Input::Eof(None) => {
            self.state   = State::Error;
            self.c_state = ConsumerState::Error(());
          },
          Input::Element(sl) | Input::Eof(Some(sl)) => {
            match nomnom_parser(sl) {
              IResult::Error(_)      => {
                self.state   = State::End;
                self.c_state = ConsumerState::Continue(Move::Consume(0));
              },
              IResult::Incomplete(n) => {
                println!("Middle got Incomplete({:?})", n);
                self.c_state = ConsumerState::Continue(Move::Await(n));
              },
              IResult::Done(i,noms_vec)     => {
                self.counter = self.counter + noms_vec.len();
                self.state = State::Middle;
                self.c_state = ConsumerState::Continue(Move::Consume(sl.offset(i)));
              }
            }
          }
        }
      },
      State::End       => {
        match input {
          Input::Empty | Input::Eof(None) => {
            self.state   = State::Error;
            self.c_state = ConsumerState::Error(());
          },
          Input::Element(sl) | Input::Eof(Some(sl)) => {
            match end_parser(sl) {
              IResult::Error(_)      => {
                self.state   = State::Error;
                self.c_state = ConsumerState::Error(());
              },
              IResult::Incomplete(n) => {
                self.c_state = ConsumerState::Continue(Move::Await(n));
              },
              IResult::Done(i,_)     => {
                self.state = State::Done;
                self.c_state = ConsumerState::Done(Move::Consume(sl.offset(i)), self.counter);
              }
            }
          }
        }
      },
    State::Done | State::Error     => {
        // this should not be called
        self.state = State::Error;
        self.c_state = ConsumerState::Error(())
      }
    };
    &self.c_state
  }
}

#[test]
fn nom1() {
  let mut p = MemProducer::new(&b"omnomkthxbye"[..], 8);
  let mut c = TestConsumer{state: State::Beginning, counter: 0, c_state: ConsumerState::Continue(Move::Consume(0))};
  while let &ConsumerState::Continue(Move::Consume(_)) = p.apply(&mut c) {
  }

  assert_eq!(c.counter, 1);
  assert_eq!(c.state, State::Done);
}

#[test]
fn nomnomnom() {
  let mut p = MemProducer::new(&b"omnomnomnomkthxbye"[..], 9);
  let mut c = TestConsumer{state: State::Beginning, counter: 0, c_state: ConsumerState::Continue(Move::Consume(0))};
  while let &ConsumerState::Continue(_) = p.apply(&mut c) {
  }

  assert_eq!(c.counter, 3);
  assert_eq!(c.state, State::Done);
}

#[test]
fn no_nomnom() {
  let mut p = MemProducer::new(&b"omkthxbye"[..], 8);
  let mut c = TestConsumer{state: State::Beginning, counter: 0, c_state: ConsumerState::Continue(Move::Consume(0))};
  while let &ConsumerState::Continue(_) = p.apply(&mut c) {
  }

  assert_eq!(c.counter, 0);
  assert_eq!(c.state, State::Done);
}

/*
#[test]
fn impolite() {
  let mut p = MemProducer::new(&b"omnomnomnom"[..], 11);
  let mut c = TestConsumer{state: State::Beginning, counter: 0, c_state: ConsumerState::Continue(Move::Consume(0))};
  while let &ConsumerState::Continue(cont) = p.apply(&mut c) {
    println!("continue {:?}", cont);
  }

  assert_eq!(c.counter, 3);
  assert_eq!(c.state, State::End);
}
*/
