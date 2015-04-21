
#[macro_use]
extern crate nom;

use nom::{Consumer,ConsumerState,MemProducer,IResult,Needed};
use nom::IResult::*;
use nom::Err::*;

#[derive(PartialEq,Eq,Debug)]
enum State {
  Beginning,
  Middle,
  End,
  Done
}

struct TestConsumer {
  state:   State,
  counter: usize,
}

named!(om_parser,                        tag!("om"));
named!(nomnom_parser<&[u8],Vec<&[u8]> >, many1!(tag!("nom")));
named!(end_parser,                       tag!("kthxbye"));

impl Consumer for TestConsumer {
  fn consume(&mut self, input: &[u8]) -> ConsumerState {
    match self.state {
      State::Beginning => {
        match om_parser(input) {
          Error(a)      => ConsumerState::ConsumerError(0),
          Incomplete(_) => ConsumerState::Await(0, 2),
          Done(_,_)     => {
            self.state = State::Middle;
            ConsumerState::Await(2, 3)
          }
        }
      },
      State::Middle    => {
        match nomnom_parser(input) {
          Error(_)         => {
            self.state = State::End;
            ConsumerState::Await(0, 7)
          },
          Incomplete(_)    => ConsumerState::Await(0, 3),
          Done(i,noms_vec) => {
            self.counter = self.counter + noms_vec.len();
            ConsumerState::Await(input.len() - i.len(), 3)
          }
        }
      },
      State::End       => {
        match end_parser(input) {
          Error(a)      => ConsumerState::ConsumerError(0),
          Incomplete(_) => ConsumerState::Await(0, 7),
          Done(_,_)     => {
            self.state = State::Done;
            ConsumerState::ConsumerDone
          }
        }
      },
      State::Done      => {
        // this should not be called
        ConsumerState::ConsumerError(42)
      }
    }
  }

  fn end(&mut self) {
    println!("counted {} noms", self.counter);
  }
}

#[test]
fn nom1() {
  let mut p = MemProducer::new(&b"omnomkthxbye"[..], 4);
  let mut c = TestConsumer{state: State::Beginning, counter: 0};
  c.run(&mut p);

  assert_eq!(c.counter, 1);
  assert_eq!(c.state, State::Done);
}

#[test]
fn nomnomnom() {
  let mut p = MemProducer::new(&b"omnomnomnomkthxbye"[..], 4);
  let mut c = TestConsumer{state: State::Beginning, counter: 0};
  c.run(&mut p);

  assert_eq!(c.counter, 3);
  assert_eq!(c.state, State::Done);
}

#[test]
fn no_nomnom() {
  let mut p = MemProducer::new(&b"omkthxbye"[..], 4);
  let mut c = TestConsumer{state: State::Beginning, counter: 0};
  c.run(&mut p);

  assert_eq!(c.counter, 0);
  assert_eq!(c.state, State::Done);
}

#[test]
fn impolite() {
  let mut p = MemProducer::new(&b"omnomnomnom"[..], 4);
  let mut c = TestConsumer{state: State::Beginning, counter: 0};
  c.run(&mut p);

  assert_eq!(c.counter, 3);
  assert_eq!(c.state, State::Middle);
}

