//! Data consumers
//!
//! The goal of data producers is to parse data depending on the previous result.
//! It can be used to selectively seek in a file.
//!
//! ## Example
//!
//! This consumer will take 4 samples from the input, print them, then stop
//!
//! ```rust
//!  use nom::{MemProducer,Consumer,ConsumerState};
//!  use std::str;
//!
//!  struct TestPrintConsumer {
//!    counter: usize
//!  }
//!
//!  impl TestPrintConsumer {
//!    fn new() -> TestPrintConsumer {
//!      TestPrintConsumer { counter: 0 }
//!    }
//!  }
//!
//!  // Return ConsumerState::Await if it needs more data, or ConsumerDone when it ends
//!  impl Consumer for TestPrintConsumer {
//!    fn consume(&mut self, input: &[u8]) -> ConsumerState {
//!      println!("{} -> {}", self.counter, str::from_utf8(input).unwrap());
//!      self.counter = self.counter + 1;
//!      if self.counter <=4 {
//!        ConsumerState::Await
//!      } else {
//!        ConsumerState::ConsumerDone
//!      }
//!    }
//!  }
//!
//!  // It can consume data directly from a producer
//!  let mut p = MemProducer::new("abcdefghijklmnopqrstuvwx".as_bytes(), 4);
//!  let mut c = TestPrintConsumer::new();
//!  c.run(&mut p);
//! ```

use self::ConsumerState::*;
use producer::Producer;
use producer::ProducerState::*;
use internal::Err;

/// Holds the current state of the consumer
///
/// * Await if more data is needed
///
/// * ConsumerDone if the consumer does not need anymore data to be parsed
///
/// * ConsumerError when something went wrong
#[derive(Debug,PartialEq,Eq,Copy)]
pub enum ConsumerState {
  Await,
  //Incomplete,
  ConsumerDone,
  ConsumerError(Err)
}

/// Implement the consume method, taking a byte array as input and returning a consumer state
///
/// The run function takes care of continuing or not
pub trait Consumer {
  fn consume(&mut self, input: &[u8]) -> ConsumerState;
  fn run(&mut self, producer: &mut Producer) {
    let mut acc: Vec<u8> = Vec::new();
    //let mut v2: Vec<u8>  = Vec::new();
    loop {
      let state = producer.produce();
      match state {
        Data(v) => {
          println!("got data");
          acc.push_all(v)
        },
        Eof([])  => {
          println!("eof empty");
          break;
        }
        Eof(v) => {
          println!("eof with {} bytes", v.len());
          acc.push_all(v)
        }
        _ => {break;}
      }
      //v2.push_all(acc.as_slice());
      //match consumer.consume(v2.as_slice()) {
      match self.consume(acc.as_slice()) {
        ConsumerError(e) => {
          println!("consumer error, stopping: {}", e);
        },
        ConsumerDone => {
          println!("data, done");
          acc.clear();
          //acc.push_all(i);
          break;
        },
        Await => {
          println!("await");
          acc.clear();
          //acc.push_all(i);
        }
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use super::ConsumerState::*;
  use producer::MemProducer;
  use std::str;

  struct TestPrintConsumer {
    counter: usize
  }

  impl TestPrintConsumer {
    fn new() -> TestPrintConsumer {
      TestPrintConsumer { counter: 0 }
    }
  }

  impl Consumer for TestPrintConsumer {
    fn consume(&mut self, input: &[u8]) -> ConsumerState {
      println!("{} -> {}", self.counter, str::from_utf8(input).unwrap());
      self.counter = self.counter + 1;
      if self.counter <=4 {
        Await
      } else {
        ConsumerDone
      }
    }
  }

  #[test]
  fn pull() {
    let mut p = MemProducer::new("abcdefghijklmnopqrstuvwx".as_bytes(), 4);
    let mut c = TestPrintConsumer::new();
    c.run(&mut p);
  }
}
