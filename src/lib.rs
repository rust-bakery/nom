//! Nom, eating data byte by byte
//!
//! The goal is to make a parser combinator library that is safe,
//! supports streaming (push and pull), and as much as possible zero copy.
//!
//! The code is available on [Github](https://github.com/Geal/nom)
//!
//! # Example
//!
//! ```
//! #[macro_use]
//! extern crate nom;
//!
//! use nom::{Consumer,ConsumerState,MemProducer,IResult};
//! use nom::IResult::*;
//!
//! // Parser definition
//!
//! named!( om_parser,                   tag!( "om" ) );
//! named!( nomnom_parser< &[u8], Vec<&[u8]> >, many1!( tag!( "nom" ) ) );
//! named!( end_parser,                  tag!( "kthxbye")  );
//!
//!
//! // Streaming parsing and state machine
//!
//! #[derive(PartialEq,Eq,Debug)]
//! enum State {
//!   Beginning,
//!   Middle,
//!   End,
//!   Done
//! }
//!
//! struct TestConsumer {
//!   state:   State,
//!   counter: usize
//! }
//!
//! impl Consumer for TestConsumer {
//!   fn consume(&mut self, input: &[u8]) -> ConsumerState {
//!     match self.state {
//!       State::Beginning => {
//!         match om_parser(input) {
//!           Error(_)      => ConsumerState::ConsumerError(0),
//!           Incomplete(_) => ConsumerState::Await(0, 2),
//!           Done(_,_)     => {
//!             // "om" was recognized, get to the next state
//!             self.state = State::Middle;
//!             ConsumerState::Await(2, 3)
//!           }
//!         }
//!       },
//!       State::Middle    => {
//!         match nomnom_parser(input) {
//!           Error(a)         => {
//!             // the "nom" parser failed, let's get to the next state
//!             self.state = State::End;
//!             ConsumerState::Await(0, 7)
//!           },
//!           Incomplete(_)    => ConsumerState::Await(0, 3),
//!           Done(i,noms_vec) => {
//!             // we got a few noms, let's count them and continue
//!             self.counter = self.counter + noms_vec.len();
//!             ConsumerState::Await(input.len() - i.len(), 3)
//!           }
//!         }
//!       },
//!       State::End       => {
//!         match end_parser(input) {
//!           Error(_)      => ConsumerState::ConsumerError(0),
//!           Incomplete(_) => ConsumerState::Await(0, 7),
//!           Done(_,_)     => {
//!             // we recognized the suffix, everything was parsed correctly
//!             self.state = State::Done;
//!             ConsumerState::ConsumerDone
//!           }
//!         }
//!       },
//!       State::Done      => {
//!         // this should not be called
//!         ConsumerState::ConsumerError(42)
//!       }
//!     }
//!   }
//!
//!   fn failed(&mut self, error_code: u32) {
//!     println!("failed with error code: {}", error_code);
//!   }
//!
//!   fn end(&mut self) {
//!     println!("we counted {} noms", self.counter);
//!   }
//! }
//!
//! fn main() {
//!   let mut p = MemProducer::new(b"omnomnomnomkthxbye", 4);
//!   let mut c = TestConsumer{state: State::Beginning, counter: 0};
//!   c.run(&mut p);
//!
//!   assert_eq!(c.counter, 3);
//!   assert_eq!(c.state, State::Done);
//! }
//! ```
//!

#![cfg_attr(feature = "core", feature(no_std))]
#![cfg_attr(feature = "core", feature(core))]
#![cfg_attr(feature = "core", feature(collections))]
#![cfg_attr(feature = "core", no_std)]

#[macro_use]
#[cfg(feature = "core")]
extern crate core;
#[cfg(feature = "core")]
extern crate collections;

#[cfg(feature = "core")]
mod std {
#[macro_use]
  pub use core::{fmt, iter, option, ops, slice, mem};
  pub use collections::{boxed, vec, string};
  pub mod prelude {
    pub use core::prelude as v1;
  }
}

pub use self::util::*;
pub use self::internal::*;//{IResult, IResultClosure, GetInput, GetOutput};
pub use self::macros::*;
#[cfg(not(feature = "core"))]
pub use self::producer::*;//{ProducerState,Producer,FileProducer,MemProducer};
#[cfg(not(feature = "core"))]
pub use self::consumer::*;//{ConsumerState,Consumer};
#[cfg(not(feature = "core"))]
pub use self::iterator::*;

pub use self::nom::*;


#[macro_use] mod util;
mod internal;
#[macro_use] mod macros;

#[macro_use]
#[cfg(not(feature = "core"))]
mod producer;
#[cfg(not(feature = "core"))]
mod consumer;

#[cfg(not(feature = "core"))]
mod iterator;

#[macro_use] mod nom;

