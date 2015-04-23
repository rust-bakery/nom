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
//! # #[macro_use] extern crate nom;
//! # use nom::{IResult,Producer,ProducerState,FileProducer};
//! # use nom::IResult::*;
//! # use std::fmt::Debug;
//! # fn main() {
//!  use std::str;
//!  fn local_print<'a,T: Debug>(input: T) -> IResult<T, ()> {
//!    println!("{:?}", input);
//!    Done(input, ())
//!  }
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
//!

pub use self::util::*;
pub use self::internal::*;//{IResult, IResultClosure, GetInput, GetOutput};
pub use self::macros::*;
pub use self::producer::*;//{ProducerState,Producer,FileProducer,MemProducer};
pub use self::consumer::*;//{ConsumerState,Consumer};
pub use self::nom::*;

#[macro_use] pub mod util;
pub mod internal;
#[macro_use] pub mod macros;
#[macro_use] pub mod producer;
pub mod consumer;
#[macro_use] pub mod nom;

