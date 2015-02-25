//! Nom, eating data byte by byte
//!
//! The goal is to make a parser combinator library that is safe,
//! supports streaming (push and pull), and as much as possible zero copy.
//!
//! The code is available on [Github](https://github.com/Geal/nom)
//!
//! # Example
//!
//! ```ignore
//!  use std::str;
//!  fn local_print<'a,T: Debug>(input: T) -> IResult<T, ()> {
//!    println!("{:?}", input);
//!    Done(input, ())
//!  }
//!  // create a data producer from a file
//!  FileProducer::new("links.txt", 20).map(|producer: FileProducer| {
//!    let mut p = producer;
//!
//!    // create the parsing function
//!    fn parser(par: IResult<(),&[u8]>) -> IResult<&[u8],()> {
//!      // convert byte array to a string, then print it
//!      par.map_res(str::from_utf8).flat_map(local_print);
//!
//!      // return a dummy answer
//!      Done(b"", ())
//!    }
//!
//!    // adapt the parsing function to the producer
//!    pusher!(push, parser);
//!    // get started
//!    push(&mut p);
//!  });
//! ```
//!

#![feature(fs,path,io,core,collections)]

pub use self::util::*;
pub use self::internal::*;//{IResult, IResultClosure, GetInput, GetOutput};
pub use self::map::*;
pub use self::producer::*;//{ProducerState,Producer,FileProducer,MemProducer};
pub use self::consumer::*;//{ConsumerState,Consumer};
pub use self::nom::*;

pub mod util;
pub mod internal;
#[macro_use] pub mod producer;
pub mod consumer;
pub mod map;
#[macro_use] pub mod nom;

