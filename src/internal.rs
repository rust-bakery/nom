//! Basic types to build the parsers

use self::IResult::*;
use util::ErrorKind;

#[cfg(feature = "core")]
use std::prelude::v1::*;
use std::boxed::Box;

/// Contains the error that a parser can return
///
/// It can represent a linked list of errors, indicating the path taken in the parsing tree, with corresponding position in the input data.
/// It depends on P, the input position (for a &[u8] parser, it would be a &[u8]), and E, the custom error type (by default, u32)
#[derive(Debug,PartialEq,Eq,Clone)]
pub enum Err<P,E=u32>{
  /// An error code, represented by an ErrorKind, which can contain a custom error code represented by E
  Code(ErrorKind<E>),
  /// An error code, and the next error
  Node(ErrorKind<E>, Box<Err<P,E>>),
  /// An error code, and the input position
  Position(ErrorKind<E>, P),
  /// An error code, the input position and the next error
  NodePosition(ErrorKind<E>, P, Box<Err<P,E>>)
}

/// Contains information on needed data if a parser returned `Incomplete`
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
pub enum Needed {
  /// needs more data, but we do not know how much
  Unknown,
  /// contains the required data size
  Size(usize)
}

/// Holds the result of parsing functions
///
/// It depends on I, the input type, O, the output type, and E, the error type (by default u32)
///
#[derive(Debug,PartialEq,Eq,Clone)]
pub enum IResult<I,O,E=u32> {
   /// indicates a correct parsing, the first field containing the rest of the unparsed data, the second field contains the parsed data
  Done(I,O),
  /// contains a Err, an enum that can indicate an error code, a position in the input, and a pointer to another error, making a list of errors in the parsing tree
  Error(Err<I,E>),
  /// Incomplete contains a Needed, an enum than can represent a known quantity of input data, or unknown
  Incomplete(Needed)
}

impl<I,O,E> IResult<I,O,E> {
  pub fn is_done(&self) -> bool {
    match *self {
      Done(_,_) => true,
      _         => false
    }
  }

  pub fn is_err(&self) -> bool {
    match *self {
      Error(_) => true,
      _        => false
    }
  }

  pub fn is_incomplete(&self) -> bool {
    match *self {
      Incomplete(_) => true,
      _             => false
    }
  }
}

pub trait GetInput<I> {
  fn remaining_input(&self) -> Option<I>;
}

pub trait GetOutput<O> {
  fn output(&self) -> Option<O>;
}

impl<'a,I,O,E> GetInput<&'a[I]> for IResult<&'a[I],O,E> {
  fn remaining_input(&self) -> Option<&'a[I]> {
    match *self {
      Done(ref i,_) => Some(*i),
      _             => None
    }
  }
}

impl<O,E> GetInput<()> for IResult<(),O,E> {
  fn remaining_input(&self) -> Option<()> {
    match *self {
      Done((),_) => Some(()),
      _          => None
    }
  }
}

impl<'a,O,E> GetInput<&'a str> for IResult<&'a str,O,E> {
  fn remaining_input(&self) -> Option<&'a str> {
    match *self {
      Done(ref i,_) => Some(*i),
      _          => None
    }
  }
}

impl<'a,I,O,E> GetOutput<&'a[O]> for IResult<I,&'a[O],E> {
  fn output(&self) -> Option<&'a[O]> {
    match *self {
      Done(_, ref o) => Some(*o),
      _              => None
    }
  }
}

impl<I,E> GetOutput<()> for IResult<I,(),E> {
  fn output(&self) -> Option<()> {
    match *self {
      Done(_,()) => Some(()),
      _          => None
    }
  }
}

impl<'a,I,E> GetOutput<&'a str> for IResult<I,&'a str,E> {
  fn output(&self) -> Option<&'a str> {
    match *self {
      Done(_,ref o) => Some(*o),
      _          => None
    }
  }
}
