//! Basic types to build the parsers

use self::IResult::*;
use util::ErrorKind;

#[cfg(feature = "core")]
use std::prelude::v1::*;
use std::boxed::Box;

/*
/// (Experimental) Closure used to hold the temporary state of resumable parsing
pub type IResultClosure<'a,I,O> = Box<FnMut(I) -> IResult<I,O> +'a>;

//cf libcore/fmt/mod.rs:674
impl<'a,I,O> Debug for IResultClosure<'a,I,O> {
  fn fmt(&self, f: &mut Formatter) -> Result {
    Display::fmt("closure", f)
  }
}

impl<'a,I:PartialEq,O:PartialEq> PartialEq for IResultClosure<'a,I,O> {
  #[allow(unused_variables)]
  fn eq<'b>(&self, other: &IResultClosure<'b,I,O>) -> bool {
    false
  }

  #[allow(unused_variables)]
  fn ne<'b>(&self, other: &IResultClosure<'b,I,O>) -> bool {
    false
  }
}

impl<'a,I:Eq,O:Eq> Eq for IResultClosure<'a,I,O> {}
*/
//type IResultClosure<'a,I,O> = |I|:'a -> IResult<'a,I,O>;
//type IResultClosure<'a,I,O> = Fn<I, IResult<'a,I,O>>;

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
  //Incomplete(proc(I):'a -> IResult<I,O>)
  /// Incomplete contains a Needed, an enum than can represent a known quantity of input data, or unknown
  Incomplete(Needed)
  //Incomplete(Box<FnMut(I) -> IResult<I,O>>)
  //Incomplete(IResultClosure<I,O>)
  //Incomplete(|I|:'a -> IResult<'a,I,O>)
  //Incomplete(fn(I) -> IResult<'a,I,O>)
}

impl<I,O> IResult<I,O> {
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

impl<'a,I,O> GetInput<&'a[I]> for IResult<&'a[I],O> {
  fn remaining_input(&self) -> Option<&'a[I]> {
    match *self {
      Done(ref i,_) => Some(*i),
      _             => None
    }
  }
}

impl<'a,O> GetInput<()> for IResult<(),O> {
  fn remaining_input(&self) -> Option<()> {
    match *self {
      Done((),_) => Some(()),
      _          => None
    }
  }
}

impl<'a,I,O> GetOutput<&'a[O]> for IResult<I,&'a[O]> {
  fn output(&self) -> Option<&'a[O]> {
    match *self {
      Done(_, ref o) => Some(*o),
      _              => None
    }
  }
}

impl<'a,I> GetOutput<()> for IResult<I,()> {
  fn output(&self) -> Option<()> {
    match *self {
      Done(_,()) => Some(()),
      _          => None
    }
  }
}

