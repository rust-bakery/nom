//! Basic types to build the parsers

use self::IResult::*;
use std::fmt::{Debug,Display,Formatter,Result};

/// Errortype. A integer for now
pub type Err = u32;
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

#[derive(Debug,PartialEq,Eq)]
pub enum Needed {
  Unknown,
  Size(u32)
}

/// Holds the result of parsing functions
///
/// It depends on I, the input types, and O, the output type.
///
/// * Done indicates a correct parsing, the first field containing the rest of the unparsed data,
/// the second field contains the parsed data
///
/// * Error is currently a u32, but should be updated to indicate which parser had a problem,
/// a description, and an eventual stack of parser to know which path failed
///
/// * Incomplete will hold the closure used to restart the computation once more data is available.
/// Current attemps at implementation of Incomplete are progressing, but slowed down by lifetime problems
#[derive(Debug,PartialEq,Eq)]
pub enum IResult<I,O> {
  Done(I,O),
  Error(Err),
  //Incomplete(proc(I):'a -> IResult<I,O>)
  Incomplete(Needed)
  //Incomplete(Box<FnMut(I) -> IResult<I,O>>)
  //Incomplete(IResultClosure<I,O>)
  //Incomplete(|I|:'a -> IResult<'a,I,O>)
  //Incomplete(fn(I) -> IResult<'a,I,O>)
}

impl<I,O> IResult<I,O> {
  pub fn is_done(&self) -> bool {
    match self {
      &Done(_,_) => true,
      _          => false
    }
  }

  pub fn is_err(&self) -> bool {
    match self {
      &Error(_) => true,
      _         => false
    }
  }

  pub fn is_incomplete(&self) -> bool {
    match self {
      &Incomplete(_) => true,
      _              => false
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
    match self {
      &Done(ref i,_) => Some(*i),
      _          => None
    }
  }
}

impl<'a,O> GetInput<()> for IResult<(),O> {
  fn remaining_input(&self) -> Option<()> {
    match self {
      &Done((),_) => Some(()),
      _          => None
    }
  }
}

impl<'a,I,O> GetOutput<&'a[O]> for IResult<I,&'a[O]> {
  fn output(&self) -> Option<&'a[O]> {
    match self {
      &Done(_, ref o) => Some(*o),
      _          => None
    }
  }
}

impl<'a,I> GetOutput<()> for IResult<I,()> {
  fn output(&self) -> Option<()> {
    match self {
      &Done(_,()) => Some(()),
      _          => None
    }
  }
}

