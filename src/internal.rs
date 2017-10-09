//! Basic types to build the parsers

use self::IResult::*;
use self::Needed::*;

#[cfg(not(feature = "std"))]
use std::prelude::v1::*;

#[cfg(feature = "verbose-errors")]
use verbose_errors::Err;

#[cfg(not(feature = "verbose-errors"))]
use simple_errors::Err;

/// Contains information on needed data if a parser returned `Incomplete`
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
pub enum Needed {
  /// needs more data, but we do not know how much
  Unknown,
  /// contains the required data size
  Size(usize)
}

impl Needed {
  pub fn is_known(&self) -> bool {
    *self != Unknown
  }

  /// Maps a `Needed` to `Needed` by appling a function to a contained `Size` value.
  #[inline]
  pub fn map<F: FnOnce(usize) -> usize>(self, f: F) -> Needed {
    match self {
      Unknown => Unknown,
      Size(n) => Size(f(n)),
    }
  }
}

#[cfg(feature = "verbose-errors")]
/// Holds the result of parsing functions
///
/// It depends on I, the input type, O, the output type, and E, the error type (by default u32)
///
/// Depending on a compilation flag, the content of the `Error` variant
/// can change. By default, it will be a `ErrorKind<E=u32>` (with `E` configurable).
///
/// If you activate the `verbose-errors` compilation flags, it will be an
/// enum that contains an error code, optionally, an input position,
/// and an error sent by child parsers.
///
/// The verbose errors feature allows very flexible error management:
/// you can know precisely which parser got to which part of the input.
/// The main drawback is that it is a lot slower than default error
/// management.
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

#[cfg(not(feature = "verbose-errors"))]
/// Holds the result of parsing functions
///
/// It depends on I, the input type, O, the output type, and E, the error type (by default u32)
///
#[derive(Debug,PartialEq,Eq,Clone)]
pub enum IResult<I,O,E=u32> {
   /// indicates a correct parsing, the first field containing the rest of the unparsed data, the second field contains the parsed data
  Done(I,O),
  /// contains a Err, an enum that can indicate an error code, a position in the input, and a pointer to another error, making a list of errors in the parsing tree
  Error(Err<E>),
  /// Incomplete contains a Needed, an enum than can represent a known quantity of input data, or unknown
  Incomplete(Needed)
}

#[cfg(feature = "verbose-errors")]
/// This is the same as IResult, but without Done
///
/// This is used as the Error type when converting to std::result::Result
#[derive(Debug,PartialEq,Eq,Clone)]
pub enum IError<I,E=u32> {
  Error(Err<I,E>),
  Incomplete(Needed)
}

#[cfg(not(feature = "verbose-errors"))]
/// This is the same as IResult, but without Done
///
/// This is used as the Error type when converting to std::result::Result
#[derive(Debug,PartialEq,Eq,Clone)]
pub enum IError<E=u32> {
  Error(Err<E>),
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

  pub fn or(self, other: IResult<I, O, E>) -> IResult<I, O, E> {
    if self.is_done() {
      self
    } else {
      other
    }
  }

  /// Maps a `IResult<I, O, E>` to `IResult<I, N, E>` by appling a function
  /// to a contained `Done` value, leaving `Error` and `Incomplete` value
  /// untouched.
  #[inline]
  pub fn map<N, F: FnOnce(O) -> N>(self, f: F) -> IResult<I, N, E> {
    match self {
      Done(i, o)    => Done(i, f(o)),
      Error(e)      => Error(e),
      Incomplete(n) => Incomplete(n),
    }
  }

  /// Maps a `IResult<I, O, E>` to `IResult<I, O, E>` by appling a function
  /// to a contained `Incomplete` value, leaving `Done` and `Error` value
  /// untouched.
  #[inline]
  pub fn map_inc<F>(self, f: F) -> IResult<I, O, E>
   where F: FnOnce(Needed) -> Needed {
    match self {
      Error(e)      => Error(e),
      Incomplete(n) => Incomplete(f(n)),
      Done(i, o)    => Done(i, o),
    }
  }

  /// Unwrap the contained `Done(I, O)` value, or panic if the `IResult` is not
  /// `Done`.
  pub fn unwrap(self) -> (I, O) {
    match self {
      Done(i, o)    => (i, o),
      Incomplete(_) => panic!("unwrap() called on an IResult that is Incomplete"),
      Error(_)      => panic!("unwrap() called on an IResult that is Error")
    }
  }

  /// Unwrap the contained `Done(I, O)` value or a default if the `IResult` is not
  /// `Done`.
  pub fn unwrap_or(self, default: (I, O)) -> (I, O) {
    match self {
      Done(i, o)    => (i, o),
      Incomplete(_) => default,
      Error(_)      => default
    }
  }

  /// Unwrap the contained `Incomplete(n)` value, or panic if the `IResult` is not
  /// `Incomplete`.
  pub fn unwrap_inc(self) -> Needed {
    match self {
      Incomplete(n) => n,
      Done(_, _)    => panic!("unwrap_inc() called on an IResult that is Done"),
      Error(_)      => panic!("unwrap_inc() called on an IResult that is Error")
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

#[cfg(feature = "verbose-errors")]
/// creates a parse error from a `nom::ErrorKind`
#[macro_export]
macro_rules! error_code(
  ($code:expr) => ($crate::Err::Code($code));
);

#[cfg(not(feature = "verbose-errors"))]
/// creates a parse error from a `nom::ErrorKind`
#[macro_export]
macro_rules! error_code(
  ($code:expr) => ($code);
);

#[cfg(feature = "verbose-errors")]
/// creates a parse error from a `nom::ErrorKind`
/// and the next error in the parsing tree.
/// if "verbose-errors" is not activated,
/// it default to only the error code
#[macro_export]
macro_rules! error_node(
  ($code:expr, $next:expr) => {
    let next_errors = match $next {
      $crate::Err::Code(e) => {
        let mut v = ::std::vec::Vec::new();
        v.push($crate::Err::Code(e));
        v
      },
      $crate::Err::Position(e, p) => {
        let mut v = ::std::vec::Vec::new();
        v.push($crate::Err::Position(e,p));
        v
      },
      $crate::Err::Node(e, mut next) => {
        next.push($crate::Err::Code(e));
        next
      },
      $crate::Err::NodePosition(e, p, mut next) => {
        next.push($crate::Err::Position(e,p));
        next
      },
    };
    $crate::Err::Node($code, next_errors)
  };
);

#[cfg(not(feature = "verbose-errors"))]
/// creates a parse error from a `nom::ErrorKind`
/// and the next error in the parsing tree.
/// if "verbose-errors" is not activated,
/// it default to only the error code
#[allow(unused_variables)]
#[macro_export]
macro_rules! error_node(
  ($code:expr, $next:expr) => ($code);
);

#[cfg(feature = "verbose-errors")]
/// creates a parse error from a `nom::ErrorKind`
/// and the position in the input
/// if "verbose-errors" is not activated,
/// it default to only the error code
#[macro_export]
macro_rules! error_position(
  ($code:expr, $input:expr) => ($crate::Err::Position($code, $input));
);

#[cfg(not(feature = "verbose-errors"))]
/// creates a parse error from a `nom::ErrorKind`
/// and the position in the input
/// if "verbose-errors" is not activated,
/// it default to only the error code
#[allow(unused_variables)]
#[macro_export]
macro_rules! error_position(
  ($code:expr, $input:expr) => ($code);
);

#[cfg(feature = "verbose-errors")]
/// creates a parse error from a `nom::ErrorKind`,
/// the position in the input and the next error in
/// the parsing tree.
/// if "verbose-errors" is not activated,
/// it default to only the error code
#[macro_export]
macro_rules! error_node_position(
  ($code:expr, $input:expr, $next:expr) => {
    {
    let next_errors = match $next {
      $crate::Err::Code(e) => {
        let mut v = ::std::vec::Vec::new();
        v.push($crate::Err::Code(e));
        v
      },
      $crate::Err::Position(e, p) => {
        let mut v = ::std::vec::Vec::new();
        v.push($crate::Err::Position(e,p));
        v
      },
      $crate::Err::Node(e, mut next) => {
        next.push($crate::Err::Code(e));
        next
      },
      $crate::Err::NodePosition(e, p, mut next) => {
        next.push($crate::Err::Position(e,p));
        next
      }
    };
    $crate::Err::NodePosition($code, $input, next_errors)
    }
  }
);

#[cfg(not(feature = "verbose-errors"))]
/// creates a parse error from a `nom::ErrorKind`,
/// the position in the input and the next error in
/// the parsing tree.
/// if "verbose-errors" is not activated,
/// it default to only the error code
#[allow(unused_variables)]
#[macro_export]
macro_rules! error_node_position(
  ($code:expr, $input: expr, $next:expr) => ($code);
);

#[cfg(test)]
mod tests {
  use super::*;
  use util::ErrorKind;

  const REST: [u8; 0] = [];
  const DONE: IResult<&'static [u8], u32> = IResult::Done(&REST, 5);
  const ERROR: IResult<&'static [u8], u32> = IResult::Error(error_code!(ErrorKind::Tag));
  const INCOMPLETE: IResult<&'static [u8], u32> = IResult::Incomplete(Needed::Unknown);

  #[test]
  fn iresult_or() {
    assert_eq!(DONE.or(ERROR), DONE);
    assert_eq!(ERROR.or(DONE), DONE);
    assert_eq!(INCOMPLETE.or(ERROR), ERROR);
  }

  #[test]
  fn needed_map() {
    let unknown = Needed::Unknown;
    let size = Needed::Size(5);

    assert_eq!(size.map(|x| x * 2), Needed::Size(10));
    assert_eq!(unknown.map(|x| x * 2), Needed::Unknown);
  }

  #[test]
  fn iresult_map() {
    assert_eq!(DONE.map(|x| x * 2), IResult::Done(&b""[..], 10));
    assert_eq!(ERROR.map(|x| x * 2), IResult::Error(error_code!(ErrorKind::Tag)));
    assert_eq!(INCOMPLETE.map(|x| x * 2), IResult::Incomplete(Needed::Unknown));
  }

  #[test]
  fn iresult_map_inc() {
    let inc_unknown: IResult<&[u8], u32> = IResult::Incomplete(Needed::Unknown);
    let inc_size: IResult<&[u8], u32> = IResult::Incomplete(Needed::Size(5));

    assert_eq!(DONE.map_inc(|n| if let Needed::Size(i) = n {Needed::Size(i+1)} else {n}), IResult::Done(&b""[..], 5));
    assert_eq!(ERROR.map_inc(|n| if let Needed::Size(i) = n {Needed::Size(i+1)} else {n}), IResult::Error(error_code!(ErrorKind::Tag)));
    assert_eq!(inc_unknown.map_inc(|n| if let Needed::Size(i) = n {Needed::Size(i+1)} else {n}), IResult::Incomplete(Needed::Unknown));
    assert_eq!(inc_size.map_inc(|n| if let Needed::Size(i) = n {Needed::Size(i+1)} else {n}), IResult::Incomplete(Needed::Size(6)));
  }

  #[test]
  #[cfg(feature = "std")]
  fn iresult_map_err() {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Error(u32);

    let error_kind = error_code!(ErrorKind::Custom(Error(5)));

    assert_eq!(DONE.map_err(|_| error_kind.clone()), IResult::Done(&b""[..], 5));
    assert_eq!(ERROR.map_err(|x| {println!("err: {:?}", x); error_kind.clone()}), IResult::Error(error_kind.clone()));
    assert_eq!(INCOMPLETE.map_err(|x| {println!("err: {:?}", x); error_kind.clone()}), IResult::Incomplete(Needed::Unknown));
  }

  #[test]
  fn iresult_unwrap_on_done() {
    assert_eq!(DONE.unwrap(), (&b""[..], 5));
  }

  #[test]
  #[should_panic]
  fn iresult_unwrap_on_err() {
    ERROR.unwrap();
  }

  #[test]
  #[should_panic]
  fn iresult_unwrap_on_inc() {
    INCOMPLETE.unwrap();
  }

  #[test]
  fn iresult_unwrap_or_on_done() {
    assert_eq!(DONE.unwrap_or((&b""[..], 2)), (&b""[..], 5));
  }

  #[test]
  fn iresult_unwrap_or_on_err() {
    assert_eq!(ERROR.unwrap_or((&b""[..], 2)), (&b""[..], 2));
  }

  #[test]
  fn iresult_unwrap_or_on_inc() {
    assert_eq!(INCOMPLETE.unwrap_or((&b""[..], 2)), (&b""[..], 2));
  }

  #[test]
  #[should_panic]
  fn iresult_unwrap_err_on_done() {
    DONE.unwrap_err();
  }

  #[test]
  fn iresult_unwrap_err_on_err() {
    assert_eq!(ERROR.unwrap_err(), error_code!(ErrorKind::Tag));
  }

  #[test]
  #[should_panic]
  fn iresult_unwrap_err_on_inc() {
    INCOMPLETE.unwrap_err();
  }

  #[test]
  #[should_panic]
  fn iresult_unwrap_inc_on_done() {
    DONE.unwrap_inc();
  }

  #[test]
  #[should_panic]
  fn iresult_unwrap_inc_on_err() {
    ERROR.unwrap_inc();
  }

  #[test]
  fn iresult_unwrap_inc_on_inc() {
    assert_eq!(INCOMPLETE.unwrap_inc(), Needed::Unknown);
  }

  #[test]
  fn iresult_to_result() {
    assert_eq!(DONE.to_result(), Ok(5));
    assert_eq!(ERROR.to_result(), Err(error_code!(ErrorKind::Tag)));
  }

  #[test]
  #[should_panic]
  fn iresult_to_result_on_incomplete() {
    INCOMPLETE.to_result().unwrap();
  }

  #[test]
  fn iresult_to_full_result() {
    assert_eq!(DONE.to_full_result(), Ok(5));
    assert_eq!(INCOMPLETE.to_full_result(), Err(IError::Incomplete(Needed::Unknown)));
    assert_eq!(ERROR.to_full_result(), Err(IError::Error(error_code!(ErrorKind::Tag))));
  }
}
