//! Basic types to build the parsers

use self::Needed::*;

#[cfg(feature = "verbose-errors")]
use verbose_errors::Context;

#[cfg(not(feature = "verbose-errors"))]
use simple_errors::Context;

/// Holds the result of parsing functions
///
/// It depends on I, the input type, O, the output type, and E, the error type (by default u32)
///
/// The `Ok` side is an enum containing the remainder of the input (the part of the data that
/// was not parsed) and the produced value. The `Err` side contains an instance of `nom::Err`.
///
pub type IResult<I, O, E = u32> = Result<(I, O), Err<I, E>>;

/// Contains information on needed data if a parser returned `Incomplete`
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Needed {
  /// needs more data, but we do not know how much
  Unknown,
  /// contains the required data size
  Size(usize),
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

/// The `Err` enum indicates the parser was not successful
///
/// It has three cases:
///
/// * `Incomplete` indicates that more data is needed to decide. The `Needed` enum
/// can contain how many additional bytes are necessary. If you are sure your parser
/// is working on full data, you can wrap your parser with the `complete` combinator
/// to transform that case in `Error`
/// * `Error` means some parser did not succeed, but another one might (as an example,
/// when testing different branches of an `alt` combinator)
/// * `Failure` indicates an unrecoverable error. As an example, if you recognize a prefix
/// to decide on the next parser to apply, and that parser fails, you know there's no need
/// to try other parsers, you were already in the right branch, so the data is invalid
///
/// Depending on a compilation flag, the content of the `Context` enum
/// can change. In the default case, it will only have one variant:
/// `Context::Code(I, ErrorKind<E=u32>)` (with `I` and `E` configurable).
/// It contains an error code and the input position that triggered it.
///
/// If you activate the `verbose-errors` compilation flags, it will add another
/// variant to the enum: `Context::List(Vec<(I, ErrorKind<E>)>)`.
/// This variant aggregates positions and error codes as the code backtracks
/// through the nested parsers.
/// The verbose errors feature allows for very flexible error management:
/// you can know precisely which parser got to which part of the input.
/// The main drawback is that it is a lot slower than default error
/// management.
#[derive(Debug, Clone, PartialEq)]
pub enum Err<I, E = u32> {
  /// There was not enough data
  Incomplete(Needed),
  /// The parser had an error (recoverable)
  Error(Context<I, E>),
  /// The parser had an unrecoverable error: we got to the right
  /// branch and we know other branches won't work, so backtrack
  /// as fast as possible
  Failure(Context<I, E>),
}

#[cfg(feature = "std")]
use std::fmt;

#[cfg(feature = "std")]
impl<I, E> fmt::Display for Err<I, E>
where
  I: fmt::Debug,
  E: fmt::Debug,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{:?}", self)
  }
}

#[cfg(feature = "std")]
use std::error::Error;

#[cfg(feature = "std")]
impl<I, E> Error for Err<I, E>
where
  I: fmt::Debug,
  E: fmt::Debug,
{
  fn description(&self) -> &str {
    match self {
      &Err::Incomplete(..) => "there was not enough data",
      &Err::Error(Context::Code(_, ref error_kind)) | &Err::Failure(Context::Code(_, ref error_kind)) => error_kind.description(),
      #[cfg(feature = "verbose-errors")]
      &Err::Error(Context::List(..)) | &Err::Failure(Context::List(..)) => "list of errors",
    }
  }

  fn cause(&self) -> Option<&Error> {
    None
  }
}

use util::Convert;

impl<I, F, E: From<F>> Convert<Err<I, F>> for Err<I, E> {
  fn convert(e: Err<I, F>) -> Self {
    match e {
      Err::Incomplete(n) => Err::Incomplete(n),
      Err::Failure(c) => Err::Failure(Context::convert(c)),
      Err::Error(c) => Err::Error(Context::convert(c)),
    }
  }
}

impl<I, E> Err<I, E> {
  pub fn into_error_kind(self) -> ::util::ErrorKind<E> {
    match self {
      Err::Incomplete(_) => ::util::ErrorKind::Complete,
      Err::Failure(c) => c.into_error_kind(),
      Err::Error(c) => c.into_error_kind(),
    }
  }

  pub fn is_incomplete(&self) -> bool {
    match *self {
      Err::Incomplete(_) => true,
      _ => false,
    }
  }
}

/*
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
}*/

#[cfg(feature = "verbose-errors")]
/// creates a parse error from a `nom::ErrorKind`
/// and the position in the input
/// if "verbose-errors" is not activated,
/// it default to only the error code
#[macro_export]
macro_rules! error_position(
  ($input: expr, $code:expr) => ({
    $crate::Context::Code($input, $code)
  });
);

#[cfg(not(feature = "verbose-errors"))]
/// creates a parse error from a `nom::ErrorKind`
/// and the position in the input
/// if "verbose-errors" is not activated,
/// it default to only the error code
#[allow(unused_variables)]
#[macro_export]
macro_rules! error_position(
  ($input:expr, $code:expr) => ({
    $crate::Context::Code($input, $code)
  });
);

#[cfg(feature = "verbose-errors")]
/// creates a parse error from a `nom::ErrorKind`,
/// the position in the input and the next error in
/// the parsing tree.
/// if "verbose-errors" is not activated,
/// it default to only the error code
#[macro_export]
macro_rules! error_node_position(
  ($input:expr, $code:expr, $next:expr) => {
    {
    let mut error_vec = match $next {
      $crate::Context::Code(i, e) => {
        let mut v = $crate::lib::std::vec::Vec::new();
        v.push((i, e));
        v
      },
      $crate::Context::List(v) => {
        v
      },
    };

    error_vec.push(($input, $code));
    $crate::Context::List(error_vec)
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
  ($input:expr, $code:expr, $next:expr) => ({
    fn unify_types<T>(_: &T, _: &T) {}
    let res = $crate::Context::Code($input, $code);
    unify_types(&res, &$next);
    res
  });
);

#[cfg(test)]
mod tests {

  /*
  const REST: [u8; 0] = [];
  const DONE: IResult<&'static [u8], u32> = Ok((&REST, 5));
  const ERROR: IResult<&'static [u8], u32> = Err(Err::Error(Context::Code(&b""[..], ErrorKind::Tag)));
  const INCOMPLETE: IResult<&'static [u8], u32> = Err(Err::Incomplete(Needed::Unknown));
  */

  /*
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
  */
}
