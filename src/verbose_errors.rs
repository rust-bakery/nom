//! Error management
//!
//! Depending on a compilation flag, the content of the `Context` enum
//! can change. In the default case, it will only have one variant:
//! `Context::Code(I, ErrorKind<E=u32>)` (with `I` and `E` configurable).
//! It contains an error code and the input position that triggered it.
//!
//! If you activate the `verbose-errors` compilation flags, it will add another
//! variant to the enum: `Context::List(Vec<(I, ErrorKind<E>)>)`.
//! This variant aggregates positions and error codes as the code backtracks
//! through the nested parsers.
//! The verbose errors feature allows for very flexible error management:
//! you can know precisely which parser got to which part of the input.
//! The main drawback is that it is a lot slower than default error
//! management.
use util::{Convert, ErrorKind};
use lib::std::convert::From;
#[cfg(feature = "alloc")]
use lib::std::vec::Vec;

/// Contains the error that a parser can return
///
/// If you use the `verbose-errors` compilation feature,
/// `nom::Err` will be the enum defined here,
/// otherwise, it will amount to a `ErrorKind<E=u32>`.
///
/// It can represent a linked list of errors, indicating the path taken in the parsing tree, with corresponding position in the input data.
/// It depends on P, the input position (for a &[u8] parser, it would be a &[u8]), and E, the custom error type (by default, u32)
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Context<I, E = u32> {
  /// An error code, represented by an ErrorKind, which can contain a custom error code represented by E
  Code(I, ErrorKind<E>),
  List(Vec<(I, ErrorKind<E>)>),
}

impl<I, F, E: From<F>> Convert<Context<I, F>> for Context<I, E> {
  fn convert(c: Context<I, F>) -> Self {
    match c {
      Context::Code(i, e) => Context::Code(i, ErrorKind::convert(e)),
      Context::List(mut v) => Context::List(
        v.drain(..)
          .map(|(i, e)| (i, ErrorKind::convert(e)))
          .collect(),
      ),
    }
  }
}

impl<I, E> Context<I, E> {
  /// Convert Err into ErrorKind.
  ///
  /// This allows application code to use ErrorKind and stay independent from the verbose-errors features activation.
  pub fn into_error_kind(self) -> ErrorKind<E> {
    match self {
      Context::Code(_, kind) => kind,
      Context::List(mut v) => {
        let (_, kind) = v.remove(0);
        kind
      }
    }
  }
}

/*
impl<I,O,E> IResult<I,O,E> {
  /// Maps a `IResult<I, O, E>` to `IResult<I, O, N>` by appling a function
  /// to a contained `Error` value, leaving `Done` and `Incomplete` value
  /// untouched.
  #[inline]
  pub fn map_err<N, F>(self, f: F) -> IResult<I, O, N>
   where F: FnOnce(Err<I, E>) -> Err<I, N> {
    match self {
      Error(e)      => Error(f(e)),
      Incomplete(n) => Incomplete(n),
      Done(i, o)    => Done(i, o),
    }
  }

  /// Unwrap the contained `Error(I, E)` value, or panic if the `IResult` is not
  /// `Error`.
  pub fn unwrap_err(self) -> Err<I, E> {
    match self {
      Error(e)      => e,
      Done(_, _)    => panic!("unwrap_err() called on an IResult that is Done"),
      Incomplete(_) => panic!("unwrap_err() called on an IResult that is Incomplete"),
    }
  }

  /// Convert the IResult to a std::result::Result
  pub fn to_full_result(self) -> Result<O, IError<I,E>> {
    match self {
      Done(_, o)    => Ok(o),
      Incomplete(n) => Err(IError::Incomplete(n)),
      Error(e)      => Err(IError::Error(e))
    }
  }

  /// Convert the IResult to a std::result::Result
  pub fn to_result(self) -> Result<O, Err<I,E>> {
    match self {
      Done(_, o)    => Ok(o),
      Error(e)      => Err(e),
      Incomplete(_) => panic!("to_result() called on an IResult that is Incomplete")
    }
  }
}

#[cfg(feature = "std")]
use $crate::lib::std::any::Any;
#[cfg(feature = "std")]
use $crate::lib::std::{error,fmt};
#[cfg(feature = "std")]
use $crate::lib::std::fmt::Debug;
#[cfg(feature = "std")]
impl<P:Debug+Any,E:Debug+Any> error::Error for Err<P,E> {
  fn description(&self) -> &str {
    let kind = match *self {
      Err::Code(ref e) | Err::Node(ref e, _) | Err::Position(ref e, _) | Err::NodePosition(ref e, _, _) => e
    };
    kind.description()
  }
}

#[cfg(feature = "std")]
impl<P:fmt::Debug,E:fmt::Debug> fmt::Display for Err<P,E> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match *self {
      Err::Code(ref e) | Err::Node(ref e, _) => {
        write!(f, "{:?}", e)
      },
      Err::Position(ref e, ref p) | Err::NodePosition(ref e, ref p, _) => {
        write!(f, "{:?}:{:?}", p, e)
      }
    }
  }
}
*/

/// translate parser result from IResult<I,O,u32> to IResult<I,O,E> with a custom type
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::ErrorKind;
/// # use nom::Context;
/// # use nom::Err;
/// # fn main() {
///     #[derive(Debug,Clone,PartialEq)]
///     pub struct ErrorStr(String);
///
///     // Convert to IResult<&[u8], &[u8], ErrorStr>
///     impl From<u32> for ErrorStr {
///       fn from(i: u32) -> Self {
///         ErrorStr(format!("custom error code: {}", i))
///       }
///     }
///
///     // will add a Custom(42) error to the error chain
///     named!(err_test, add_return_error!(ErrorKind::Custom(42), tag!("abcd")));
///
///     // Convert to IResult<&[u8], &[u8], ErrorStr>
///     named!(parser<&[u8], &[u8], ErrorStr>, fix_error!(ErrorStr, err_test));
///
///     let a = &b"efghblah"[..];
///     //assert_eq!(parser(a), Err(Err::Error(Context::Code(a, ErrorKind::Custom(ErrorStr("custom error code: 42".to_string()))))));
///     let list = vec!((a, ErrorKind::Tag), (a, ErrorKind::Custom(ErrorStr("custom error code: 42".to_string()))));
///     assert_eq!(
///       parser(a),
///       Err(Err::Error(Context::List(list)))
///     );
/// # }
/// ```
#[macro_export]
macro_rules! fix_error (
  ($i:expr, $t:ty, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::lib::std::result::Result::*;
      use $crate::{Err,Convert,ErrorKind,Context};

      match $submac!($i, $($args)*) {
        Err(e)     => {
          let e2 = match e {
            Err::Error(err) => {
              let err2 = match err {
                Context::Code(i, code) => {
                  let code2: ErrorKind<$t> = ErrorKind::convert(code);
                  Context::Code(i, code2)
                },
                Context::List(mut v) => {
                  Context::List(v.drain(..).map(|(i, code)| {
                    let code2: ErrorKind<$t> = ErrorKind::convert(code);
                    (i, code2)
                  }).collect())
                }
              };
              Err::Error(err2)
            },
            Err::Failure(err) => {
              let err2 = match err {
                Context::Code(i, code) => {
                  let code2: ErrorKind<$t> = ErrorKind::convert(code);
                  Context::Code(i, code2)
                },
                Context::List(mut v) => {
                  Context::List(v.drain(..).map(|(i, code)| {
                    let code2: ErrorKind<$t> = ErrorKind::convert(code);
                    (i, code2)
                  }).collect())
                }
              };
              Err::Failure(err2)
            },
            Err::Incomplete(i) => Err::Incomplete(i),
          };
          Err(e2)
        },
        Ok((i, o)) => Ok((i, o)),
      }
    }
  );
  ($i:expr, $t:ty, $f:expr) => (
    fix_error!($i, $t, call!($f));
  );
);

/// `flat_map!(R -> IResult<R,S>, S -> IResult<S,T>) => R -> IResult<R, T>`
///
/// combines a parser R -> IResult<R,S> and
/// a parser S -> IResult<S,T> to return another
/// parser R -> IResult<R,T>
#[macro_export]
macro_rules! flat_map(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    flat_map!(__impl $i, $submac!($($args)*), $submac2!($($args2)*));
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    flat_map!(__impl $i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    flat_map!(__impl $i, call!($f), $submac!($($args)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    flat_map!(__impl $i, call!($f), call!($g));
  );
  (__impl $i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      use $crate::lib::std::result::Result::*;
      use $crate::{Err,Convert};

      ($submac!($i, $($args)*)).and_then(|(i,o)| {
        match $submac2!(o, $($args2)*) {
          Err(e)      => Err(Err::convert(e)),
          Ok((_, o2)) => Ok((i, o2))
        }
      })
    }
  );
);
