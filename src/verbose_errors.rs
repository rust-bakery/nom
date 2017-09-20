//! Error management
//!
//! there are two ways to handle errors in nom. The first one,
//! activated by default, uses the `nom::ErrorKind<E=u32>` enum
//! in the error branch of `IResult`. This enum can hold either
//! a parser specific error code, or a custom error type you
//! specify.
//!
//! If you need more advanced error management, you can activate
//! the "verbose-errors" compilation feature, which will give you
//! the error system available in nom 1.0. The verbose errors
//! accumulate error codes and positions as you backtrack through
//! the parser tree. From there, you can precisely identify which
//! parts of the input triggered the error case.
//!
//! Please note that the verbose error management is a bit slower
//! than the simple one.
use util::ErrorKind;
use internal::{IResult, IError};
use internal::IResult::*;

/// Contains the error that a parser can return
///
/// If you use the `verbose-errors` compilation feature,
/// `nom::Err` will be the enum defined here,
/// otherwise, it will amount to a `ErrorKind<E=u32>`.
///
/// It can represent a linked list of errors, indicating the path taken in the parsing tree, with corresponding position in the input data.
/// It depends on P, the input position (for a &[u8] parser, it would be a &[u8]), and E, the custom error type (by default, u32)
#[derive(Debug,PartialEq,Eq,Clone)]
pub enum Err<P,E=u32>{
  /// An error code, represented by an ErrorKind, which can contain a custom error code represented by E
  Code(ErrorKind<E>),
  /// An error code, and the next error
  Node(ErrorKind<E>, Vec<Err<P,E>>),
  /// An error code, and the input position
  Position(ErrorKind<E>, P),
  /// An error code, the input position and the next error
  NodePosition(ErrorKind<E>, P, Vec<Err<P,E>>)
}

impl<P,E> Err<P,E> {
  /// Convert Err into ErrorKind.
  ///
  /// This allows application code to use ErrorKind and stay independent from the verbose-errors features activation.
  pub fn into_error_kind(self) -> ErrorKind<E> {
    match self {
      Err::Code(kind) => kind,
      Err::Node(kind, _) => kind,
      Err::Position(kind, _) => kind,
      Err::NodePosition(kind, _, _) => kind,
    }
  }
}

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
use std::any::Any;
#[cfg(feature = "std")]
use std::{error,fmt};
#[cfg(feature = "std")]
use std::fmt::Debug;
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


/// translate parser result from IResult<I,O,u32> to IResult<I,O,E> with a custom type
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use std::collections;
/// # use nom::IResult::Error;
/// # use nom::Err::{Position,NodePosition};
/// # use nom::ErrorKind;
/// # fn main() {
///     // will add a Custom(42) error to the error chain
///     named!(err_test, add_return_error!(ErrorKind::Custom(42), tag!("abcd")));
///     // Convert to IREsult<&[u8], &[u8], &str>
///     named!(parser<&[u8], &[u8], &str>, add_return_error!(ErrorKind::Custom("custom error message"), fix_error!(&str, err_test)));
///
///     let a = &b"efghblah"[..];
///     let res_a = parser(a);
///     assert_eq!(res_a,  Error(NodePosition( ErrorKind::Custom("custom error message"), a, vec!(Position(ErrorKind::Fix, a)))));
/// # }
/// ```
#[macro_export]
macro_rules! fix_error (
  ($i:expr, $t:ty, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
        $crate::IResult::Error(e) => {
          let err = match e {
            $crate::Err::Code($crate::ErrorKind::Custom(_)) |
              $crate::Err::Node($crate::ErrorKind::Custom(_), _) => {
              let e: $crate::ErrorKind<$t> = $crate::ErrorKind::Fix;
              $crate::Err::Code(e)
            },
            $crate::Err::Position($crate::ErrorKind::Custom(_), p) |
              $crate::Err::NodePosition($crate::ErrorKind::Custom(_), p, _) => {
              let e: $crate::ErrorKind<$t> = $crate::ErrorKind::Fix;
              $crate::Err::Position(e, p)
            },
            $crate::Err::Code(_) |
              $crate::Err::Node(_, _) => {
              let e: $crate::ErrorKind<$t> = $crate::ErrorKind::Fix;
              $crate::Err::Code(e)
            },
            $crate::Err::Position(_, p) |
              $crate::Err::NodePosition(_, p, _) => {
              let e: $crate::ErrorKind<$t> = $crate::ErrorKind::Fix;
              $crate::Err::Position(e, p)
            },
          };
          $crate::IResult::Error(err)
        }
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
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done(i, o)                          => match $submac2!(o, $($args2)*) {
          $crate::IResult::Error(e)                                 => {
            let err = match e {
              $crate::Err::Code(k) | $crate::Err::Node(k, _) | $crate::Err::Position(k, _) | $crate::Err::NodePosition(k, _, _) => {
                $crate::Err::Position(k, $i)
              }
            };
            $crate::IResult::Error(err)
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown)      => $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::IResult::Incomplete($crate::Needed::Size(ref i2)) => $crate::IResult::Incomplete($crate::Needed::Size(*i2)),
          $crate::IResult::Done(_, o2)                              => $crate::IResult::Done(i, o2)
        }
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    flat_map!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $f:expr, $g:expr) => (
    flat_map!($i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    flat_map!($i, call!($f), $submac!($($args)*));
  );
);
