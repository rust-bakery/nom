//! Error management
//!
//! Depending on a compilation flag, the content of the `Context` enum
//! can change. In the default case, it will only have one variant:
//! `Context::Code(I, ErrorKind<E=u32>)` (with `I` and `E` configurable).
//! It contains an error code and the input position that triggered it.
//!

/*
#[derive(Debug, Clone, PartialEq)]
pub enum Context<I, E = u32> {
  Code(I, ErrorKind<E>),
}

impl<I, H: From<I>, F, E: From<F>> Convert<Context<I, F>> for Context<H, E> {
  fn convert(c: Context<I, F>) -> Self {
    let Context::Code(i, e) = c;

    Context::Code(i.into(), ErrorKind::convert(e))
  }
}

*/

/*
impl<I,O,E> IResult<I,O,E> {
  /// Maps a `IResult<I, O, E>` to `IResult<I, O, N>` by appling a function
  /// to a contained `Error` value, leaving `Done` and `Incomplete` value
  /// untouched.
  #[inline]
  pub fn map_err<N, F>(self, f: F) -> IResult<I, O, N>
   where F: FnOnce(Err<E>) -> Err<N> {
    match self {
      Error(e)      => Error(f(e)),
      Incomplete(n) => Incomplete(n),
      Done(i, o)    => Done(i, o),
    }
  }

  /// Unwrap the contained `Error(E)` value, or panic if the `IResult` is not
  /// `Error`.
  pub fn unwrap_err(self) -> Err<E> {
    match self {
      Error(e)      => e,
      Done(_, _)    => panic!("unwrap_err() called on an IResult that is Done"),
      Incomplete(_) => panic!("unwrap_err() called on an IResult that is Incomplete"),
    }
  }

  /// Convert the IResult to a std::result::Result
  pub fn to_full_result(self) -> Result<O, IError<E>> {
    match self {
      Done(_, o)    => Ok(o),
      Incomplete(n) => Err(IError::Incomplete(n)),
      Error(e)      => Err(IError::Error(e))
    }
  }

  /// Convert the IResult to a std::result::Result, or panic if the `IResult` is `Incomplete`
  pub fn to_result(self) -> Result<O, Err<E>> {
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
impl<E: fmt::Debug+Any> error::Error for Err<E> {
  fn description(&self) -> &str {
    self.description()
  }
}

#[cfg(feature = "std")]
impl<E: fmt::Debug> fmt::Display for Err<E> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.description())
  }
}
*/

//FIXME: error rewrite
/// translate parser result from IResult<I,O,u32> to IResult<I,O,E> with a custom type
///
/// ```
/// # //FIXME
/// # #[macro_use] extern crate nom;
/// # use nom::IResult;
/// # use std::convert::From;
/// # use nom::Err;
/// # use nom::ErrorKind;
/// # fn main() {
/// #    /*
/// #    // will add a Custom(42) error to the error chain
/// #    named!(err_test, add_return_error!(ErrorKind::Custom(42u32), tag!("abcd")));
/// #
/// #    #[derive(Debug,Clone,PartialEq)]
/// #    pub struct ErrorStr(String);
/// #
/// #    // Convert to IResult<&[u8], &[u8], ErrorStr>
/// #    impl From<u32> for ErrorStr {
/// #      fn from(i: u32) -> Self {
/// #        ErrorStr(format!("custom error code: {}", i))
/// #      }
/// #    }
/// #
/// #    named!(parser<&[u8], &[u8], ErrorStr>,
/// #        fix_error!(ErrorStr, err_test)
/// #      );
/// #
/// #    let a = &b"efghblah"[..];
/// #    assert_eq!(parser(a), Err(Err::Error(Context::Code(a, ErrorKind::Custom(ErrorStr("custom error code: 42".to_string()))))));
/// # */
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! fix_error (
  ($i:expr, $t:ty, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::lib::std::result::Result::*;
      use $crate::Err;

      match $submac!($i, $($args)*) {
        Ok((i,o)) => Ok((i,o)),
        Err(e) => {
          let e2 = match e {
            Err::Error(err) => {
              /*
              let Context::Code(i, code) = err;
              let code2: ErrorKind<$t> = ErrorKind::convert(code);
              Err::Error(Context::Code(i, code2))
              */
              Err::Error(err.into())
            },
            Err::Failure(err) => {
              /*
              let Context::Code(i, code) = err;
              let code2: ErrorKind<$t> = ErrorKind::convert(code);
              Err::Failure(Context::Code(i, code2))
              */
              Err::Failure(err.into())
            },
            Err::Incomplete(e) => Err::Incomplete(e),
          };
          Err(e2)
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
#[macro_export(local_inner_macros)]
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
      use $crate::Err;

      ($submac!($i, $($args)*)).and_then(|(i,o)| {
        match $submac2!(o, $($args2)*) {
          Err(e)      => Err(e.into()),
          Ok((_, o2)) => Ok((i, o2))
        }
      })
    }
  );
);
