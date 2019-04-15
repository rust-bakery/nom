//! Error management
//!
//! Depending on a compilation flag, the content of the `Context` enum
//! can change. In the default case, it will only have one variant:
//! `Context::Code(I, ErrorKind<E=u32>)` (with `I` and `E` configurable).
//! It contains an error code and the input position that triggered it.
//!

use internal::{Err, IResult};
use util::ErrorKind;

pub trait ParseError<I>: Sized {
  fn from_error_kind(input: I, kind: ErrorKind) -> Self;

  fn append(input: I, kind: ErrorKind, other: Self) -> Self;

  fn from_char(input: I, _: char) -> Self {
    Self::from_error_kind(input, ErrorKind::Char)
  }

  fn or(self, other: Self) -> Self {
    other
  }

  fn add_context(_input: I, _ctx: &'static str, other: Self) -> Self {
    other
  }
}

impl<I> ParseError<I> for (I, ErrorKind) {
  fn from_error_kind(input: I, kind: ErrorKind) -> Self {
    (input, kind)
  }

  fn append(_: I, _: ErrorKind, other: Self) -> Self {
    other
  }
}

impl<I> ParseError<I> for () {
  fn from_error_kind(_: I, _: ErrorKind) -> Self { }

  fn append(_: I, _: ErrorKind, _: Self) -> Self { }
}

pub fn make_error<I, E: ParseError<I>>(input: I, kind: ErrorKind) -> E {
  E::from_error_kind(input, kind)
}

pub fn append_error<I, E: ParseError<I>>(input: I, kind: ErrorKind, other: E) -> E {
  E::append(input, kind, other)
}

#[cfg(feature = "alloc")]
#[derive(Clone,Debug,PartialEq)]
pub struct VerboseError<I> {
  pub errors: ::lib::std::vec::Vec<(I, VerboseErrorKind)>,
}

#[cfg(feature = "alloc")]
#[derive(Clone,Debug,PartialEq)]
pub enum VerboseErrorKind {
  Context(&'static str),
  Char(char),
  Nom(ErrorKind),
}

#[cfg(feature = "alloc")]
impl<I> ParseError<I> for VerboseError<I> {
  fn from_error_kind(input: I, kind: ErrorKind) -> Self {
    VerboseError {
      errors: vec![(input, VerboseErrorKind::Nom(kind))]
    }
  }

  fn append(input: I, kind: ErrorKind, mut other: Self) -> Self {
    other.errors.push((input, VerboseErrorKind::Nom(kind)));
    other
  }

  fn from_char(input: I, c: char) -> Self {
    VerboseError {
      errors: vec![(input, VerboseErrorKind::Char(c))]
    }
  }

  fn add_context(input: I, ctx: &'static str, mut other: Self) -> Self {
    other.errors.push((input, VerboseErrorKind::Context(ctx)));
    other
  }
}

#[cfg(feature = "alloc")]
pub fn context<I: Clone, E: ParseError<I>, F, O>(context: &'static str, f: F) -> impl FnOnce(I) -> IResult<I, O, E>
where
  F: Fn(I) -> IResult<I, O, E> {

    move |i: I| {
      match f(i.clone()) {
        Ok(o) => Ok(o),
        Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
        Err(Err::Error(e)) | Err(Err::Failure(e)) => {
          Err(Err::Failure(E::add_context(i, context, e)))
        }
      }
    }

}

/// creates a parse error from a `nom::ErrorKind`
/// and the position in the input
#[allow(unused_variables)]
#[macro_export(local_inner_macros)]
macro_rules! error_position(
  ($input:expr, $code:expr) => ({
    $crate::error::make_error($input, $code)
  });
);

/// creates a parse error from a `nom::ErrorKind`,
/// the position in the input and the next error in
/// the parsing tree.
#[allow(unused_variables)]
#[macro_export(local_inner_macros)]
macro_rules! error_node_position(
  ($input:expr, $code:expr, $next:expr) => ({
    $crate::error::append_error($input, $code, $next)
  });
);

/*

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
