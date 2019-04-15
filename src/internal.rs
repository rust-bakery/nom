//! Basic types to build the parsers

use self::Needed::*;
use error::ErrorKind;

/// Holds the result of parsing functions
///
/// It depends on I, the input type, O, the output type, and E, the error type (by default u32)
///
/// The `Ok` side is an enum containing the remainder of the input (the part of the data that
/// was not parsed) and the produced value. The `Err` side contains an instance of `nom::Err`.
///
pub type IResult<I, O, E=(I,ErrorKind)> = Result<(I, O), Err<E>>;

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
#[derive(Debug, Clone, PartialEq)]
pub enum Err<E> {
  /// There was not enough data
  Incomplete(Needed),
  /// The parser had an error (recoverable)
  Error(E),
  /// The parser had an unrecoverable error: we got to the right
  /// branch and we know other branches won't work, so backtrack
  /// as fast as possible
  Failure(E),
}

/*
#[cfg(feature = "std")]
use std::fmt;

#[cfg(feature = "std")]
impl<E> fmt::Display for Err<E>
where
  E: fmt::Debug,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{:?}", self)
  }
}

#[cfg(feature = "std")]
use std::error::Error;

#[cfg(feature = "std")]
impl<E> Error for Err<E>
where
  I: fmt::Debug,
  E: fmt::Debug,
{
  fn description(&self) -> &str {
    match self {
      &Err::Incomplete(..) => "there was not enough data",
      &Err::Error(Context::Code(_, ref error_kind)) | &Err::Failure(Context::Code(_, ref error_kind)) => error_kind.description(),
    }
  }

  fn cause(&self) -> Option<&Error> {
    None
  }
}
*/

use util::Convert;

impl<F, E: From<F>> Convert<Err<F>> for Err<E> {
  fn convert(e: Err<F>) -> Self {
    match e {
      Err::Incomplete(n) => Err::Incomplete(n),
      Err::Failure(c) => Err::Failure(c.into()),
      Err::Error(c) => Err::Error(c.into()),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use error::ErrorKind;

  #[macro_export]
  macro_rules! assert_size (
    ($t:ty, $sz:expr) => (
      assert_eq!(::lib::std::mem::size_of::<$t>(), $sz);
    );
  );

  #[test]
  #[cfg(target_pointer_width = "64")]
  fn size_test() {
    assert_size!(IResult<&[u8], &[u8], (&[u8], u32)>, 40);
    assert_size!(IResult<&str, &str, u32>, 40);
    assert_size!(Needed, 16);
    assert_size!(Err<u32>, 24);
    assert_size!(ErrorKind, 1);
  }

}
