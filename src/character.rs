/// Character level parsers

use internal::{IResult,Needed};
use traits::{AsChar,InputIter,InputLength,Slice};
use std::ops::RangeFrom;
use traits::{need_more,AtEof};

/// matches one of the provided characters
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
/// named!(simple<char>, one_of!(&b"abc"[..]));
/// assert_eq!(simple(b"a123"), Ok((&b"123"[..], 'a')));
///
/// named!(a_or_b<&str, char>, one_of!("ab汉"));
/// assert_eq!(a_or_b("汉jiosfe"), Ok(("jiosfe", '汉')));
/// # }
/// ```
#[macro_export]
macro_rules! one_of (
  ($i:expr, $inp: expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,Needed};

      use $crate::Slice;
      use $crate::AsChar;
      use $crate::FindToken;
      use $crate::InputIter;

      match ($i).iter_elements().next().map(|c| {
        (c, $inp.find_token(c))
      }) {
        None             => $crate::need_more($i, Needed::Size(1)),
        Some((_, false)) => Err(Err::Error(error_position!($crate::ErrorKind::OneOf::<u32>, $i))),
        //the unwrap should be safe here
        Some((c, true))  => Ok(( $i.slice(c.len()..), $i.iter_elements().next().unwrap().as_char() ))
      }
    }
  );
);

/// matches anything but the provided characters
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::{Err,ErrorKind};
/// # fn main() {
/// named!(no_letter_a<char>, none_of!(&b"abc"[..]));
/// assert_eq!(no_letter_a(b"123"), Ok((&b"23"[..], '1')));
///
/// named!(err_on_single_quote<char>, none_of!(&b"'"[..]));
/// assert_eq!(err_on_single_quote(b"'jiosfe"), Err(Err::Error(error_position!(ErrorKind::NoneOf, &b"'jiosfe"[..]))));
/// # }
/// ```
#[macro_export]
macro_rules! none_of (
  ($i:expr, $inp: expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,Needed};

      use $crate::Slice;
      use $crate::AsChar;
      use $crate::FindToken;
      use $crate::InputIter;

      match ($i).iter_elements().next().map(|c| {
        (c, !$inp.find_token(c))
      }) {
        None             => $crate::need_more($i, Needed::Size(1)),
        Some((_, false)) => Err(Err::Error(error_position!($crate::ErrorKind::NoneOf::<u32>, $i))),
        //the unwrap should be safe here
        Some((c, true))  => Ok(( $i.slice(c.len()..), $i.iter_elements().next().unwrap().as_char() ))
      }
    }
  );
);

/// matches one character: `char!(char) => &[u8] -> IResult<&[u8], char>
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::{Err,ErrorKind};
/// # fn main() {
/// named!(match_letter_a<char>, char!('a'));
/// assert_eq!(match_letter_a(b"abc"), Ok((&b"bc"[..],'a')));
///
/// assert_eq!(match_letter_a(b"123cdef"), Err(Err::Error(error_position!(ErrorKind::Char, &b"123cdef"[..]))));
/// # }
/// ```
#[macro_export]
macro_rules! char (
  ($i:expr, $c: expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,Needed};

      use $crate::Slice;
      use $crate::AsChar;
      use $crate::InputIter;

      match ($i).iter_elements().next().map(|c| {
        (c, c.as_char() == $c)
      }) {
        None             => $crate::need_more($i, Needed::Size(1)),
        Some((_, false)) => {
          let e: $crate::ErrorKind<u32> = $crate::ErrorKind::Char;
          Err(Err::Error($crate::Context::Code($i, e)))
        },
        //the unwrap should be safe here
        Some((c, true))  => Ok(( $i.slice(c.len()..), $i.iter_elements().next().unwrap().as_char() ))
      }
    }
  );
);

named!(#[doc="Matches a newline character '\\n'"], pub newline<char>, char!('\n'));

named!(#[doc="Matches a tab character '\\t'"], pub tab<char>, char!('\t'));

/// matches one byte as a character. Note that the input type will
/// accept a `str`, but not a `&[u8]`, unlike many other nom parsers.
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::anychar;
/// # fn main() {
/// assert_eq!(anychar("abc"), Ok(("bc",'a')));
/// # }
/// ```
pub fn anychar<T>(input: T) -> IResult<T, char> where
  T: InputIter+InputLength+Slice<RangeFrom<usize>>+AtEof,
  <T as InputIter>::Item: AsChar {
  if input.input_len() == 0 {
    need_more(input, Needed::Size(1))
  } else {
    Ok((input.slice(1..), input.iter_elements().next().expect("slice should contain at least one element").as_char()))
  }
}

#[cfg(test)]
mod tests {
  use internal::Err;
  use util::ErrorKind;

  #[test]
  fn one_of() {
    named!(f<char>, one_of!("ab"));

    let a = &b"abcd"[..];
    assert_eq!(f(a),Ok((&b"bcd"[..], 'a')));

    let b = &b"cde"[..];
    assert_eq!(f(b), Err(Err::Error(error_position!(ErrorKind::OneOf, b))));

    named!(utf8(&str) -> char,
      one_of!("+\u{FF0B}"));

    assert!(utf8("+").is_ok());
    assert!(utf8("\u{FF0B}").is_ok());
  }

  #[test]
  fn none_of() {
    named!(f<char>, none_of!("ab"));

    let a = &b"abcd"[..];
    assert_eq!(f(a), Err(Err::Error(error_position!(ErrorKind::NoneOf, a))));

    let b = &b"cde"[..];
    assert_eq!(f(b),Ok((&b"de"[..], 'c')));
  }

  #[test]
  fn char() {
    named!(f<char>, char!('c'));

    let a = &b"abcd"[..];
    assert_eq!(f(a), Err(Err::Error(error_position!(ErrorKind::Char, a))));

    let b = &b"cde"[..];
    assert_eq!(f(b),Ok((&b"de"[..], 'c')));
  }

}
