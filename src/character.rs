/// Character level parsers

use internal::{IResult,Needed};
use traits::{AsChar,InputIter,InputLength,Slice};
use std::ops::RangeFrom;

/// matches one of the provided characters
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult;
/// # fn main() {
/// named!(simple<char>, one_of!(&b"abc"[..]));
/// assert_eq!(simple(b"a123"), IResult::Done(&b"123"[..], 'a'));
///
/// named!(a_or_b<&str, char>, one_of!("ab汉"));
/// assert_eq!(a_or_b("汉jiosfe"), IResult::Done("jiosfe", '汉'));
/// # }
/// ```
#[macro_export]
macro_rules! one_of (
  ($i:expr, $inp: expr) => (
    {
      use $crate::Slice;
      use $crate::AsChar;
      use $crate::FindToken;
      use $crate::InputIter;

      match ($i).iter_elements().next().map(|c| {
        (c, c.find_token($inp))
      }) {
        None             => $crate::IResult::Incomplete::<_, _>($crate::Needed::Size(1)),
        Some((_, false)) => $crate::IResult::Error(error_position!($crate::ErrorKind::OneOf, $i)),
        //the unwrap should be safe here
        Some((c, true))  => $crate::IResult::Done($i.slice(c.len()..), $i.iter_elements().next().unwrap().as_char())
      }
    }
  );
);

/// matches anything but the provided characters
#[macro_export]
macro_rules! none_of (
  ($i:expr, $inp: expr) => (
    {
      use $crate::Slice;
      use $crate::AsChar;
      use $crate::FindToken;
      use $crate::InputIter;

      match ($i).iter_elements().next().map(|c| {
        (c, !c.find_token($inp))
      }) {
        None             => $crate::IResult::Incomplete::<_, _>($crate::Needed::Size(1)),
        Some((_, false)) => $crate::IResult::Error(error_position!($crate::ErrorKind::NoneOf, $i)),
        //the unwrap should be safe here
        Some((c, true))  => $crate::IResult::Done($i.slice(c.len()..), $i.iter_elements().next().unwrap().as_char())
      }
    }
  );
);

/// matches one character: `char!(char) => &[u8] -> IResult<&[u8], char>
#[macro_export]
macro_rules! char (
  ($i:expr, $c: expr) => (
    {
      use $crate::Slice;
      use $crate::AsChar;
      use $crate::InputIter;

      match ($i).iter_elements().next().map(|c| {
        (c, c.as_char() == $c)
      }) {
        None             => $crate::IResult::Incomplete::<_, _>($crate::Needed::Size(1)),
        Some((_, false)) => $crate::IResult::Error(error_position!($crate::ErrorKind::Char, $i)),
        //the unwrap should be safe here
        Some((c, true))  => $crate::IResult::Done($i.slice(c.len()..), $i.iter_elements().next().unwrap().as_char())
      }
    }
  );
);

named!(#[doc="Matches a newline character '\\n'"], pub newline<char>, char!('\n'));

named!(#[doc="Matches a tab character '\\t'"], pub tab<char>, char!('\t'));

pub fn anychar<T>(input: T) -> IResult<T, char> where
  T: InputIter+InputLength+Slice<RangeFrom<usize>>,
  <T as InputIter>::Item: AsChar {
  if input.input_len() == 0 {
    IResult::Incomplete(Needed::Size(1))
  } else {
    IResult::Done(input.slice(1..), input.iter_elements().next().expect("slice should contain at least one element").as_char())
  }
}

#[cfg(test)]
mod tests {
  use internal::IResult::*;
  use util::ErrorKind;

  #[test]
  fn one_of() {
    named!(f<char>, one_of!("ab"));

    let a = &b"abcd"[..];
    assert_eq!(f(a), Done(&b"bcd"[..], 'a'));

    let b = &b"cde"[..];
    assert_eq!(f(b), Error(error_position!(ErrorKind::OneOf, b)));

    named!(utf8(&str) -> char,
      one_of!("+\u{FF0B}"));

    assert!(utf8("+").is_done());
    assert!(utf8("\u{FF0B}").is_done());
  }

  #[test]
  fn none_of() {
    named!(f<char>, none_of!("ab"));

    let a = &b"abcd"[..];
    assert_eq!(f(a), Error(error_position!(ErrorKind::NoneOf, a)));

    let b = &b"cde"[..];
    assert_eq!(f(b), Done(&b"de"[..], 'c'));
  }

  #[test]
  fn char() {
    named!(f<char>, char!('c'));

    let a = &b"abcd"[..];
    assert_eq!(f(a), Error(error_position!(ErrorKind::Char, a)));

    let b = &b"cde"[..];
    assert_eq!(f(b), Done(&b"de"[..], 'c'));
  }

}
