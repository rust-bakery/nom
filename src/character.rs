/// Character level parsers

use internal::{IResult,Needed};

/// matches one of the provided characters
#[macro_export]
macro_rules! one_of (
  ($i:expr, $inp: expr) => (
    {
      use $crate::Slice;
      use $crate::AsChar;
      use $crate::FindToken;
      use $crate::InputIter;

      match ($i).iter_elements().next().map(|c| {
        c.find_token($inp)
      }) {
        None        => $crate::IResult::Incomplete::<_, _>($crate::Needed::Size(1)),
        Some(false) => $crate::IResult::Error(error_position!($crate::ErrorKind::OneOf, $i)),
        //the unwrap should be safe here
        Some(true)  => $crate::IResult::Done($i.slice(1..), $i.iter_elements().next().unwrap().as_char())
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
        !c.find_token($inp)
      }) {
        None        => $crate::IResult::Incomplete::<_, _>($crate::Needed::Size(1)),
        Some(false) => $crate::IResult::Error(error_position!($crate::ErrorKind::NoneOf, $i)),
        //the unwrap should be safe here
        Some(true)  => $crate::IResult::Done($i.slice(1..), $i.iter_elements().next().unwrap().as_char())
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
        c.as_char() == $c
      }) {
        None        => $crate::IResult::Incomplete::<_, _>($crate::Needed::Size(1)),
        Some(false) => $crate::IResult::Error(error_position!($crate::ErrorKind::Char, $i)),
        //the unwrap should be safe here
        Some(true)  => $crate::IResult::Done($i.slice(1..), $i.iter_elements().next().unwrap().as_char())
      }
    }
  );
);

named!(#[doc="Matches a newline character '\\n'"], pub newline<char>, char!('\n'));

named!(#[doc="Matches a tab character '\\t'"], pub tab<char>, char!('\t'));

pub fn anychar(input:&[u8]) -> IResult<&[u8], char> {
  if input.is_empty() {
    IResult::Incomplete(Needed::Size(1))
  } else {
    IResult::Done(&input[1..], input[0] as char)
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
