//! Byte level parsers and combinators
//!

/// `tag!(&[T]: nom::AsBytes) => &[T] -> IResult<&[T], &[T]>`
/// declares a byte array as a suite to recognize
///
/// consumes the recognized characters
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(x, tag!("abcd"));
///  let r = x(&b"abcdefgh"[..]);
///  assert_eq!(r, Done(&b"efgh"[..], &b"abcd"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! tag (
  ($i:expr, $inp: expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      if bytes.len() > $i.len() {
        $crate::IResult::Incomplete($crate::Needed::Size(bytes.len()))
      } else if &$i[0..bytes.len()] == bytes {
        $crate::IResult::Done(&$i[bytes.len()..], &$i[0..bytes.len()])
      } else {
        $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::Tag as u32, $i))
      }
    }
  );
);

/// `is_not!(&[T:AsBytes]) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest list of bytes that do not appear in the provided array
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!( not_space, is_not!( " \t\r\n" ) );
///
///  let r = not_space(&b"abcdefgh\nijkl"[..]);
///  assert_eq!(r, Done(&b"\nijkl"[..], &b"abcdefgh"[..]));
///  # }
/// ```
#[macro_export]
macro_rules! is_not(
  ($input:expr, $arr:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected   = $arr;
      let bytes      = as_bytes(&expected);

      match $input.iter().position(|c| {
        for &i in bytes.iter() {
          if *c == i { return true }
        }
        false
      }) {
        Some(0) => $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::IsNot as u32,$input)),
        Some(n) => {
          let res = $crate::IResult::Done(&$input[n..], &$input[..n]);
          res
        },
        None    => {
          $crate::IResult::Done(&b""[..], $input)
        }
      }
    }
  );
);

/// `is_a!(&[T]) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest list of bytes that appear in the provided array
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(abcd, is_a!( "abcd" ));
///
///  let r1 = abcd(&b"aaaaefgh"[..]);
///  assert_eq!(r1, Done(&b"efgh"[..], &b"aaaa"[..]));
///
///  let r2 = abcd(&b"dcbaefgh"[..]);
///  assert_eq!(r2, Done(&b"efgh"[..], &b"dcba"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! is_a(
  ($input:expr, $arr:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected  = $arr;
      let bytes     = as_bytes(&expected);

      match $input.iter().position(|c| {
        for &i in bytes.iter() {
          if *c == i { return false }
        }
        true
      }) {
        Some(0) => $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::IsA as u32,$input)),
        Some(n) => {
          let res = $crate::IResult::Done(&$input[n..], &$input[..n]);
          res
        },
        None    => {
          $crate::IResult::Done(&b""[..], $input)
        }
      }
    }
  );
);

/// `filter!(&[T] -> bool) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest list of bytes until the provided function fails.
///
/// The argument is either a function `&[T] -> bool` or a macro returning a `bool
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # use nom::is_alphanumeric;
/// # fn main() {
///  named!( alpha, filter!( is_alphanumeric ) );
///
///  let r = alpha(&b"abcd\nefgh"[..]);
///  assert_eq!(r, Done(&b"\nefgh"[..], &b"abcd"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! filter(
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $input.iter().position(|c| !$submac!(*c, $($args)*)) {
        Some(n) => {
          let res = $crate::IResult::Done(&$input[n..], &$input[..n]);
          res
        },
        None    => {
          $crate::IResult::Done(&b""[..], $input)
        }
      }
    }
  );
  ($input:expr, $f:expr) => (
    filter!($input, call!($f));
  );
);

/// `take_while!(&[T] -> bool) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest list of bytes until the provided function fails.
///
/// The argument is either a function `&[T] -> bool` or a macro returning a `bool
#[macro_export]
macro_rules! take_while (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $input.iter().position(|c| !$submac!(*c, $($args)*)) {
        Some(n) => {
          let res = $crate::IResult::Done(&$input[n..], &$input[..n]);
          res
        },
        None    => {
          $crate::IResult::Done(&b""[..], $input)
        }
      }
    }
  );
  ($input:expr, $f:expr) => (
    take_while!($input, call!($f));
  );
);

/// `take_while1!(&[T] -> bool) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest (non empty) list of bytes until the provided function fails.
///
/// The argument is either a function `&[T] -> bool` or a macro returning a `bool
#[macro_export]
macro_rules! take_while1 (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $input.iter().position(|c| !$submac!(*c, $($args)*)) {
        Some(0) => $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::TakeWhile1 as u32,$input)),
        Some(n) => {
          let res = $crate::IResult::Done(&$input[n..], &$input[..n]);
          res
        },
        None    => {
          $crate::IResult::Done(&b""[..], $input)
        }
      }
    }
  );
  ($input:expr, $f:expr) => (
    take_while1!($input, call!($f));
  );
);

/// `take_till!(&[T] -> bool) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest list of bytes until the provided function succeeds
///
/// The argument is either a function `&[T] -> bool` or a macro returning a `bool
#[macro_export]
macro_rules! take_till (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (

    {
      match $input.iter().position(|c| $submac!(c, $($args)*)) {
        Some(n) => $crate::IResult::Done(&$input[n..], &$input[..n]),
        None    => $crate::IResult::Done(&b""[..], $input)
      }
    }
  );
  ($input:expr, $f:expr) => (
    take_till!($input, call!($f));
  );
);

/// `take!(nb) => &[T] -> IResult<&[T], &[T]>`
/// generates a parser consuming the specified number of bytes
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  // Desmond parser
///  named!(take5, take!( 5 ) );
///
///  let a = b"abcdefgh";
///
///  assert_eq!(take5(&a[..]), Done(&b"fgh"[..], &b"abcde"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! take(
  ($i:expr, $count:expr) => (
    {
      let cnt = $count as usize;
      if $i.len() < cnt {
        $crate::IResult::Incomplete($crate::Needed::Size(cnt))
      } else {
        $crate::IResult::Done(&$i[cnt..],&$i[0..cnt])
      }
    }
  );
);

/// `take!(nb) => &[T] -> IResult<&[T], &str>`
/// same as take! but returning a &str
#[macro_export]
macro_rules! take_str (
 ( $i:expr, $size:expr ) => ( map_res!($i, take!($size), ::std::str::from_utf8) );
);

/// `take_until_and_consume!(tag) => &[T] -> IResult<&[T], &[T]>`
/// generates a parser consuming bytes until the specified byte sequence is found, and consumes it
#[macro_export]
macro_rules! take_until_and_consume(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected   = $inp;
      let bytes      = as_bytes(&expected);
      if bytes.len() > $i.len() {
        $crate::IResult::Incomplete($crate::Needed::Size(bytes.len()))
      } else {
        let mut index  = 0;
        let mut parsed = false;

        for idx in 0..$i.len() {
          if idx + bytes.len() > $i.len() {
            index = idx;
            break;
          }
          if &$i[idx..idx + bytes.len()] == bytes {
            parsed = true;
            index = idx;
            break;
          }
        }

        if parsed {
          $crate::IResult::Done(&$i[(index + bytes.len())..], &$i[0..index])
        } else {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::TakeUntilAndConsume as u32,$i))
        }
      }
    }
  );
);

/// `take_until!(tag) => &[T] -> IResult<&[T], &[T]>`
/// consumes data until it finds the specified tag
#[macro_export]
macro_rules! take_until(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected   = $inp;
      let bytes      = as_bytes(&expected);
      if bytes.len() > $i.len() {
        $crate::IResult::Incomplete($crate::Needed::Size(bytes.len()))
      } else {
        let mut index  = 0;
        let mut parsed = false;

        for idx in 0..$i.len() {
          if idx + bytes.len() > $i.len() {
            index = idx;
            break;
          }
          if &$i[idx..idx+bytes.len()] == bytes {
            parsed = true;
            index  = idx;
            break;
          }
        }

        if parsed {
          $crate::IResult::Done(&$i[index..], &$i[0..index])
        } else {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::TakeUntil as u32,$i))
        }
      }
    }
  );
);

/// `take_until_either_and_consume!(tag) => &[T] -> IResult<&[T], &[T]>`
/// consumes data until it finds any of the specified characters, and consume it
#[macro_export]
macro_rules! take_until_either_and_consume(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected   = $inp;
      let bytes      = as_bytes(&expected);
      if 1 > $i.len() {
        $crate::IResult::Incomplete($crate::Needed::Size(1))
      } else {
        let mut index  = 0;
        let mut parsed = false;

        for idx in 0..$i.len() {
          if idx + 1 > $i.len() {
            index = idx;
            break;
          }
          for &t in bytes.iter() {
            if $i[idx] == t {
              parsed = true;
              index = idx;
              break;
            }
          }
          if parsed { break; }
        }

        if parsed {
          $crate::IResult::Done(&$i[(index+1)..], &$i[0..index])
        } else {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::TakeUntilEitherAndConsume as u32,$i))
        }
      }
    }
  );
);

/// `take_until_either!(tag) => &[T] -> IResult<&[T], &[T]>`
#[macro_export]
macro_rules! take_until_either(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected   = $inp;
      let bytes      = as_bytes(&expected);
      if 1 > $i.len() {
        $crate::IResult::Incomplete($crate::Needed::Size(1))
      } else {
        let mut index  = 0;
        let mut parsed = false;

        for idx in 0..$i.len() {
          if idx + 1 > $i.len() {
            index = idx;
            break;
          }
          for &t in bytes.iter() {
            if $i[idx] == t {
              parsed = true;
              index = idx;
              break;
            }
          }
          if parsed { break; }
        }

        if parsed {
          $crate::IResult::Done(&$i[index..], &$i[0..index])
        } else {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::TakeUntilEither as u32,$i))
        }
      }
    }
  );
);

/// `length_bytes!(&[T] -> IResult<&[T], nb>) => &[T] -> IResult<&[T], &[T]>
/// gets a number from the first parser, then extracts that many bytes from the
/// remaining stream
#[macro_export]
macro_rules! length_bytes(
  ($i:expr, $f:expr) => (
    {
      match $f($i) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,nb)   => {
          let length_remaining = i1.len();
          if length_remaining < nb {
            $crate::IResult::Incomplete(Needed::Size(nb - length_remaining))
          } else {
            $crate::IResult::Done(&i1[nb..], &i1[..nb])
          }
        }
      }
    }
  )
);

#[cfg(test)]
mod tests {
  use internal::Needed;
  use internal::IResult::*;
  use internal::Err::*;
  use util::ErrorCode;

  #[test]
  fn is_a() {
    named!(a_or_b, is_a!(&b"ab"[..]));

    let a = &b"abcd"[..];
    assert_eq!(a_or_b(a), Done(&b"cd"[..], &b"ab"[..]));

    let b = &b"bcde"[..];
    assert_eq!(a_or_b(b), Done(&b"cde"[..], &b"b"[..]));

    let c = &b"cdef"[..];
    assert_eq!(a_or_b(c), Error(Position(ErrorCode::IsA as u32,c)));

    let d = &b"bacdef"[..];
    assert_eq!(a_or_b(d), Done(&b"cdef"[..], &b"ba"[..]));
  }

  #[test]
  fn is_not() {
    named!(a_or_b, is_not!(&b"ab"[..]));

    let a = &b"cdab"[..];
    assert_eq!(a_or_b(a), Done(&b"ab"[..], &b"cd"[..]));

    let b = &b"cbde"[..];
    assert_eq!(a_or_b(b), Done(&b"bde"[..], &b"c"[..]));

    let c = &b"abab"[..];
    assert_eq!(a_or_b(c), Error(Position(ErrorCode::IsNot as u32,c)));

    let d = &b"cdefba"[..];
    assert_eq!(a_or_b(d), Done(&b"ba"[..], &b"cdef"[..]));

    let e = &b"e"[..];
    assert_eq!(a_or_b(e), Done(&b""[..], &b"e"[..]));

    let f = &b"fghi"[..];
    assert_eq!(a_or_b(f), Done(&b""[..], &b"fghi"[..]));
  }

  #[test]
  fn issue_84() {
    let r0 = is_a!(&b"aaaaefgh"[..], "abcd");
    assert_eq!(r0, Done(&b"efgh"[..], &b"aaaa"[..]));
    let r1 = is_a!(&b"aaaa"[..], "abcd");
    assert_eq!(r1, Done(&b""[..], &b"aaaa"[..]));
    let r2 = is_a!(&b"1"[..], "123456789");
    assert_eq!(r2, Done(&b""[..], &b"1"[..]));
  }

  #[test]
  fn take_str_test() {
    let a = b"omnomnom";

    assert_eq!(take_str!(&a[..], 5), Done(&b"nom"[..], "omnom"));
    assert_eq!(take_str!(&a[..], 9), Incomplete(Needed::Size(9)));
  }

  #[test]
  fn take_until_test() {
    named!(x, take_until_and_consume!("efgh"));
    let r = x(&b"abcdabcdefghijkl"[..]);
    assert_eq!(r, Done(&b"ijkl"[..], &b"abcdabcd"[..]));

    println!("Done 1\n");

    let r2 = x(&b"abcdabcdefgh"[..]);
    assert_eq!(r2, Done(&b""[..], &b"abcdabcd"[..]));

    println!("Done 2\n");
    let r3 = x(&b"abcefg"[..]);
    assert_eq!(r3,  Error(Position(ErrorCode::TakeUntilAndConsume as u32, &b"abcefg"[..])));

    assert_eq!(
      x(&b"ab"[..]),
      Incomplete(Needed::Size(4))
    );
  }

  #[test]
  fn take_until_either_incomplete() {
    named!(x, take_until_either!("!."));
    assert_eq!(
      x(&b"123"[..]),
      Error(Position(ErrorCode::TakeUntilEither as u32, &b"123"[..]))
    );
  }

  #[test]
  fn take_until_incomplete() {
    named!(y, take_until!("end"));
    assert_eq!(
      y(&b"nd"[..]),
      Incomplete(Needed::Size(3))
    );
    assert_eq!(
      y(&b"123"[..]),
      Error(Position(ErrorCode::TakeUntil as u32, &b"123"[..]))
    );
  }

  #[cfg(feature = "nightly")]
  use test::Bencher;

  #[cfg(feature = "nightly")]
  #[bench]
  fn filter(b: &mut Bencher) {
    use nom::is_alphabetic;
    named!(f, filter!(is_alphabetic));
    b.iter(|| {
      f(&b"abcdefghijklABCDEejfrfrjgro12aa"[..])
    });
  }
}
