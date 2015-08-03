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
      let mut parsed = false;
      let mut index  = 0;

      for idx in 0..$input.len() {
        index = idx;
        for &i in bytes.iter() {
          if $input[idx] == i {
            parsed = true;
            break;
          }
        }
        if parsed { break; }
      }
      if index == 0 {
        $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::IsNot as u32,$input))
      } else {
        $crate::IResult::Done(&$input[index..], &$input[0..index])
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
      let mut index = 0;

      for idx in 0..$input.len() {
        index = idx;
        let mut cont = false;
        for &i in bytes.iter() {
          if $input[idx] == i {
            cont = true;
            break;
          }
        }
        if !cont { break; }
      }
      if index == 0 {
        $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::IsA as u32,$input))
      } else {
        $crate::IResult::Done(&$input[index..], &$input[0..index])
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
      let mut index = 0;
      let mut found = false;
      for idx in 0..$input.len() {
        index = idx;
        if !$submac!($input[idx], $($args)*) {
          found = true;
          break;
        }
      }
      if index == 0 {
        $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::Filter as u32,$input))
      } else if found {
        $crate::IResult::Done(&$input[index..], &$input[0..index])
      } else {
        $crate::IResult::Done(&b""[..], $input)
      }
    }
  );
  ($input:expr, $f:expr) => (
    filter!($input, call!($f));
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
 ( $i:expr, $size:expr ) => ( map_res!($i, take!($size), from_utf8) );
);

/// `separated_list!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// separated_list(sep, X) returns Vec<X>
#[macro_export]
macro_rules! separated_list(
  ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => (
    {
      let mut res   = Vec::new();
      let mut input = $i;

      // get the first element
      match $submac!(input, $($args2)*) {
        $crate::IResult::Error(_)      => $crate::IResult::Done(input, Vec::new()),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i,o)     => {
          if i.len() == input.len() {
            $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::SeparatedList as u32,input))
          } else {
            res.push(o);
            input = i;

            loop {
              // get the separator first
              match $sep!(input, $($args)*) {
                $crate::IResult::Error(_)      => break,
                $crate::IResult::Incomplete(_) => break,
                $crate::IResult::Done(i2,_)    => {
                  if i2.len() == input.len() {
                    break;
                  }
                  input = i2;

                  // get the element next
                  match $submac!(input, $($args2)*) {
                    $crate::IResult::Error(_)      => break,
                    $crate::IResult::Incomplete(_) => break,
                    $crate::IResult::Done(i3,o3)   => {
                      if i3.len() == input.len() {
                        break;
                      }
                      res.push(o3);
                      input = i3;
                    },
                  }
                }
              }
            }
            $crate::IResult::Done(input, res)
          }
        },
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    separated_list!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    separated_list!($i, call!($f), $submac!($($args)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    separated_list!($i, call!($f), call!($g));
  );
);

/// `separated_nonempty_list!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// separated_nonempty_list(sep, X) returns Vec<X>
#[macro_export]
macro_rules! separated_nonempty_list(
  ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res = Vec::new();

      // get the first element
      match $submac!($i, $($args2)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i,o)     => {
          if i.len() == $i.len() {
            $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::SeparatedNonEmptyList as u32,$i))
          } else {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();

            loop {
              // get the separator first
              match $sep!(&$i[begin..], $($args)*) {
                $crate::IResult::Error(_)      => break,
                $crate::IResult::Incomplete(_) => break,
                $crate::IResult::Done(i2,_)    => {
                  if i2.len() == (&$i[begin..]).len() {
                    break;
                  }
                  begin += remaining - i2.len();
                  remaining = i2.len();

                  // get the element next
                  match $submac!(&$i[begin..], $($args2)*) {
                    $crate::IResult::Error(_)      => break,
                    $crate::IResult::Incomplete(_) => break,
                    $crate::IResult::Done(i3,o3)   => {
                      if i3.len() == $i[begin..].len() {
                        break;
                      }
                      res.push(o3);
                      begin += remaining - i3.len();
                      remaining = i3.len();
                    },
                  }
                }
              }
            }
            $crate::IResult::Done(&$i[begin..], res)
          }
        },
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    separated_nonempty_list!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    separated_nonempty_list!($i, call!($f), $submac!($($args)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    separated_nonempty_list!($i, call!($f), call!($g));
  );
);

/// `many0!(I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// Applies the parser 0 or more times and returns the list of results in a Vec
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >, many0!( tag!( "abcd" ) ) );
///
///  let a = b"abcdabcdef";
///  let b = b"azerty";
///
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&a[..]), Done(&b"ef"[..], res));
///  assert_eq!(multi(&b[..]), Done(&b"azerty"[..], Vec::new()));
/// # }
/// ```
/// 0 or more
#[macro_export]
macro_rules! many0(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let mut res   = Vec::new();
      let mut input = $i;
      loop {
        match $submac!(input, $($args)*) {
          $crate::IResult::Done(i,o) => {
            if i.len() == input.len() {
              break;
            }
            res.push(o);
            input = i;
          },
          _                          => {
            break;
          }
        }
      }
      $crate::IResult::Done(input, res)
    }
  );
  ($i:expr, $f:expr) => (
    many0!($i, call!($f));
  );
);

/// `many1!(I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// Applies the parser 1 or more times and returns the list of results in a Vec
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # use nom::Err::Position;
/// # use nom::ErrorCode;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >, many1!( tag!( "abcd" ) ) );
///
///  let a = b"abcdabcdef";
///  let b = b"azerty";
///
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&a[..]), Done(&b"ef"[..], res));
///  assert_eq!(multi(&b[..]), Error(Position(ErrorCode::Many1 as u32,&b[..])));
/// # }
/// ```
#[macro_export]
macro_rules! many1(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let mut res   = Vec::new();
      let mut input = $i;
      loop {
        match $submac!(input, $($args)*) {
          $crate::IResult::Done(i,o) => {
            if i.len() == input.len() {
              break;
            }
            res.push(o);
            input = i;
          },
          _                          => {
            break;
          }
        }
      }
      if res.len() == 0 {
        $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::Many1 as u32,$i))
      } else {
        $crate::IResult::Done(input, res)
      }
    }
  );
  ($i:expr, $f:expr) => (
    many1!($i, call!($f));
  );
);

/// `count!(I -> IResult<I,O>, nb) => I -> IResult<I, Vec<O>>`
/// Applies the child parser a specified number of times
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done,Error};
/// # use nom::Err::Position;
/// # use nom::ErrorCode;
/// # fn main() {
///  named!(counter< Vec<&[u8]> >, count!( tag!( "abcd" ), 2 ) );
///
///  let a = b"abcdabcdabcdef";
///  let b = b"abcdefgh";
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///
///  assert_eq!(counter(&a[..]), Done(&b"abcdef"[..], res));
///  assert_eq!(counter(&b[..]), Error(Position(ErrorCode::Count as u32, &b[..])));
/// # }
/// ```
///
#[macro_export]
macro_rules! count(
  ($i:expr, $submac:ident!( $($args:tt)* ), $count: expr) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res = Vec::new();
      let mut cnt: usize = 0;
      let mut err = false;
      loop {
        match $submac!(&$i[begin..], $($args)*) {
          $crate::IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            cnt = cnt + 1;
            if cnt == $count {
              break
            }
          },
          $crate::IResult::Error(_)  => {
            err = true;
            break;
          },
          $crate::IResult::Incomplete(_) => {
            break;
          }
        }
      }
      if err {
        $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::Count as u32,$i))
      } else if cnt == $count {
        $crate::IResult::Done(&$i[begin..], res)
      } else {
        $crate::IResult::Incomplete($crate::Needed::Unknown)
      }
    }
  );
  ($i:expr, $f:expr, $count: expr) => (
    count!($i, call!($f), $count);
  );
);

/// `count_fixed!(I -> IResult<I,O>, nb) => I -> IResult<I, [O; nb]>`
/// Applies the child parser a fixed number of times and returns a fixed size array
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done,Error};
/// # use nom::Err::Position;
/// # use nom::ErrorCode;
/// # fn main() {
///  named!(counter< [&[u8]; 2] >, count_fixed!( &[u8], tag!( "abcd" ), 2 ) );
///  // can omit the type specifier if returning slices
///  // named!(counter< [&[u8]; 2] >, count_fixed!( tag!( "abcd" ), 2 ) );
///
///  let a = b"abcdabcdabcdef";
///  let b = b"abcdefgh";
///  let res = [&b"abcd"[..], &b"abcd"[..]];
///
///  assert_eq!(counter(&a[..]), Done(&b"abcdef"[..], res));
///  assert_eq!(counter(&b[..]), Error(Position(ErrorCode::Count as u32, &b[..])));
/// # }
/// ```
///
#[macro_export]
macro_rules! count_fixed(
  ($i:expr, $typ:ty, $submac:ident!( $($args:tt)* ), $count: expr) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res: [$typ; $count] = unsafe{[::std::mem::uninitialized(); $count as usize]};
      let mut cnt: usize = 0;
      let mut err = false;
      loop {
        match $submac!(&$i[begin..], $($args)*) {
          $crate::IResult::Done(i,o) => {
            res[cnt] = o;
            begin += remaining - i.len();
            remaining = i.len();
            cnt = cnt + 1;
            if cnt == $count {
              break
            }
          },
          $crate::IResult::Error(_)  => {
            err = true;
            break;
          },
          $crate::IResult::Incomplete(_) => {
            break;
          }
        }
      }
      if err {
        $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::Count as u32,$i))
      } else if cnt == $count {
        $crate::IResult::Done(&$i[begin..], res)
      } else {
        $crate::IResult::Incomplete($crate::Needed::Unknown)
      }
    }
  );
  ($i:expr, $typ: ty, $f:ident, $count: expr) => (
    count_fixed!($i, $typ, call!($f), $count);
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $count: expr) => (
    count_fixed!($i, &[u8], $submac!($($args)*), $count);
  );
  ($i:expr, $f:ident, $count: expr) => (
    count_fixed!($i, &[u8], call!($f), $count);
  );
);

/// `take_until_and_consume!(tag) => &[T] -> IResult<&[T], &[T]>`
/// generates a parser consuming bytes until the specified byte sequence is found
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

      if index + bytes.len() > $i.len() {
        $crate::IResult::Incomplete($crate::Needed::Size(index + bytes.len()))
      } else {
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

      if index + bytes.len() > $i.len() {
        $crate::IResult::Incomplete($crate::Needed::Size(index + bytes.len()))
      } else {
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
      if index + 1 > $i.len() {
        $crate::IResult::Incomplete($crate::Needed::Size(index + 1))
      } else {
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
      if index + 1 > $i.len() {
        $crate::IResult::Incomplete($crate::Needed::Size(index + 1))
      } else {
        if parsed {
          $crate::IResult::Done(&$i[index..], &$i[0..index])
        } else {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::TakeUntilEither as u32,$i))
        }
      }
    }
  );
);

/// `length_value!(I -> IResult<I, nb>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// gets a number from the first parser, then applies the second parser that many times
#[macro_export]
macro_rules! length_value(
  ($i:expr, $f:expr, $g:expr) => (
    {
      match $f($i) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,nb)   => {
          let length_token     = $i.len() - i1.len();
          let mut begin        = 0;
          let mut remaining    = i1.len();
          let mut res          = Vec::new();
          let mut err          = false;
          let mut inc          = $crate::Needed::Unknown;

          loop {
            if res.len() == nb as usize {
              break;
            }
            match $g(&i1[begin..]) {
              $crate::IResult::Done(i2,o2) => {
              res.push(o2);
                let parsed  = remaining - i2.len();
                begin      += parsed;
                remaining   = i2.len();
              },
              $crate::IResult::Error(_)      => {
                err = true;
              },
              $crate::IResult::Incomplete(a) => {
                inc = a;
                break;
              }
            }
          }
          if err {
            $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::LengthValue as u32,$i))
          } else if res.len() < nb as usize {
            match inc {
              $crate::Needed::Unknown      => $crate::IResult::Incomplete($crate::Needed::Unknown),
              $crate::Needed::Size(length) => $crate::IResult::Incomplete($crate::Needed::Size(length_token + nb as usize * length))
            }
          } else {
            $crate::IResult::Done(&i1[begin..], res)
          }

        }
      }
    }
  );
  ($i:expr, $f:expr, $g:expr, $length:expr) => (
    {
      match $f($i) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,nb)   => {
          let length_token     = $i.len() - i1.len();
          let mut begin        = 0;
          let mut remaining    = i1.len();
          let mut res          = Vec::new();
          let mut err          = false;
          let mut inc          = $crate::Needed::Unknown;

          loop {
            if res.len() == nb as usize {
              break;
            }
            match $g(&i1[begin..]) {
              $crate::IResult::Done(i2,o2) => {
              res.push(o2);
                let parsed  = remaining - i2.len();
                begin      += parsed;
                remaining   = i2.len();
              },
              $crate::IResult::Error(_)      => {
                err = true;
              },
              $crate::IResult::Incomplete(a) => {
                inc = a;
                break;
              }
            }
          }
          if err {
            $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::LengthValue as u32,$i))
          } else if res.len() < nb as usize {
            match inc {
              $crate::Needed::Unknown => $crate::IResult::Incomplete($crate::Needed::Unknown),
              $crate::Needed::Size(_) => $crate::IResult::Incomplete($crate::Needed::Size(length_token + nb as usize * $length))
            }
          } else {
            $crate::IResult::Done(&i1[begin..], res)
          }

        }
      }
    }
  );
);

#[cfg(test)]
mod tests {
  use internal::{Needed,IResult};
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
  fn separated_list() {
    named!(multi<&[u8],Vec<&[u8]> >, separated_list!(tag!(","), tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"azerty"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"ef"[..], res2));
    assert_eq!(multi(c), Done(&b"azerty"[..], Vec::new()));
  }

  #[test]
  fn separated_nonempty_list() {
    named!(multi<&[u8],Vec<&[u8]> >, separated_nonempty_list!(tag!(","), tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"azerty"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"ef"[..], res2));
    assert_eq!(multi(c), Error(Position(0,c)));
  }

  #[test]
  fn many0() {
    named!(multi<&[u8],Vec<&[u8]> >, many0!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcdabcdef"[..];
    let c = &b"azerty"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"ef"[..], res2));
    assert_eq!(multi(c), Done(&b"azerty"[..], Vec::new()));
  }

  #[test]
  fn many1() {
    named!(multi<&[u8],Vec<&[u8]> >, many1!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcdabcdef"[..];
    let c = &b"azerty"[..];
    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"ef"[..], res2));
    assert_eq!(multi(c), Error(Position(ErrorCode::Many1 as u32,c)));
  }

  #[test]
  fn infinite_many() {
    fn tst(input: &[u8]) -> IResult<&[u8], &[u8]> {
      println!("input: {:?}", input);
      Error(Position(0,input))
    }

    // should not go into an infinite loop
    named!(multi0<&[u8],Vec<&[u8]> >, many0!(tst));
    let a = &b"abcdef"[..];
    assert_eq!(multi0(a), Done(a, Vec::new()));

    named!(multi1<&[u8],Vec<&[u8]> >, many1!(tst));
    let a = &b"abcdef"[..];
    assert_eq!(multi1(a), Error(Position(ErrorCode::Many1 as u32,a)));
  }

  #[test]
  fn count() {
    fn counter(input: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
      let size: usize = 2;
      count!(input, tag!( "abcd" ), size )
    }

    let a = b"abcdabcdabcdef";
    let b = b"abcdefgh";
    let res = vec![&b"abcd"[..], &b"abcd"[..]];

    assert_eq!(counter(&a[..]), Done(&b"abcdef"[..], res));
    assert_eq!(counter(&b[..]), Error(Position(ErrorCode::Count as u32, &b[..])));
  }

  #[test]
  fn count_fixed() {
    named!(counter< [&[u8]; 2] >, count_fixed!( &[u8], tag!( "abcd" ), 2 ) );

    let a = b"abcdabcdabcdef";
    let b = b"abcdefgh";
    let res = [&b"abcd"[..], &b"abcd"[..]];

    assert_eq!(counter(&a[..]), Done(&b"abcdef"[..], res));
    assert_eq!(counter(&b[..]), Error(Position(ErrorCode::Count as u32, &b[..])));
  }

  use nom::{le_u16,eof};
  #[allow(dead_code)]
  pub fn compile_count_fixed(input: &[u8]) -> IResult<&[u8], ()> {
    chain!(input,
      tag!("abcd")                   ~
      count_fixed!( u16, le_u16, 4 ) ~
      eof                            ,
      || { () }
    )
  }

  #[test]
  fn count_fixed_no_type() {
    named!(counter< [&[u8]; 2] >, count_fixed!( tag!( "abcd" ), 2 ) );

    let a = b"abcdabcdabcdef";
    let b = b"abcdefgh";
    let res = [&b"abcd"[..], &b"abcd"[..]];

    assert_eq!(counter(&a[..]), Done(&b"abcdef"[..], res));
    assert_eq!(counter(&b[..]), Error(Position(ErrorCode::Count as u32, &b[..])));
  }

  use std::str::from_utf8;
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
    assert_eq!(r3, Incomplete(Needed::Size(7)));
  }

  use nom::{be_u8,be_u16};
  #[test]
  fn length_value_test() {
    named!(tst1<&[u8], Vec<u16> >, length_value!(be_u8, be_u16));
    named!(tst2<&[u8], Vec<u16> >, length_value!(be_u8, be_u16, 2));

    let i1 = vec![0, 5, 6];
    let i2 = vec![1, 5, 6, 3];
    let i3 = vec![2, 5, 6, 3];
    let i4 = vec![2, 5, 6, 3, 4, 5, 7];
    let i5 = vec![3, 5, 6, 3, 4, 5];

    let r1: Vec<u16> = Vec::new();
    let r2: Vec<u16> = vec![1286];
    let r4: Vec<u16> = vec![1286, 772];
    assert_eq!(tst1(&i1), IResult::Done(&i1[1..], r1));
    assert_eq!(tst1(&i2), IResult::Done(&i2[3..], r2));
    assert_eq!(tst1(&i3), IResult::Incomplete(Needed::Size(5)));
    assert_eq!(tst1(&i4), IResult::Done(&i4[5..], r4));
    assert_eq!(tst1(&i5), IResult::Incomplete(Needed::Size(7)));

    let r6: Vec<u16> = Vec::new();
    let r7: Vec<u16> = vec![1286];
    let r9: Vec<u16> = vec![1286, 772];
    assert_eq!(tst2(&i1), IResult::Done(&i1[1..], r6));
    assert_eq!(tst2(&i2), IResult::Done(&i2[3..], r7));
    assert_eq!(tst2(&i3), IResult::Incomplete(Needed::Size(5)));
    assert_eq!(tst2(&i4), IResult::Done(&i4[5..], r9));
    assert_eq!(tst1(&i5), IResult::Incomplete(Needed::Size(7)));

  }
}
