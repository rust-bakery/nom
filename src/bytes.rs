//! Byte level parsers and combinators
//!
#[allow(unused_variables)]

/// `tag!(&[T]: nom::AsBytes) => &[T] -> IResult<&[T], &[T]>`
/// declares a byte array as a suite to recognize
///
/// consumes the recognized characters
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!(x, tag!("abcd"));
///  let r = x(&b"abcdefgh"[..]);
///  assert_eq!(r, Ok((&b"efgh"[..], &b"abcd"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! tag (
  ($i:expr, $tag: expr) => (
    {
      use ::std::result::Result::*;
      use $crate::{Err,Needed,IResult,ErrorKind};
      use $crate::{Compare,CompareResult,InputLength,Slice,need_more};

      let res: IResult<_,_> = match ($i).compare($tag) {
        CompareResult::Ok => {
          let blen = $tag.input_len();
          Ok(($i.slice(blen..), $i.slice(..blen)))
        },
        CompareResult::Incomplete => {
          need_more($i, Needed::Size($tag.input_len()))
        },
        CompareResult::Error => {
          let e:ErrorKind<u32> = ErrorKind::Tag;
          Err(Err::Error($crate::Context::Code($i, e)))
        }
      };
      res
    }
  );
);

/// `tag_no_case!(&[T]) => &[T] -> IResult<&[T], &[T]>`
/// declares a case insensitive ascii string as a suite to recognize
///
/// consumes the recognized characters
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!(test, tag_no_case!("ABcd"));
///
///  let r = test(&b"aBCdefgh"[..]);
///  assert_eq!(r, Ok((&b"efgh"[..], &b"aBCd"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! tag_no_case (
  ($i:expr, $tag: expr) => (
    {
      use ::std::result::Result::*;
      use $crate::{Err,Needed,IResult,ErrorKind};
      use $crate::{Compare,CompareResult,InputLength,Slice};

      let res: IResult<_,_> = match ($i).compare_no_case($tag) {
        CompareResult::Ok => {
          let blen = $tag.input_len();
          Ok(($i.slice(blen..), $i.slice(..blen)))
        },
        CompareResult::Incomplete => {
          $crate::need_more($i, Needed::Size($tag.input_len()))
        },
        CompareResult::Error => {
          let e:ErrorKind<u32> = ErrorKind::Tag;
          Err(Err::Error($crate::Context::Code($i, e)))
        }
      };
      res
    }
  );
);


/// `is_not!(&[T:AsBytes]) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest list of bytes that do not appear in the provided array
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!( not_space, is_not!( " \t\r\n" ) );
///
///  let r = not_space(&b"abcdefgh\nijkl"[..]);
///  assert_eq!(r, Ok((&b"\nijkl"[..], &b"abcdefgh"[..])));
///  # }
/// ```
#[macro_export]
macro_rules! is_not(
  ($input:expr, $arr:expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,IResult,ErrorKind};

      use $crate::InputLength;
      use $crate::InputIter;
      use $crate::FindToken;
      use $crate::Slice;

      let res: IResult<_,_> = match $input.position(|c| {
        c.find_token($arr)
      }) {
        Some(0) => {
          let e = ErrorKind::IsNot::<u32>;
          Err(Err::Error(error_position!(e,$input)))
        },
        Some(n) => {
          let res = Ok(($input.slice(n..), $input.slice(..n)));
          res
        },
        None    => {
          Ok(($input.slice($input.input_len()..), $input))
        }
      };
      res
    }
  );
);

/// `is_a!(&[T]) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest list of bytes that appear in the provided array
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!(abcd, is_a!( "abcd" ));
///
///  let r1 = abcd(&b"aaaaefgh"[..]);
///  assert_eq!(r1, Ok((&b"efgh"[..], &b"aaaa"[..])));
///
///  let r2 = abcd(&b"dcbaefgh"[..]);
///  assert_eq!(r2, Ok((&b"efgh"[..], &b"dcba"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! is_a (
  ($input:expr, $arr:expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,IResult,ErrorKind};

      use $crate::InputLength;
      use $crate::InputIter;
      use $crate::FindToken;
      use $crate::Slice;

      let res: IResult<_,_> = match $input.position(|c| {
        !c.find_token($arr)
      }) {
        Some(0) => {
          let e: ErrorKind<u32> = ErrorKind::IsA;
          Err(Err::Error(error_position!(e,$input)))
        },
        Some(n) => {
          let res: IResult<_,_, u32> = Ok(($input.slice(n..), $input.slice(..n)));
          res
        },
        None    => {
          Ok(($input.slice(($input).input_len()..), $input))
        }
      };
      res
    }
  );
);

/// `escaped!(&[T] -> IResult<&[T], &[T]>, T, &[T] -> IResult<&[T], &[T]>) => &[T] -> IResult<&[T], &[T]>`
/// matches a byte string with escaped characters.
///
/// The first argument matches the normal characters (it must not accept the control character), the second argument is the control character (like `\` in most languages),
/// the third argument matches the escaped characters
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::alpha;
/// # fn main() {
///  named!(esc, escaped!(call!(alpha), '\\', one_of!("\"n\\")));
///  assert_eq!(esc(&b"abcd"[..]), Ok((&b""[..], &b"abcd"[..])));
///  assert_eq!(esc(&b"ab\\\"cd"[..]), Ok((&b""[..], &b"ab\\\"cd"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! escaped (
  // Internal parser, do not use directly
  (__impl $i: expr, $normal:ident!(  $($args:tt)* ), $control_char: expr, $escapable:ident!(  $($args2:tt)* )) => (
    {
      use ::std::result::Result::*;
      use $crate::{Err,Needed,IResult,ErrorKind,need_more};

      use $crate::InputLength;
      use $crate::Slice;
      let cl = || -> IResult<_,_,u32> {
        use $crate::Offset;
        let mut index  = 0;

        while index < $i.input_len() {
          match $normal!($i.slice(index..), $($args)*) {
            Ok((i, _)) => {
              if i.is_empty() {
                return Ok(($i.slice($i.input_len()..), $i))
              } else {
                index = $i.offset(i);
              }
            },
            Err(Err::Error(e)) => {
              if $i[index] == $control_char as u8 {
                if index + 1 >= $i.input_len() {
                  return need_more($i, Needed::Unknown)
                } else {
                  match $escapable!($i.slice(index+1..), $($args2)*) {
                    Ok((i,_)) => {
                      if i.is_empty() {
                        return Ok(($i.slice($i.input_len()..), $i))
                      } else {
                        index = $i.offset(i);
                      }
                    },
                    Err(e) => return Err(e)
                  }
                }
              } else {
                return Ok(($i.slice(index..), $i.slice(..index)));
              }
            },
            Err(e) => {
              return Err(e)
            }
          }
        }
        Ok((&$i[index..], &$i[..index]))
      };
      match cl() {
        Err(Err::Incomplete(x)) => Err(Err::Incomplete(x)),
        Ok((i, o))    => Ok((i, o)),
        Err(Err::Error(e))      => {
          let e2 = ErrorKind::Escaped::<u32>;
          return Err(Err::Error(error_node_position!(e2, $i, e)))
        },
        Err(Err::Failure(e))      => {
          let e2 = ErrorKind::Escaped::<u32>;
          return Err(Err::Failure(error_node_position!(e2, $i, e)))
        }
      }
    }
  );
  // Internal parser, do not use directly
  (__impl_1 $i:expr, $submac1:ident!( $($args:tt)* ), $control_char: expr, $submac2:ident!( $($args2:tt)*) ) => (
    {
     escaped!(__impl $i, $submac1!($($args)*), $control_char,  $submac2!($($args2)*))
    }
  );
  // Internal parser, do not use directly
  (__impl_1 $i:expr, $submac1:ident!( $($args:tt)* ), $control_char: expr, $g:expr) => (
     escaped!(__impl $i, $submac1!($($args)*), $control_char, call!($g))
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $control_char: expr, $($rest:tt)+) => (
    {
      let input: &[u8] = $i;

      escaped!(__impl_1 input, $submac!($($args)*), $control_char, $($rest)*)
    }
  );

  ($i:expr, $f:expr, $control_char: expr, $($rest:tt)+) => (
    escaped!(__impl_1 $i, call!($f), $control_char, $($rest)*)
  );
);

/// `escaped_transform!(&[T] -> IResult<&[T], &[T]>, T, &[T] -> IResult<&[T], &[T]>) => &[T] -> IResult<&[T], Vec<T>>`
/// matches a byte string with escaped characters.
///
/// The first argument matches the normal characters (it must not match the control character), the second argument is the control character (like `\` in most languages),
/// the third argument matches the escaped characters and transforms them.
///
/// As an example, the chain `abc\tdef` could be `abc    def` (it also consumes the control character)
///
/// WARNING: if you do not use the `verbose-errors` feature, this combinator will currently fail to build
/// because of a type inference error
///
/// # Example
/// ```ignore
/// # #[macro_use] extern crate nom;
/// # use nom::alpha;
/// # use std::str::from_utf8;
/// # fn main() {
/// fn to_s(i:Vec<u8>) -> String {
///   String::from_utf8_lossy(&i).into_owned()
/// }

///  named!(transform < String >,
///    map!(
///      escaped_transform!(call!(alpha), '\\',
///        alt!(
///            tag!("\\")       => { |_| &b"\\"[..] }
///          | tag!("\"")       => { |_| &b"\""[..] }
///          | tag!("n")        => { |_| &b"\n"[..] }
///        )
///      ), to_s
///    )
///  );
///  assert_eq!(transform(&b"ab\\\"cd"[..]), Ok((&b""[..], String::from("ab\"cd"))));
/// # }
/// ```
#[macro_export]
macro_rules! escaped_transform (
  // Internal parser, do not use directly
  (__impl $i: expr, $normal:ident!(  $($args:tt)* ), $control_char: expr, $transform:ident!(  $($args2:tt)* )) => (
    {
      use ::std::result::Result::*;
      use $crate::{Err,ErrorKind};

      use $crate::{InputLength,Slice};
      let cl = || {
        use $crate::Offset;
        let mut index  = 0;
        let mut res = Vec::new();

        while index < $i.input_len() {
          if let Ok((i,o)) = $normal!($i.slice(index..), $($args)*) {
            res.extend(o.iter().cloned());
            if i.is_empty() {
              return Ok(($i.slice($i.input_len()..), res));
            } else {
              index = $i.offset(i);
            }
          } else if $i[index] == $control_char as u8 {
            if index + 1 >= $i.input_len() {
              let e = ErrorKind::EscapedTransform::<u32>;
              return Err(Err::Error(error_position!(e,$i.slice(index..))));
            } else {
              match $transform!($i.slice(index+1..), $($args2)*) {
                Ok((i,o)) => {
                  res.extend(o.iter().cloned());
                  if i.is_empty() {
                    return Ok(($i.slice($i.input_len()..), res))
                  } else {
                    index = $i.offset(i);
                  }
                },
                Err(e) => return Err(e)
              }
            }
          } else {
            if index == 0 {
              let e = ErrorKind::EscapedTransform::<u32>;
              return Err(Err::Error(error_position!(e,$i.slice(index..))))
            } else {
              return Ok(($i.slice(index..), res))
            }
          }
        }
        Ok(($i.slice(index..), res))
      };
      match cl() {
        Err(Err::Incomplete(x)) => Err(Err::Incomplete(x)),
        Ok((i, o))    => Ok((i, o)),
        Err(Err::Error(e))      => {
          let e2 = ErrorKind::EscapedTransform::<u32>;
          return Err(Err::Error(error_node_position!(e2, $i, e)))
        },
        Err(Err::Failure(e))      => {
          let e2 = ErrorKind::EscapedTransform::<u32>;
          return Err(Err::Failure(error_node_position!(e2, $i, e)))
        }
      }
    }
  );
  // Internal parser, do not use directly
  (__impl_1 $i:expr, $submac1:ident!( $($args:tt)* ), $control_char: expr, $submac2:ident!( $($args2:tt)*) ) => (
    {
     escaped_transform!(__impl $i, $submac1!($($args)*), $control_char,  $submac2!($($args2)*))
    }
  );
  // Internal parser, do not use directly
  (__impl_1 $i:expr, $submac1:ident!( $($args:tt)* ), $control_char: expr, $g:expr) => (
     escaped_transform_impl!($i, $submac1!($($args)*), $control_char, call!($g))
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $control_char: expr, $($rest:tt)+) => (
    {
      let input: &[u8] = $i;

      escaped_transform!(__impl_1 input, $submac!($($args)*), $control_char, $($rest)*)
    }
  );

  ($i:expr, $f:expr, $control_char: expr, $($rest:tt)+) => (
    escaped_transform!(__impl_1 $i, call!($f), $control_char, $($rest)*)
  );
);

/// `take_while!(T -> bool) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest list of bytes until the provided function fails.
///
/// The argument is either a function `T -> bool` or a macro returning a `bool`.
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::is_alphanumeric;
/// # fn main() {
///  named!( alpha, take_while!( is_alphanumeric ) );
///
///  let r = alpha(&b"abcd\nefgh"[..]);
///  assert_eq!(r, Ok((&b"\nefgh"[..], &b"abcd"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! take_while (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::IResult;

      use $crate::{InputLength,InputIter,Slice};
      let input = $input;

      match input.position(|c| !$submac!(c, $($args)*)) {
        Some(n) => {
          let res:IResult<_,_> = Ok((input.slice(n..), input.slice(..n)));
          res
        },
        None    => {
          Ok((input.slice(input.input_len()..), input))
        }
      }
    }
  );
  ($input:expr, $f:expr) => (
    take_while!($input, call!($f));
  );
);

/// `take_while1!(T -> bool) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest (non empty) list of bytes until the provided function fails.
///
/// The argument is either a function `&[T] -> bool` or a macro returning a `bool`
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::{Err,ErrorKind};
/// # use nom::is_alphanumeric;
/// # fn main() {
///  named!( alpha, take_while1!( is_alphanumeric ) );
///
///  let r = alpha(&b"abcd\nefgh"[..]);
///  assert_eq!(r, Ok((&b"\nefgh"[..], &b"abcd"[..])));
///  let r = alpha(&b"\nefgh"[..]);
///  assert_eq!(r, Err(Err::Error(error_position!(ErrorKind::TakeWhile1, &b"\nefgh"[..]))));
/// # }
/// ```
#[macro_export]
macro_rules! take_while1 (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,ErrorKind,Needed,need_more};

      let input = $input;

      use $crate::InputLength;
      use $crate::InputIter;
      use $crate::Slice;
      if input.input_len() == 0 {
        need_more(input, Needed::Unknown)
      } else {
        match input.position(|c| !$submac!(c, $($args)*)) {
          Some(0) => {
            let e = ErrorKind::TakeWhile1::<u32>;
            Err(Err::Error(error_position!(e,input)))
          },
          Some(n) => {
            Ok((input.slice(n..), input.slice(..n)))
          },
          None    => {
            Ok((input.slice(input.input_len()..), input))
          }
        }
      }
    }
  );
  ($input:expr, $f:expr) => (
    take_while1!($input, call!($f));
  );
);

/// `take_till!(T -> bool) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest list of bytes until the provided function succeeds
///
/// The argument is either a function `&[T] -> bool` or a macro returning a `bool
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!( till_colon, take_till!(|ch| ch == b':') );
///
///  let r = till_colon(&b"abcd:efgh"[..]);
///  assert_eq!(r, Ok((&b":efgh"[..], &b"abcd"[..])));
///  let r2 = till_colon(&b":abcdefgh"[..]); // empty match is allowed
///  assert_eq!(r2, Ok((&b":abcdefgh"[..], &b""[..])));
/// # }
/// ```
#[macro_export]
macro_rules! take_till (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;

      let input = $input;

      use $crate::InputLength;
      use $crate::InputIter;
      use $crate::Slice;
      match input.position(|c| $submac!(c, $($args)*)) {
        Some(n) => Ok((input.slice(n..), input.slice(..n))),
        None    => Ok((input.slice(input.input_len()..), input))
      }
    }
  );
  ($input:expr, $f:expr) => (
    take_till!($input, call!($f));
  );
);

/// `take_till1!(T -> bool) => &[T] -> IResult<&[T], &[T]>`
/// returns the longest non empty list of bytes until the provided function succeeds
///
/// The argument is either a function `&[T] -> bool` or a macro returning a `bool
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::{Err,ErrorKind};
/// # fn main() {
///  named!( till1_colon, take_till1!(|ch| ch == b':') );
///
///  let r = till1_colon(&b"abcd:efgh"[..]);
///  assert_eq!(r, Ok((&b":efgh"[..], &b"abcd"[..])));
///
///  let r2 = till1_colon(&b":abcdefgh"[..]); // empty match is error
///  assert_eq!(r2, Err(Err::Error(error_position!(ErrorKind::TakeTill1, &b":abcdefgh"[..]))));
/// # }
/// ```
#[macro_export]
macro_rules! take_till1 (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,Needed,ErrorKind,need_more};

      let input = $input;

      use $crate::InputLength;
      use $crate::InputIter;
      use $crate::Slice;
      if input.input_len() == 0 {
        need_more(input, Needed::Unknown)
      } else {
        match input.position(|c| $submac!(c, $($args)*)) {
          Some(0) => {
            let e = ErrorKind::TakeTill1::<u32>;
            Err(Err::Error(error_position!(e,input)))
          },
          Some(n) => Ok((input.slice(n..), input.slice(..n))),
          None    => Ok((input.slice(input.input_len()..), input))
        }
      }
    }
  );
  ($input:expr, $f:expr) => (
    take_till1!($input, call!($f));
  );
);

/// `take!(nb) => &[T] -> IResult<&[T], &[T]>`
/// generates a parser consuming the specified number of bytes
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  // Desmond parser
///  named!(take5, take!( 5 ) );
///
///  let a = b"abcdefgh";
///
///  assert_eq!(take5(&a[..]), Ok((&b"fgh"[..], &b"abcde"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! take (
  ($i:expr, $count:expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Needed,IResult};

      use $crate::InputIter;
      use $crate::Slice;
      let input = $i;

      let cnt = $count as usize;

      let res: IResult<_,_,u32> = match input.slice_index(cnt) {
        None        => $crate::need_more($i, Needed::Size(cnt)),
        //FIXME: use the InputTake trait
        Some(index) => Ok((input.slice(index..), input.slice(..index)))
      };
      res
    }
  );
);

/// `take_str!(nb) => &[T] -> IResult<&[T], &str>`
/// same as take! but returning a &str
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!(take5( &[u8] ) -> &str, take_str!( 5 ) );
///
///  let a = b"abcdefgh";
///
///  assert_eq!(take5(&a[..]), Ok((&b"fgh"[..], "abcde")));
/// # }
/// ```
#[macro_export]
macro_rules! take_str (
 ( $i:expr, $size:expr ) => (
    {
      let input: &[u8] = $i;

      map_res!(input, take!($size), ::std::str::from_utf8)
    }
  );
);

/// `take_until_and_consume!(tag) => &[T] -> IResult<&[T], &[T]>`
/// generates a parser consuming bytes until the specified byte sequence is found, and consumes it
///
/// The parsed input and the tag are removed from the remainder.
/// (As opposed to `take_until!` that does not remove the tag from the remainder.)
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!(x, take_until_and_consume!("foo"));
///  let r = x(&b"abcd foo efgh"[..]);
///  assert_eq!(r, Ok((&b" efgh"[..], &b"abcd "[..])));
/// # }
/// ```
#[macro_export]
macro_rules! take_until_and_consume (
  ($i:expr, $substr:expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,Needed,IResult,ErrorKind,need_more};

      use $crate::InputLength;
      use $crate::FindSubstring;
      use $crate::Slice;

      let res: IResult<_,_> = if $substr.input_len() > $i.input_len() {
        need_more($i, Needed::Size($substr.input_len()))
      } else {
        match ($i).find_substring($substr) {
          None => {
            let e = ErrorKind::TakeUntilAndConsume::<u32>;
            Err(Err::Error(error_position!(e,$i)))
          },
          Some(index) => {
            Ok(($i.slice(index+$substr.input_len()..), $i.slice(0..index)))
          },
        }
      };
      res
    }
  );
);

/// `take_until_and_consume1!(tag) => &[T] -> IResult<&[T], &[T]>`
/// generates a parser consuming bytes (at least 1) until the specified byte sequence is found, and consumes it
///
/// The parsed input and the tag are removed from the remainder.
/// (As opposed to `take_until1!` that does not remove the tag from the remainder.)
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!(x, take_until_and_consume!("foo"));
///  let r = x(&b"abcd foo efgh"[..]);
///  assert_eq!(r, Ok((&b" efgh"[..], &b"abcd "[..])));
/// # }
/// ```
#[macro_export]
macro_rules! take_until_and_consume1 (
  ($i:expr, $substr:expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,Needed,IResult,ErrorKind,need_more};

      use $crate::InputLength;
      use $crate::FindSubstring;
      use $crate::Slice;

      let res: IResult<_,_> = if 1 + $substr.input_len() > $i.input_len() {
        need_more($i, Needed::Size(1+$substr.input_len()))
      } else {
        // To guarantee returning a non-empty subsequence, look for the substring
        // starting from index 1. We know that there is at least one byte available
        // because of the previous check.
        match ($i.slice(1..)).find_substring($substr) {
          None => {
            let e = ErrorKind::TakeUntilAndConsume1::<u32>;
            Err(Err::Error(error_position!(e,$i)))
          },
          Some(index) => {
            // convert the index within $i.slice(1..) to the index within $i
            let index = index + 1;
            Ok(($i.slice(index+$substr.input_len()..), $i.slice(0..index)))
          },
        }
      };
      res
    }
  );
);

/// `take_until!(tag) => &[T] -> IResult<&[T], &[T]>`
/// consumes data until it finds the specified tag.
///
/// The remainder still contains the tag.
/// (As opposed to `take_until!` which removes it from the remainder.)
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!(x, take_until!("foo"));
///  let r = x(&b"abcd foo efgh"[..]);
///  assert_eq!(r, Ok((&b"foo efgh"[..], &b"abcd "[..])));
/// # }
/// ```
#[macro_export]
macro_rules! take_until (
  ($i:expr, $substr:expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,Needed,IResult,ErrorKind,need_more};

      use $crate::InputLength;
      use $crate::FindSubstring;
      use $crate::Slice;

      let res: IResult<_,_> = if $substr.input_len() > $i.input_len() {
        need_more($i, Needed::Size($substr.input_len()))
      } else {
        match ($i).find_substring($substr) {
          None => {
            let e = ErrorKind::TakeUntil::<u32>;
            Err(Err::Error(error_position!(e,$i)))
          },
          Some(index) => {
            Ok(($i.slice(index..), $i.slice(0..index)))
          },
        }
      };
      res
    }
  );
);

/// `take_until1!(tag) => &[T] -> IResult<&[T], &[T]>`
/// consumes data (at least one byte) until it finds the specified tag
///
/// The remainder still contains the tag.
/// (As opposed to `take_until_and_consume1!` which removes it from the remainder.)
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!(x, take_until1!("foo"));
///
///  let r = x(&b"abcd foo efgh"[..]);
///
///  assert_eq!(r, Ok((&b"foo efgh"[..], &b"abcd "[..])));
/// # }
/// ```
#[macro_export]
macro_rules! take_until1 (
  ($i:expr, $substr:expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,Needed,IResult,need_more,ErrorKind};
      use $crate::InputLength;
      use $crate::FindSubstring;
      use $crate::Slice;

      let res: IResult<_,_> = if 1+$substr.input_len() > $i.input_len() {
        need_more($i, Needed::Size($substr.input_len()))
      } else {
        match ($i).find_substring($substr) {
          None => {
            Err(Err::Error(error_position!(ErrorKind::TakeUntil::<u32>,$i)))
          },
          Some(index) => {
            Ok(($i.slice(index..), $i.slice(0..index)))
          },
        }
      };
      res
    }
  );
);

/// `take_until_either_and_consume!(tag) => &[T] -> IResult<&[T], &[T]>`
/// consumes data until it finds any of the specified characters, and consume it
///
/// The parsed input and the tag are removed from the remainder.
/// (As opposed to `take_until_either!` that does not remove the tag from the remainder.)
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!(x, take_until_either_and_consume!("012"));
///  let r = x(&b"abcd2efgh"[..]);
///  assert_eq!(r, Ok((&b"efgh"[..], &b"abcd"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! take_until_either_and_consume (
  ($input:expr, $arr:expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,Needed,IResult,need_more,ErrorKind};

      use $crate::InputLength;
      use $crate::InputIter;
      use $crate::FindToken;
      use $crate::Slice;

      if $input.input_len() == 0 {
        need_more($input, Needed::Unknown)
      } else {
        let res: IResult<_,_> = match $input.position(|c| {
          c.find_token($arr)
        }) {
          Some(0) => Err(Err::Error(error_position!(ErrorKind::TakeUntilEitherAndConsume::<u32>,$input))),
          Some(n) => {
            let res = Ok(($input.slice(n+1..), $input.slice(..n)));
            res
          },
          None    => {
            Err(Err::Error(error_position!(ErrorKind::TakeUntilEitherAndConsume::<u32>,$input)))
          }
        };
        res
      }
    }
  );
);

/// `take_until_either!(tag) => &[T] -> IResult<&[T], &[T]>`
/// consumes data until it finds any of the specified characters
///
/// The remainder still contains the tag.
/// (As opposed to `take_until_either_and_consume!` which removes it from the remainder.)
///
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!(x, take_until_either!("012"));
///  let r = x(&b"abcd2efgh"[..]);
///  assert_eq!(r, Ok((&b"2efgh"[..], &b"abcd"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! take_until_either (
  ($input:expr, $arr:expr) => (
    {
      use ::std::result::Result::*;
      use ::std::option::Option::*;
      use $crate::{Err,Needed,IResult,need_more,ErrorKind};

      use $crate::InputLength;
      use $crate::InputIter;
      use $crate::FindToken;
      use $crate::Slice;

      if $input.input_len() == 0 {
        need_more($input, Needed::Unknown)
      } else {
        let res: IResult<_,_> = match $input.position(|c| {
          c.find_token($arr)
        }) {
          Some(0) => Err(Err::Error(error_position!(ErrorKind::TakeUntilEither::<u32>,$input))),
          Some(n) => {
            let res = Ok(($input.slice(n..), $input.slice(..n)));
            res
          },
          None    => {
            Err(Err::Error(error_position!(ErrorKind::TakeUntilEither::<u32>,$input)))
          }
        };
        res
      }
    }
  );
);

/// `length_bytes!(&[T] -> IResult<&[T], nb>) => &[T] -> IResult<&[T], &[T]>`
/// Gets a number from the first parser, then extracts that many bytes from the
/// remaining stream
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::be_u8;
/// # fn main() {
///  named!(with_length, length_bytes!( be_u8 ));
///  let r = with_length(&b"\x05abcdefgh"[..]);
///  assert_eq!(r, Ok((&b"fgh"[..], &b"abcde"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! length_bytes(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      length_data!($i, $submac!($($args)*))
    }
  );
  ($i:expr, $f:expr) => (
    length_data!($i, call!($f))
  )
);

#[cfg(test)]
mod tests {
  use internal::{Err,Needed};
  use nom::{alpha, digit, hex_digit, oct_digit, alphanumeric, space, multispace};
  use util::ErrorKind;

  macro_rules! one_of (
    ($i:expr, $inp: expr) => (
      {
        if $i.is_empty() {
          Err::<_,_>(Err::Incomplete(Needed::Unknown))
        } else {
          #[inline(always)]
          fn as_bytes<T: $crate::AsBytes>(b: &T) -> &[u8] {
            b.as_bytes()
          }

          let expected = $inp;
          let bytes = as_bytes(&expected);
          one_of_bytes!($i, bytes)
        }
      }
    );
  );

  macro_rules! one_of_bytes (
    ($i:expr, $bytes: expr) => (
      {
        if $i.is_empty() {
          Err::<_,_>(Err::Incomplete(Needed::Unknown))
        } else {
          let mut found = false;

          for &i in $bytes {
            if i == $i[0] {
              found = true;
              break;
            }
          }

          if found {
            Ok((&$i[1..], $i[0] as char))
          } else {
            Err(Err::Error(error_position!(ErrorKind::OneOf::<u32>, $i)))
          }
        }
      }
    );
  );

  #[test]
  fn is_a() {
    named!(a_or_b, is_a!(&b"ab"[..]));

    let a = &b"abcd"[..];
    assert_eq!(a_or_b(a), Ok((&b"cd"[..], &b"ab"[..])));

    let b = &b"bcde"[..];
    assert_eq!(a_or_b(b), Ok((&b"cde"[..], &b"b"[..])));

    let c = &b"cdef"[..];
    assert_eq!(a_or_b(c), Err(Err::Error(error_position!(ErrorKind::IsA::<u32>,c))));

    let d = &b"bacdef"[..];
    assert_eq!(a_or_b(d), Ok((&b"cdef"[..], &b"ba"[..])));
  }

  #[test]
  fn is_not() {
    named!(a_or_b, is_not!(&b"ab"[..]));

    let a = &b"cdab"[..];
    assert_eq!(a_or_b(a), Ok((&b"ab"[..], &b"cd"[..])));

    let b = &b"cbde"[..];
    assert_eq!(a_or_b(b), Ok((&b"bde"[..], &b"c"[..])));

    let c = &b"abab"[..];
    assert_eq!(a_or_b(c), Err(Err::Error(error_position!(ErrorKind::IsNot,c))));

    let d = &b"cdefba"[..];
    assert_eq!(a_or_b(d), Ok((&b"ba"[..], &b"cdef"[..])));

    let e = &b"e"[..];
    assert_eq!(a_or_b(e), Ok((&b""[..], &b"e"[..])));

    let f = &b"fghi"[..];
    assert_eq!(a_or_b(f), Ok((&b""[..], &b"fghi"[..])));
  }

  #[allow(unused_variables)]
  #[test]
  fn escaping() {
    named!(esc, escaped!(call!(alpha), '\\', one_of!("\"n\\")));
    assert_eq!(esc(&b"abcd"[..]), Ok((&b""[..], &b"abcd"[..])));
    assert_eq!(esc(&b"ab\\\"cd"[..]), Ok((&b""[..], &b"ab\\\"cd"[..])));
    assert_eq!(esc(&b"\\\"abcd"[..]), Ok((&b""[..], &b"\\\"abcd"[..])));
    assert_eq!(esc(&b"\\n"[..]), Ok((&b""[..], &b"\\n"[..])));
    assert_eq!(esc(&b"ab\\\"12"[..]), Ok((&b"12"[..], &b"ab\\\""[..])));
    assert_eq!(esc(&b"AB\\"[..]), Err(Err::Incomplete(Needed::Unknown)));
    assert_eq!(esc(&b"AB\\A"[..]), Err(Err::Error(error_node_position!(ErrorKind::Escaped, &b"AB\\A"[..],
      error_position!(ErrorKind::OneOf, &b"A"[..])))));

    named!(esc2, escaped!(call!(digit), '\\', one_of!("\"n\\")));
    assert_eq!(esc2(&b"12\\nnn34"[..]), Ok((&b"nn34"[..], &b"12\\n"[..])));
  }

  #[cfg(feature = "verbose-errors")]
  fn to_s(i:Vec<u8>) -> String {
    String::from_utf8_lossy(&i).into_owned()
  }

  #[cfg(feature = "verbose-errors")]
  #[test]
  fn escape_transform() {
    use std::str;

    named!(esc<String>, map!(escaped_transform!(alpha, '\\',
      alt!(
          tag!("\\")       => { |_| &b"\\"[..] }
        | tag!("\"")       => { |_| &b"\""[..] }
        | tag!("n")        => { |_| &b"\n"[..] }
      )), to_s)
    );

    assert_eq!(esc(&b"abcd"[..]), Ok((&b""[..], String::from("abcd"))));
    assert_eq!(esc(&b"ab\\\"cd"[..]), Ok((&b""[..], String::from("ab\"cd"))));
    assert_eq!(esc(&b"\\\"abcd"[..]), Ok((&b""[..], String::from("\"abcd"))));
    assert_eq!(esc(&b"\\n"[..]), Ok((&b""[..], String::from("\n"))));
    assert_eq!(esc(&b"ab\\\"12"[..]), Ok((&b"12"[..], String::from("ab\""))));
    assert_eq!(esc(&b"AB\\"[..]), Err(Err::Error(error_node_position!(ErrorKind::EscapedTransform, &b"AB\\"[..], error_position!(ErrorKind::EscapedTransform, &b"\\"[..])))));
    assert_eq!(esc(&b"AB\\A"[..]), Err(Err::Error(error_node_position!(ErrorKind::EscapedTransform, &b"AB\\A"[..],
      error_position!(ErrorKind::Alt, &b"A"[..])))));

    let e = "è";
    let a = "à";
    println!("è: {:?} | à: {:?}", str::as_bytes(e), str::as_bytes(a));
    named!(esc2< String >, map!(escaped_transform!(call!(alpha), '&',
      alt!(
          tag!("egrave;") => { |_| str::as_bytes("è") }
        | tag!("agrave;") => { |_| str::as_bytes("à") }
      )), to_s)
    );
    assert_eq!(esc2(&b"ab&egrave;DEF"[..]), Ok((&b""[..], String::from("abèDEF"))));
    assert_eq!(esc2(&b"ab&egrave;D&agrave;EF"[..]), Ok((&b""[..], String::from("abèDàEF"))));
  }

  #[test]
  fn issue_84() {
    let r0 = is_a!(&b"aaaaefgh"[..], "abcd");
    assert_eq!(r0, Ok((&b"efgh"[..], &b"aaaa"[..])));
    let r1 = is_a!(&b"aaaa"[..], "abcd");
    assert_eq!(r1, Ok((&b""[..], &b"aaaa"[..])));
    let r2 = is_a!(&b"1"[..], "123456789");
    assert_eq!(r2, Ok((&b""[..], &b"1"[..])));
  }

  #[test]
  fn take_str_test() {
    let a = b"omnomnom";

    assert_eq!(take_str!(&a[..], 5), Ok((&b"nom"[..], "omnom")));
    assert_eq!(take_str!(&a[..], 9), Err(Err::Incomplete(Needed::Size(9))));
  }

  #[test]
  fn take_until_and_consume() {
    named!(x, take_until_and_consume!("efgh"));
    let r = x(&b"abcdabcdefghijkl"[..]);
    assert_eq!(r, Ok((&b"ijkl"[..], &b"abcdabcd"[..])));
    println!("Done 1\n");

    let r2 = x(&b"abcdabcdefgh"[..]);
    assert_eq!(r2, Ok((&b""[..], &b"abcdabcd"[..])));
    println!("Done 2\n");

    let r3 = x(&b"abcefg"[..]);
    assert_eq!(r3,  Err(Err::Error(error_position!(ErrorKind::TakeUntilAndConsume, &b"abcefg"[..]))));
    println!("Done 3\n");

    assert_eq!(
      x(&b"ab"[..]),
      Err(Err::Incomplete(Needed::Size(4)))
    );
  }

  #[test]
  fn take_until_and_consume1() {
    named!(x, take_until_and_consume1!("efgh"));
    let r = x(&b"abcdabcdefghijkl"[..]);
    assert_eq!(r, Ok((&b"ijkl"[..], &b"abcdabcd"[..])));
    println!("Done 1\n");

    let r2 = x(&b"abcdabcdefgh"[..]);
    assert_eq!(r2, Ok((&b""[..], &b"abcdabcd"[..])));
    println!("Done 2\n");

    let r3 = x(&b"abcefg"[..]);
    assert_eq!(r3, Err(Err::Error(error_position!(ErrorKind::TakeUntilAndConsume1, &b"abcefg"[..]))));
    println!("Done 3\n");

    let r4 = x(&b"efgh"[..]);
    assert_eq!(r4, Err(Err::Incomplete(Needed::Size(5))));
    println!("Done 4\n");

    named!(x2, take_until_and_consume1!(""));
    let r5 = x2(&b""[..]);
    assert_eq!(r5, Err(Err::Incomplete(Needed::Size(1))));
    println!("Done 5\n");

    let r6 = x2(&b"a"[..]);
    assert_eq!(r6, Ok((&b""[..], &b"a"[..])));
    println!("Done 6\n");

    let r7 = x(&b"efghi"[..]);
    assert_eq!(r7, Err(Err::Error(error_position!(ErrorKind::TakeUntilAndConsume1, &b"efghi"[..]))));
  }

  #[test]
  fn take_until_either() {
    named!(x, take_until_either!("!."));
    assert_eq!(
      x(&b"123!abc"[..]),
      Ok((&b"!abc"[..], &b"123"[..]))
    );
  }

  #[test]
  fn take_until_either_incomplete() {
    named!(x, take_until_either!("!."));
    assert_eq!(
      x(&b"123"[..]),
      Err(Err::Error(error_position!(ErrorKind::TakeUntilEither, &b"123"[..])))
    );
  }

  #[test]
  fn take_until_either_and_consume() {
    named!(x, take_until_either_and_consume!("!."));
    assert_eq!(
      x(&b"123.abc"[..]),
      Ok((&b"abc"[..], &b"123"[..]))
    );
  }


  #[test]
  fn take_until_incomplete() {
    named!(y, take_until!("end"));
    assert_eq!(
      y(&b"nd"[..]),
      Err(Err::Incomplete(Needed::Size(3)))
    );
    assert_eq!(
      y(&b"123"[..]),
      Err(Err::Error(error_position!(ErrorKind::TakeUntil, &b"123"[..])))
    );
  }

  #[test]
  fn recognize() {
    named!(x, recognize!(delimited!(tag!("<!--"), take!(5), tag!("-->"))));
    let r = x(&b"<!-- abc --> aaa"[..]);
    assert_eq!(r, Ok((&b" aaa"[..], &b"<!-- abc -->"[..])));

    let empty = &b""[..];

    named!(ya, recognize!(alpha));
    let ra = ya(&b"abc"[..]);
    assert_eq!(ra, Ok((empty, &b"abc"[..])));

    named!(yd, recognize!(digit));
    let rd = yd(&b"123"[..]);
    assert_eq!(rd, Ok((empty, &b"123"[..])));

    named!(yhd, recognize!(hex_digit));
    let rhd = yhd(&b"123abcDEF"[..]);
    assert_eq!(rhd, Ok((empty, &b"123abcDEF"[..])));

    named!(yod, recognize!(oct_digit));
    let rod = yod(&b"1234567"[..]);
    assert_eq!(rod, Ok((empty, &b"1234567"[..])));

    named!(yan, recognize!(alphanumeric));
    let ran = yan(&b"123abc"[..]);
    assert_eq!(ran, Ok((empty, &b"123abc"[..])));

    named!(ys, recognize!(space));
    let rs = ys(&b" \t"[..]);
    assert_eq!(rs, Ok((empty, &b" \t"[..])));

    named!(yms, recognize!(multispace));
    let rms = yms(&b" \t\r\n"[..]);
    assert_eq!(rms, Ok((empty, &b" \t\r\n"[..])));
  }

  #[test]
  fn take_while() {
    use nom::is_alphabetic;
    named!(f, take_while!(is_alphabetic));
    let a = b"";
    let b = b"abcd";
    let c = b"abcd123";
    let d = b"123";

    assert_eq!(f(&a[..]), Ok((&a[..], &a[..])));
    assert_eq!(f(&b[..]), Ok((&a[..], &b[..])));
    assert_eq!(f(&c[..]), Ok((&d[..], &b[..])));
    assert_eq!(f(&d[..]), Ok((&d[..], &a[..])));
  }

  #[test]
  fn take_while1() {
    use nom::is_alphabetic;
    named!(f, take_while1!(is_alphabetic));
    let a = b"";
    let b = b"abcd";
    let c = b"abcd123";
    let d = b"123";

    assert_eq!(f(&a[..]), Err(Err::Incomplete(Needed::Unknown)));
    assert_eq!(f(&b[..]), Ok((&a[..], &b[..])));
    assert_eq!(f(&c[..]), Ok((&b"123"[..], &b[..])));
    assert_eq!(f(&d[..]), Err(Err::Error(error_position!(ErrorKind::TakeWhile1, &d[..]))));
  }

  #[test]
  fn take_till() {
    use nom::is_alphabetic;
    named!(f, take_till!(is_alphabetic));
    let a = b"";
    let b = b"abcd";
    let c = b"123abcd";
    let d = b"123";

    assert_eq!(f(&a[..]), Ok((&b""[..], &b""[..])));
    assert_eq!(f(&b[..]), Ok((&b"abcd"[..], &b""[..])));
    assert_eq!(f(&c[..]), Ok((&b"abcd"[..], &b"123"[..])));
    assert_eq!(f(&d[..]), Ok((&b""[..], &b"123"[..])));
  }

  #[test]
  fn take_till1() {
    use nom::is_alphabetic;
    named!(f, take_till1!(is_alphabetic));
    let a = b"";
    let b = b"abcd";
    let c = b"123abcd";
    let d = b"123";

    assert_eq!(f(&a[..]), Err(Err::Incomplete(Needed::Unknown)));
    assert_eq!(f(&b[..]), Err(Err::Error(error_position!(ErrorKind::TakeTill1, &b[..]))));
    assert_eq!(f(&c[..]), Ok((&b"abcd"[..], &b"123"[..])));
    assert_eq!(f(&d[..]), Ok((&b""[..], &b"123"[..])));
  }

  #[cfg(feature = "nightly")]
  use test::Bencher;

  #[cfg(feature = "nightly")]
  #[bench]
  fn take_while_bench(b: &mut Bencher) {
    use nom::is_alphabetic;
    named!(f, take_while!(is_alphabetic));
    b.iter(|| {
      f(&b"abcdefghijklABCDEejfrfrjgro12aa"[..])
    });
  }

  #[test]
  #[cfg(feature = "std")]
  fn recognize_take_while() {
    use nom::is_alphanumeric;
    named!(x, take_while!(is_alphanumeric));
    named!(y, recognize!(x));
    assert_eq!(x(&b"ab"[..]), Ok((&[][..], &b"ab"[..])));
    println!("X: {:?}", x(&b"ab"[..]));
    assert_eq!(y(&b"ab"[..]), Ok((&[][..], &b"ab"[..])));
  }

  #[test]
  fn length_bytes() {
    use nom::le_u8;
    named!(x, length_bytes!(le_u8));
    assert_eq!(x(b"\x02..>>"), Ok((&b">>"[..], &b".."[..])));
    assert_eq!(x(b"\x02.."), Ok((&[][..], &b".."[..])));
    assert_eq!(x(b"\x02."), Err(Err::Incomplete(Needed::Size(2))));
    assert_eq!(x(b"\x02"), Err(Err::Incomplete(Needed::Size(2))));

    named!(y, do_parse!(tag!("magic") >> b: length_bytes!(le_u8) >> (b)));
    assert_eq!(y(b"magic\x02..>>"), Ok((&b">>"[..], &b".."[..])));
    assert_eq!(y(b"magic\x02.."), Ok((&[][..], &b".."[..])));
    assert_eq!(y(b"magic\x02."), Err(Err::Incomplete(Needed::Size(2))));
    assert_eq!(y(b"magic\x02"), Err(Err::Incomplete(Needed::Size(2))));
  }

  #[test]
  fn case_insensitive() {
    named!(test, tag_no_case!("ABcd"));
    assert_eq!(test(&b"aBCdefgh"[..]), Ok((&b"efgh"[..], &b"aBCd"[..])));
    assert_eq!(test(&b"abcdefgh"[..]), Ok((&b"efgh"[..], &b"abcd"[..])));
    assert_eq!(test(&b"ABCDefgh"[..]), Ok((&b"efgh"[..], &b"ABCD"[..])));
    assert_eq!(test(&b"ab"[..]), Err(Err::Incomplete(Needed::Size(4))));
    assert_eq!(test(&b"Hello"[..]), Err(Err::Error(error_position!(ErrorKind::Tag, &b"Hello"[..]))));
    assert_eq!(test(&b"Hel"[..]), Err(Err::Error(error_position!(ErrorKind::Tag, &b"Hel"[..]))));

    named!(test2<&str, &str>, tag_no_case!("ABcd"));
    assert_eq!(test2("aBCdefgh"), Ok(("efgh", "aBCd")));
    assert_eq!(test2("abcdefgh"), Ok(("efgh", "abcd")));
    assert_eq!(test2("ABCDefgh"), Ok(("efgh", "ABCD")));
    assert_eq!(test2("ab"), Err(Err::Incomplete(Needed::Size(4))));
    assert_eq!(test2("Hello"), Err(Err::Error(error_position!(ErrorKind::Tag, &"Hello"[..]))));
    assert_eq!(test2("Hel"), Err(Err::Error(error_position!(ErrorKind::Tag, &"Hel"[..]))));
  }

  #[test]
  fn tag_fixed_size_array() {
    named!(test, tag!([0x42]));
    named!(test2, tag!(&[0x42]));
    let input = [0x42, 0x00];
    assert_eq!(test(&input), Ok((&b"\x00"[..], &b"\x42"[..])));
    assert_eq!(test2(&input), Ok((&b"\x00"[..], &b"\x42"[..])));
  }
}
