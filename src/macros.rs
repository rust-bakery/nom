extern crate collections;

use std::fmt::Debug;
use internal::*;
use internal::IResult::*;

#[macro_export]
macro_rules! closure (
    ($ty:ty, $submac:ident!( $($args:tt)* )) => (
        |i: $ty| { $submac!(i, $($args)*) }
    );
    ($submac:ident!( $($args:tt)* )) => (
        |i| { $submac!(i, $($args)*) }
    );
);

#[macro_export]
macro_rules! named (
    ($name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: $i ) -> $o {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: $i ) -> IResult<$i, $o> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: &[u8] ) -> IResult<&[u8], &[u8]> {
            $submac!(i, $($args)*)
        }
    );
);


/// declares a byte array as a suite to recognize
///
/// consumes the recognized characters
///
/// ```ignore
///  tag!(x "abcd");
///  let r = Done((), b"abcdabcdefgh").flat_map(x);
///  assert_eq!(r, Done(b"efgh", b"abcd"));
/// ```
#[macro_export]
macro_rules! tag (
  ($i:expr, $inp: expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      if bytes.len() > $i.len() {
        Incomplete(Needed::Size(bytes.len() as u32))
      } else if &$i[0..bytes.len()] == bytes {
        Done(&$i[bytes.len()..], &$i[0..bytes.len()])
      } else {
        Error(0)
      }
    }
  );
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      if bytes.len() > i.len() {
        return Incomplete(Needed::Size(bytes.len() as u32));
      }

      if &i[0..bytes.len()] == bytes {
        Done(&i[bytes.len()..], &i[0..bytes.len()])
      } else {
        Error(0)
      }
    }
  );
);

#[macro_export]
macro_rules! map(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        Error(ref e) => Error(*e),
        Incomplete(Needed::Unknown) => Incomplete(Needed::Unknown),
        Incomplete(Needed::Size(i)) => Incomplete(Needed::Size(i)),
        Done(i, o) => Done(i, $submac2!(o, $($args2)*))
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    {
      let fun2 = $g;
      match $submac!($i, $($args)*) {
        Error(ref e) => Error(*e),
        Incomplete(Needed::Unknown) => Incomplete(Needed::Unknown),
        Incomplete(Needed::Size(i)) => Incomplete(Needed::Size(i)),
        Done(i, o) => Done(i, fun2(o))
      }
    }
  );
  ($i:expr, $f:expr, $g:expr) => (
    {
      let fun  = $f;
      let fun2 = $g;
      match fun($i) {
        Error(ref e) => Error(*e),
        Incomplete(Needed::Unknown) => Incomplete(Needed::Unknown),
        Incomplete(Needed::Size(i)) => Incomplete(Needed::Size(i)),
        Done(i, o) => Done(i,fun2(o))
      }
    }
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let fun  = $f;
      match fun($i) {
        Error(ref e) => Error(*e),
        Incomplete(Needed::Unknown) => Incomplete(Needed::Unknown),
        Incomplete(Needed::Size(i)) => Incomplete(Needed::Size(i)),
        Done(i, o) => Done(i, $submac!(o, $($args)*))
      }
    }
  );
);

#[macro_export]
macro_rules! map_res(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        Error(ref e) => Error(*e),
        Incomplete(Needed::Unknown) => Incomplete(Needed::Unknown),
        Incomplete(Needed::Size(i)) => Incomplete(Needed::Size(i)),
        Done(i, o) => match $submac2!(o, $($args2)*) {
          Ok(output) => Done(i, output),
          Err(_)     => Error(0)
        }
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    {
      let fun2 = $g;
      match $submac!($i, $($args)*) {
        Error(ref e) => Error(*e),
        Incomplete(Needed::Unknown) => Incomplete(Needed::Unknown),
        Incomplete(Needed::Size(i)) => Incomplete(Needed::Size(i)),
        Done(i, o) => match fun2(o) {
          Ok(output) => Done(i, output),
          Err(_)     => Error(0)
        }
      }
    }
  );
  ($i:expr, $f:expr, $g:expr) => (
    {
      let fun  = $f;
      let fun2 = $g;
      match fun($i) {
        Error(ref e) => Error(*e),
        Incomplete(Needed::Unknown) => Incomplete(Needed::Unknown),
        Incomplete(Needed::Size(i)) => Incomplete(Needed::Size(i)),
        Done(i, o) => match fun2(o) {
          Ok(output) => Done(i, output),
          Err(_)     => Error(0)
        }
      }
    }
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let fun  = $f;
      match fun($i) {
        Error(ref e) => Error(*e),
        Incomplete(Needed::Unknown) => Incomplete(Needed::Unknown),
        Incomplete(Needed::Size(i)) => Incomplete(Needed::Size(i)),
        Done(i, o) => match $submac!(o, $($args)*) {
          Ok(output) => Done(i, output),
          Err(_)     => Error(0)
        }
      }
    }
  );
);

#[macro_export]
macro_rules! map_opt(
  ($i:expr, $f:ident, $g:ident) => (
    match $f($i) {
      Error(ref e) => Error(e),
      Incomplete(Needed::Unknown) => Incomplete(Needed::Unknown),
      Incomplete(Needed::Size(i)) => Incomplete(Needed::Size(i)),
      Done(i, o) => match $g(o) {
        Some(output) => Done(i, output),
        None         => Error(0)
      }
    }
  );
);

/// chains parsers and assemble the results through a closure
///
/// ```ignore
/// #[derive(PartialEq,Eq,Debug)]
/// struct B {
///   a: u8,
///   b: Option<u8>
/// }
///
/// tag!(x "abcd");
/// tag!(y "efgh");
///
/// fn ret_int(i:&[u8]) -> IResult<&[u8], u8> { Done(i, 1) };
/// fn ret_y(i:&[u8]) -> IResult<&[u8], u8> { y(i).map(|_| 1) }; // return 1 if the "efgh" tag is found
///
///  chain!(z<&[u8], u8>,
///    x            ~
///    aa: ret_int  ~     // the result of that parser will be used in the closure
///    x?           ~     // this parser is optional
///    bb: ret_y?   ,     // the result of that parser is an option
///    ||{B{a: aa, b: bb}}
///  );
///
/// // the first "abcd" tag is not present, we have an error
/// let r1 = z(b"efgh");
/// assert_eq!(r1, Error(0));
///
/// // everything is present, everything is parsed
/// let r2 = z(b"abcdabcdefgh");
/// assert_eq!(r2, Done(b"", B{a: 1, b: Some(1)}));
///
/// // the second "abcd" tag is optional
/// let r3 = z(b"abcdefgh");
/// assert_eq!(r3, Done(b"", B{a: 1, b: Some(1)}));
///
/// // the result of ret_y is optional, as seen in the B structure
/// let r4 = z(b"abcdabcd");
/// assert_eq!(r4, Done(b"", B{a: 1, b: None}));
/// ```
#[macro_export]
macro_rules! chain (
  ($i:expr, $($rest:tt)*) => (
    chaining_parser!($i, $($rest)*)
  );
);

#[macro_export]
macro_rules! chaining_parser (
  ($i:expr, $e:ident ~ $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,_)     => {
        chaining_parser!(i, $($rest)*)
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    match $submac!($i, $($args)*) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,_)     => {
        chaining_parser!(i, $($rest)*)
      }
    }
  );

  ($i:expr, $e:ident ? ~ $($rest:tt)*) => (
    match $e($i) {
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Error(_)      => {
        chaining_parser!($i, $($rest)*)
      },
      IResult::Done(i,_)     => {
        chaining_parser!(i, $($rest)*)
      }
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => (
    match  $submac!($i, $($args)*) {
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Error(_)      => {
        chaining_parser!($i, $($rest)*)
      },
      IResult::Done(i,_)     => {
        chaining_parser!(i, $($rest)*)
      }
    }
  );

  ($i:expr, $field:ident : $e:ident ~ $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,o)     => {
        let $field = o;
        chaining_parser!(i, $($rest)*)
      }
    }
  );

  ($i:expr, $field:ident : $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    match  $submac!($i, $($args)*) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,o)     => {
        let $field = o;
        chaining_parser!(i, $($rest)*)
      }
    }
  );

  ($i:expr, $field:ident : $e:ident ? ~ $($rest:tt)*) => (
    match $e($i) {
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Error(_)      => {
        let $field = None;
        chaining_parser!($i, $($rest)*)
      },
      IResult::Done(i,o)     => {
        let $field = Some(o);
        chaining_parser!(i, $($rest)*)
      }
    }
  );

  ($i:expr, $field:ident : $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => (
    match  $submac!($i, $($args)*) {
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Error(_)      => {
        let $field = None;
        chaining_parser!($i, $($rest)*)
      },
      IResult::Done(i,o)     => {
        let $field = Some(o);
        chaining_parser!(i, $($rest)*)
      }
    }
  );

  // ending the chain
  ($i:expr, $e:ident, $assemble:expr) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,_)     => {
        IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,_)     => {
        IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $e:ident ?, $assemble:expr) => (
    match $e($i) {
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Error(_)      => {
        IResult::Done($i, $assemble())
      },
      IResult::Done(i,_)     => {
        IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ) ?, $assemble:expr) => (
    match $submac!($i, $($args)*) {
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Error(_)      => {
        IResult::Done($i, $assemble())
      },
      IResult::Done(i,_)     => {
        IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $field:ident : $e:ident, $assemble:expr) => (
    match $e($i) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,o)     => {
        let $field = o;
        IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $field:ident : $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      IResult::Error(e)      => IResult::Error(e),
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Done(i,o)     => {
        let $field = o;
        IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $field:ident : $e:ident ? , $assemble:expr) => (
    match $e($i) {
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Error(_)      => {
        let $field = None;
        IResult::Done($i, $assemble())
      },
      IResult::Done(i,o)     => {
        let $field = Some(o);
        IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $field:ident : $submac:ident!( $($args:tt)* ) ? , $assemble:expr) => (
    match $submac!($i, $($args)*)  {
      IResult::Incomplete(i) => IResult::Incomplete(i),
      IResult::Error(_)      => {
        let $field = None;
        IResult::Done($i, $assemble())
      },
      IResult::Done(i,o)     => {
        let $field = Some(o);
        IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $assemble:expr) => (
    IResult::Done($i, $assemble())
  )
);

/// try a list of parser, return the result of the first successful one
///
/// Incomplete results are ignored
///
/// ```ignore
///  tag!(x "abcd");
///  tag!(y "efgh");
///  alt!(test<&[u8], &[u8]> x | y);
///  let r1 = test(b"abcdefgh"));
///  assert_eq!(r1, Done(b"efgh", b"abcd"));
///  let r2 = test(b"efghijkl"));
///  assert_eq!(r2, Done(b"ijkl", b"efgh"));
/// ```
#[macro_export]
macro_rules! alt (
  ($name:ident<$i:ty,$o:ty>, $($rest:tt)*) => (
    fn $name(i:$i) -> IResult<$i,$o>{
      alt_parser!(i, $($rest)*)
    }
  );
  ($i:expr, $($rest:tt)*) => (
    {
      alt_parser!($i, $($rest)*)
    }
  );
);

#[macro_export]
macro_rules! alt_parser (
  ($i:expr, $e:ident | $($rest:tt)*) => (
    match $e($i) {
      IResult::Error(_)      => alt_parser!($i, $($rest)*),
      IResult::Incomplete(_) => alt_parser!($i, $($rest)*),
      IResult::Done(i,o)     => IResult::Done(i,o)
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)*) | $($rest:tt)*) => (
    {
      match $submac!($i, $($args)*) {
        IResult::Error(_)      => alt_parser!($i, $($rest)*),
        IResult::Incomplete(_) => alt_parser!($i, $($rest)*),
        IResult::Done(i,o)     => IResult::Done(i,o)
      }
    }
  );

  ($i:expr, $e:ident) => (
    match $e($i) {
      IResult::Error(_)      => alt_parser!($i),
      IResult::Incomplete(_) => alt_parser!($i),
      IResult::Done(i,o)     => IResult::Done(i,o)
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)*)) => (
    match $submac!($i, $($args)*) {
      IResult::Error(_)      => alt_parser!($i),
      IResult::Incomplete(_) => alt_parser!($i),
      IResult::Done(i,o)     => IResult::Done(i,o)
    }
  );

  ($i:expr) => (
    IResult::Error(1)
  );
);

/// returns the longest list of bytes that do not appear in the provided array
///
/// ```ignore
///  is_not!(not_space b" \t\r\n");
///  let r = not_space(b"abcdefgh\nijkl"));
///  assert_eq!(r, Done(b"\nijkl", b"abcdefgh"));
/// ```
#[macro_export]
macro_rules! is_not(
  ($input:expr, $arr:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $arr;
      let bytes = as_bytes(&expected);

      for idx in 0..$input.len() {
        for &i in bytes.iter() {
          if $input[idx] == i {
            return IResult::Done(&$input[idx..], &$input[0..idx])
          }
        }
      }
      IResult::Done(b"", $input)
    }
  );
  ($name:ident $arr:expr) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $arr;
      let bytes = as_bytes(&expected);

      for idx in 0..input.len() {
        for &i in bytes.iter() {
          if input[idx] == i {
            return IResult::Done(&input[idx..], &input[0..idx])
          }
        }
      }
      IResult::Done(b"", input)
    }
  );
);

/// returns the longest list of bytes that appear in the provided array
///
/// ```ignore
///  is_a!(abcd b"abcd");
///  let r1 = abcd(b"aaaaefgh"));
///  assert_eq!(r1, Done(b"efgh", b"aaaa"));
///
///  let r2 = abcd(b"dcbaefgh"));
///  assert_eq!(r2, Done(b"efgh", b"dcba"));
/// ```
#[macro_export]
macro_rules! is_a(
  ($input:expr, $arr:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $arr;
      let bytes = as_bytes(&expected);

      for idx in 0..$input.len() {
        let mut res = false;
        for &i in bytes.iter() {
          if $input[idx] == i {
            res = true;
            break;
          }
        }
        if !res {
          return IResult::Done(&$input[idx..], &$input[0..idx])
        }
      }
      IResult::Done(b"", $input)
    }
  );
  ($name:ident $arr:expr) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $arr;
      let bytes = as_bytes(&expected);

      for idx in 0..input.len() {
        let mut res = false;
        for &i in bytes.iter() {
          if input[idx] == i {
            res = true;
            break;
          }
        }
        if !res {
          return IResult::Done(&input[idx..], &input[0..idx])
        }
      }
      IResult::Done(b"", input)
    }
  );
);

/// returns the longest list of bytes until the provided parser fails
///
/// ```ignore
///  filter!(alpha is_alphanumeric);
///  let r = alpha(b"abcd\nefgh"));
///  assert_eq!(r, Done(b"\nefgh", b"abcd"));
/// ```
#[macro_export]
macro_rules! filter(
  ($input:expr, $arr:expr) => (
    {
      for idx in 0..$input.len() {
        if !$f($input[idx]) {
          return IResult::Done(&$input[idx..], &$input[0..idx])
        }
      }
      IResult::Done(b"", $input)
    }
  );
  ($name:ident $f:ident) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      for idx in 0..input.len() {
        if !$f(input[idx]) {
          return IResult::Done(&input[idx..], &input[0..idx])
        }
      }
      IResult::Done(b"", input)
    }
  );
  ($name:ident $submac:ident!( $($args:tt)* )) => (
    fn $name(input:&[u8]) -> IResult<&[u8], &[u8]> {
      for idx in 0..input.len() {
        if !$submac!(input[idx], $($args)*) {
          return IResult::Done(&input[idx..], &input[0..idx])
        }
      }
      IResult::Done(b"", input)
    }
  );
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      for idx in 0..$input.len() {
        if !$submac!($input[idx], $($args)*) {
          return IResult::Done(&$input[idx..], &$input[0..idx])
        }
      }
      IResult::Done(b"", $input)
    }
  );
);

/// make the underlying parser optional
///
/// returns an Option of the returned type
///
/// ```ignore
///  tag!(x "abcd");
///  opt!(o<&[u8],&[u8]> x);
///
///  let a = b"abcdef";
///  let b = b"bcdefg";
///  assert_eq!(o(a), Done(b"ef", Some(b"abcd")));
///  assert_eq!(o(b), Done(b"bcdefg", None));
/// ```
#[macro_export]
macro_rules! opt(
  ($name:ident<$i:ty,$o:ty> $f:ident) => (
    fn $name(input:$i) -> IResult<$i, Option<$o>> {
      match $f(input) {
        IResult::Done(i,o)     => IResult::Done(i, Some(o)),
        IResult::Error(_)      => IResult::Done(input, None),
        IResult::Incomplete(i) => IResult::Incomplete(i)
      }
    }
  );
  ($name:ident<$i:ty,$o:ty> $submac:ident!( $($args:tt)* )) => (
    fn $name(input:$i) -> IResult<$i, Option<$o>> {
      match $submac!(input, $($args)*) {
        IResult::Done(i,o)     => IResult::Done(i, Some(o)),
        IResult::Error(_)      => IResult::Done(input, None),
        IResult::Incomplete(i) => IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $f:ident) => (
    {
      match $f($i) {
        IResult::Done(i,o)     => IResult::Done(i, Some(o)),
        IResult::Error(_)      => IResult::Done($i, None),
        IResult::Incomplete(i) => IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        IResult::Done(i,o)     => IResult::Done(i, Some(o)),
        IResult::Error(_)      => IResult::Done($i, None),
        IResult::Incomplete(i) => IResult::Incomplete(i)
      }
    }
  );
);

/// returns a result without consuming the input
///
/// the embedded parser may return Incomplete
///
/// ```ignore
///  tag!(x "abcd");
///  peek!(ptag<&[u8], &[u8]> x);
///  let r = ptag(b"abcdefgh"));
///  assert_eq!(r, Done(b"abcdefgh", b"abcd"));
/// ```
#[macro_export]
macro_rules! peek(
  ($name:ident<$i:ty,$o:ty> $f:ident) => (
    fn $name(input:$i) -> IResult<$i, $o> {
      match $f(input) {
        IResult::Done(i,o)     => IResult::Done(input, o),
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i)
      }
    }
  );
  ($name:ident<$i:ty,$o:ty> $submac:ident!( $($args:tt)* )) => (
    fn $name(input:$i) -> IResult<$i, $o> {
      match $submac!(input, $($args)*) {
        IResult::Done(i,o)     => IResult::Done(input, o),
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $f:ident) => (
    {
      match $f($i) {
        IResult::Done(i,o)     => IResult::Done($i, o),
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        IResult::Done(i,o)     => IResult::Done($i, o),
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i)
      }
    }
  );
);

/// Applies the parser 0 or more times and returns the list of results in a Vec
///
/// the embedded parser may return Incomplete
///
/// ```ignore
///  tag!(x "abcd");
///  many0!(multi<&[u8],&[u8]> x);
///
///  let a = b"abcdabcdef";
///  let b = b"azerty";
///
///  let res = vec![b"abcd", b"abcd"];
///  assert_eq!(multi(a), Done(b"ef", res));
///  assert_eq!(multi(b), Done(b"azerty", Vec::new()));
/// ```
// 0 or more
#[macro_export]
macro_rules! many0(
  ($name:ident<$i:ty,$o:ty>, $f:ident) => (
    fn $name(input:$i) -> IResult<$i,Vec<$o>> {
      let mut begin = 0;
      let mut remaining = input.len();
      let mut res: Vec<$o> = Vec::new();
      loop {
        match $f(&input[begin..]) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            return IResult::Done(&input[begin..], res)
          }
        }
      }
    }
  );
  ($name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
    fn $name(input:$i) -> IResult<$i,Vec<$o>> {
      let mut begin = 0;
      let mut remaining = input.len();
      let mut res: Vec<$o> = Vec::new();
      loop {
        match $submac!(&input[begin..], $($args)*) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            return IResult::Done(&input[begin..], res)
          }
        }
      }
    }
  );
  ($i:expr, $f:ident) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res = Vec::new();
      loop {
        match $f(&$i[begin..]) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= $i.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            return IResult::Done(&$i[begin..], res)
          }
        }
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res = Vec::new();
      loop {
        match $submac!(&$i[begin..], $($args)*) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= $i.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            return IResult::Done(&$i[begin..], res)
          }
        }
      }
    }
  );
);

/// Applies the parser 0 or more times and returns the list of results in a Vec
///
/// the embedded parser may return Incomplete
///
/// ```ignore
///  tag!(x "abcd");
///  many1!(multi<&[u8],&[u8]> x);
///
///  let a = b"abcdabcdef";
///  let b = b"azerty";
///
///  let res = vec![b"abcd", b"abcd"];
///  assert_eq!(multi(a), Done(b"ef", res));
///  assert_eq!(multi(b), Error(0));
/// ```
#[macro_export]
macro_rules! many1(
  ($name:ident<$i:ty,$o:ty> $f:ident) => (
    fn $name(input:$i) -> IResult<$i,Vec<$o>> {
      let mut begin = 0;
      let mut remaining = input.len();
      let mut res: Vec<$o> = Vec::new();
      loop {
        match $f(&input[begin..]) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            if begin == 0 {
              return IResult::Error(0)
            } else {
            return IResult::Done(&input[begin..], res)
            }
          }
        }
      }
    }
  );
  ($name:ident<$i:ty,$o:ty> $submac:ident!( $($args:tt)* )) => (
    fn $name(input:$i) -> IResult<$i,Vec<$o>> {
      let mut begin = 0;
      let mut remaining = input.len();
      let mut res: Vec<$o> = Vec::new();
      loop {
        match $submac!(&input[begin..], $($args)*) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            if begin == 0 {
              return IResult::Error(0)
            } else {
            return IResult::Done(&input[begin..], res)
            }
          }
        }
      }
    }
  );
  ($i:expr, $f:ident) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res = Vec::new();
      loop {
        match $f(&$i[begin..]) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= $i.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            if begin == 0 {
              return IResult::Error(0)
            } else {
              return IResult::Done(&$i[begin..], res)
            }
          }
        }
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res = Vec::new();
      loop {
        match $submac!(&$i[begin..], $($args)*) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= $i.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            if begin == 0 {
              return IResult::Error(0)
            } else {
              return IResult::Done(&$i[begin..], res)
            }
          }
        }
      }
    }
  );
);

/// takes an assembling closure, and a parser, and generates a fold on the input 0 or more times
///
/// for the parser `fn p(i:I) -> IResult<I,T>` and the usage `fold0!(f<I,O>, |a,b| { ... }, p)`, this macro generates
/// `fn f(input:I, z: O) -> IResult<I,O>`
/// The closure takes as argument a value of type O and a value of type T and returns a value of type T
///
#[macro_export]
macro_rules! fold0(
  ($name:ident<$i:ty,$o:ty>, $assemble:expr, $f:ident) => (
    fn $name(input:$i, z:$o) -> IResult<$i,$o> {
      fold0_impl!(<$i, $o>, $assemble, $f, input, z);
    }
  );
  ($name:ident<$i:ty,$o:ty>, $assemble:expr, $f:expr) => (
    fn $name(input:$i, z:$o) -> IResult<$i,$o> {
      fold0_impl!(<$i, $o>, $assemble, $f, input, z);
    }
  );
);

#[macro_export]
macro_rules! fold0_impl(
  (<$i:ty,$o:ty>, $assemble:expr, $f:ident, $input:ident, $z:ident) => (
    {
      let mut begin = 0;
      let mut remaining = $input.len();
      let mut res: $o = $z;
      loop {
        match $f(&$input[begin..]) {
          IResult::Done(i,o) => {
            //res.push(o);
            res = $assemble(res, o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= $input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            return IResult::Done(&$input[begin..], res)
          }
        }
      }
    }
  );
  (<$i:ty,$o:ty>, $assemble:expr,  $submac:ident!( $($args:tt)*), $input:ident, $z:ident) => (
    {
      let mut begin = 0;
      let mut remaining = $input.len();
      let mut res: $o = $z;
      loop {
        match $submac!(&input[begin..], $($args)*) {
          IResult::Done(i,o) => {
            //res.push(o);
            res = $assemble(res, o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= $input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            return IResult::Done(&$input[begin..], res)
          }
        }
      }
    }
  );
);

/// takes an assembling closure, and a parser, and generates a fold on the input 1 or more times
///
/// for the parser `fn p(i:I) -> IResult<I,T>` and the usage `fold0!(f<I,O>, |a,b| { ... }, p)`, this macro generates
/// `fn f(input:I, z: O) -> IResult<I,O>`
/// The closure takes as argument a value of type O and a value of type T and returns a value of type T
///
#[macro_export]
macro_rules! fold1(
  ($name:ident<$i:ty,$o:ty>, $assemble:expr, $f:ident) => (
    fn $name(input:$i, z:$o) -> IResult<$i,$o> {
      fold1_impl!(<$i, $o>, $assemble, $f, input, z);
    }
  );
  ($name:ident<$i:ty,$o:ty>, $assemble:expr, $f:expr) => (
    fn $name(input:$i, z:$o) -> IResult<$i,$o> {
      fold1_impl!(<$i, $o>, $assemble, $f, input, z);
    }
  );
);

#[macro_export]
macro_rules! fold1_impl(
  (<$i:ty,$o:ty>, $assemble:expr, $f:ident, $input:ident, $z:ident) => (
    {
      let mut begin = 0;
      let mut remaining = $input.len();
      let mut res: $o = $z;
      loop {
        match $f(&$input[begin..]) {
          IResult::Done(i,o) => {
            //res.push(o);
            res = $assemble(res, o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= $input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            if begin == 0 {
              return IResult::Error(0)
            } else {
              return IResult::Done(&$input[begin..], res)
            }
          }
        }
      }
    }
  );
  (<$i:ty,$o:ty>, $assemble:expr,  $submac:ident!( $($args:tt)*), $input:ident, $z:ident) => (
    {
      let mut begin = 0;
      let mut remaining = $input.len();
      let mut res: $o = $z;
      loop {
        match $submac!(&input[begin..], $($args)*) {
          IResult::Done(i,o) => {
            //res.push(o);
            res = $assemble(res, o);
            begin += remaining - i.len();
            remaining = i.len();
            if begin >= $input.len() {
              return IResult::Done(i, res)
            }
          },
          _                  => {
            if begin == 0 {
              return IResult::Error(0)
            } else {
              return IResult::Done(&$input[begin..], res)
            }
          }
        }
      }
    }
  );
);

/// generates a parser consuming the specified number of bytes
///
/// ```ignore
///  take!(take5 5);
///
///  let a = b"abcdefgh";
///
///  assert_eq!(take5(a), Done(b"fgh", b"abcde"));
/// ```
#[macro_export]
macro_rules! take(
  ($i:expr, $count:expr) => (
    {
      if $i.len() < $count {
        Incomplete(Needed::Size($count))
      } else {
        Done(&$i[$count..],&$i[0..$count])
      }
    }
  );
  ($name:ident $count:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      if i.len() < $count {
        Incomplete(Needed::Size($count))
      } else {
        Done(&i[$count..],&i[0..$count])
      }
    }
  );
);

/// generates a parser consuming bytes until the specified byte sequence is found
#[macro_export]
macro_rules! take_until(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      for idx in 0..i.len() {
        if idx + bytes.len() > $i.len() {
          return Incomplete(Needed::Size((idx + bytes.len()) as u32))
        }
        if &$i[idx..idx + bytes.len()] == bytes {
          if idx + bytes.len() > $i.len() {
            return Done(b"", &$i[0..idx])
          } else {
            return Done(&$i[(idx + bytes.len())..], &$i[0..idx])
          }
        }
      }
      return Error(0)
    }
  );
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      for idx in 0..i.len() {
        if idx + bytes.len() > i.len() {
          return Incomplete(Needed::Size((idx + bytes.len()) as u32))
        }
        if &i[idx..idx + bytes.len()] == bytes {
          if idx + bytes.len() > i.len() {
            return Done(b"", &i[0..idx])
          } else {
            return Done(&i[(idx + bytes.len())..], &i[0..idx])
          }
        }
      }
      return Error(0)
    }
  );
);

#[macro_export]
macro_rules! take_until_and_leave(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      for idx in 0..$i.len() {
        if idx + bytes.len() > $i.len() {
          return Incomplete(Needed::Size((idx + bytes.len()) as u32))
        }
        if &$i[idx..idx+bytes.len()] == bytes {
          return Done(&$i[idx..], &$i[0..idx])
        }
      }
      return Error(0)
    }
  );
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      for idx in 0..i.len() {
        if idx + bytes.len() > i.len() {
          return Incomplete(Needed::Size((idx + bytes.len()) as u32))
        }
        if &i[idx..idx+bytes.len()] == bytes {
          return Done(&i[idx..], &i[0..idx])
        }
      }
      return Error(0)
    }
  );
);

#[macro_export]
macro_rules! take_until_either(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      for idx in 0..$i.len() {
        if idx + 1 > $i.len() {
          return Incomplete(Needed::Size(1 + idx as u32))
        }
        for &t in bytes.iter() {
          if $i[idx] == t {
            if idx + 1 > $i.len() {
              return Done(b"", &$i[0..idx])
            } else {
              return Done(&$i[(idx+1)..], &$i[0..idx])
            }
          }
        }
      }
      return Error(0)
    }
  );
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      for idx in 0..i.len() {
        if idx + 1 > i.len() {
          return Incomplete(Needed::Size(1 + idx as u32))
        }
        for &t in bytes.iter() {
          if i[idx] == t {
            if idx + 1 > i.len() {
              return Done(b"", &i[0..idx])
            } else {
              return Done(&i[(idx+1)..], &i[0..idx])
            }
          }
        }
      }
      return Error(0)
    }
  );
);

#[macro_export]
macro_rules! take_until_either_and_leave(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      for idx in 0..$i.len() {
        if idx + 1 > $i.len() {
          return Incomplete(Needed::Size(1 + idx as u32))
        }
        for &t in bytes.iter() {
          if $i[idx] == t {
            return Done(&$i[idx..], &$i[0..idx])
          }
        }
      }
      return Error(0)
    }
  );
  ($name:ident $inp:expr) => (
    fn $name(i:&[u8]) -> IResult<&[u8], &[u8]>{
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
        b.as_bytes()
      }

      let expected = $inp;
      let bytes = as_bytes(&expected);

      for idx in 0..i.len() {
        if idx + 1 > i.len() {
          return Incomplete(Needed::Size(1 + idx as u32))
        }
        for &t in bytes.iter() {
          if i[idx] == t {
            return Done(&i[idx..], &i[0..idx])
          }
        }
      }
      return Error(0)
    }
  );
);

/// returns
#[macro_export]
macro_rules! length_value(
  ($name:ident<$i:ty,$o:ty> $f:ident $g:ident) => (
    fn $name(input:$i) -> IResult<$i, Vec<$o>> {
      match $f(input) {
        Error(a)      => Error(a),
        Incomplete(i) => Incomplete(i),
        Done(i1,nb)   => {
          let length_token     = input.len() - i1.len();
          let mut begin        = 0;
          let mut remaining    = i1.len();
          let mut res: Vec<$o> = Vec::new();

          loop {
            if res.len() == nb as usize {
              return Done(&i1[begin..], res);
            }

            match $g(&i1[begin..]) {
              Done(i2,o2) => {
              res.push(o2);
                let parsed  = remaining - i2.len();
                begin      += parsed;
                remaining   = i2.len();
                if begin   >= i1.len() {
                  return Incomplete(Needed::Size((length_token + nb as usize * parsed) as u32));
                }
              },
              Error(a)      => return Error(a),
              Incomplete(Needed::Unknown) => {
                return Incomplete(Needed::Unknown)
              },
              Incomplete(Needed::Size(a)) => {
                return Incomplete(Needed::Size(length_token  as u32 + a * nb as u32))
              }
            }
          }
        }
      }
    }
  );

  ($name:ident<$i:ty,$o:ty> $f:ident $g:ident $length:expr) => (
    fn $name(input:$i) -> IResult<$i, Vec<$o>> {
      match $f(input) {
        Error(a)      => Error(a),
        Incomplete(i) => Incomplete(i),
        Done(i1,nb)   => {
          let length_token     = input.len() - i1.len();
          let mut begin        = 0;
          let mut remaining    = i1.len();
          let mut res: Vec<$o> = Vec::new();

          loop {
            if res.len() == nb as usize {
              return Done(&i1[begin..], res);
            }

            match $g(&i1[begin..]) {
              Done(i2,o2) => {
                res.push(o2);
                let parsed  = remaining - i2.len();
                begin      += parsed;
                remaining   = i2.len();
                if begin   >= i1.len() {
                  return Incomplete(Needed::Size((length_token + nb as usize * $length) as u32));
                }
              },
              Error(a)      => return Error(a),
              Incomplete(Needed::Unknown) => {
                return Incomplete(Needed::Unknown)
              },
              Incomplete(Needed::Size(_)) => {
                return Incomplete(Needed::Size(length_token  as u32 + $length * nb as u32))
              }
            }
          }
        }
      }
    }
  );
);

#[cfg(test)]
mod tests {
  use super::*;
  use map::*;
  use internal::Needed;
  use internal::IResult;
  use internal::IResult::*;

  #[test]
  fn is_a() {
    is_a!(a_or_b   b"ab");

    let a = b"abcd";
    assert_eq!(a_or_b(a), Done(b"cd", b"ab"));

    let b = b"bcde";
    assert_eq!(a_or_b(b), Done(b"cde", b"b"));

    let c = b"cdef";
    assert_eq!(a_or_b(c), Done(b"cdef", b""));

    let d = b"bacdef";
    assert_eq!(a_or_b(d), Done(b"cdef", b"ba"));
  }

  #[derive(PartialEq,Eq,Debug)]
  struct B {
    a: u8,
    b: u8
  }

  #[test]
  fn chain2() {
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };
    named!(f<&[u8],B>,
      chain!(
        tag!("abcd")   ~
        tag!("abcd")?  ~
        aa: ret_int1   ~
        tag!("efgh")   ~
        bb: ret_int2   ~
        tag!("efgh")   ,
        ||{B{a: aa, b: bb}}
      )
    );

    let r = f(b"abcdabcdefghefghX");
    assert_eq!(r, Done(b"X", B{a: 1, b: 2}));

    let r2 = f(b"abcdefghefghX");
    assert_eq!(r2, Done(b"X", B{a: 1, b: 2}));
  }

  #[test]
  fn nested_chain() {
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };
    named!(f<&[u8],B>,
      chain!(
        chain!(
          tag!("abcd")   ~
          tag!("abcd")?  ,
          || {}
        )              ~
        aa: ret_int1   ~
        tag!("efgh")   ~
        bb: ret_int2   ~
        tag!("efgh")   ,
        ||{B{a: aa, b: bb}}
      )
    );

    let r = f(b"abcdabcdefghefghX");
    assert_eq!(r, Done(b"X", B{a: 1, b: 2}));

    let r2 = f(b"abcdefghefghX");
    assert_eq!(r2, Done(b"X", B{a: 1, b: 2}));
  }

  #[derive(PartialEq,Eq,Debug)]
  struct C {
    a: u8,
    b: Option<u8>
  }

  #[test]
  fn chain_opt() {
    named!(y, tag!("efgh"));
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_y(i:&[u8]) -> IResult<&[u8], u8> {
      y(i).map(|_| 2)
    };

    named!(f<&[u8],C>,
      chain!(
        tag!("abcd") ~
        aa: ret_int1 ~
        bb: ret_y?   ,
        ||{C{a: aa, b: bb}}
      )
    );

    let r = f(b"abcdefghX");
    assert_eq!(r, Done(b"X", C{a: 1, b: Some(2)}));

    let r2 = f(b"abcdWXYZ");
    assert_eq!(r2, Done(b"WXYZ", C{a: 1, b: None}));

    let r3 = f(b"abcdX");
    assert_eq!(r3, Incomplete(Needed::Size(4)));
  }

  #[test]
  fn alt() {
    fn work(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Done(b"", input)
    }

    #[allow(unused_variables)]
    fn dont_work(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Error(3)
    }

    fn work2(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Done(input, b"")
    }

    alt!(alt1<&[u8],&[u8]>, dont_work | dont_work);
    alt!(alt2<&[u8],&[u8]>, dont_work | work);
    alt!(alt3<&[u8],&[u8]>, dont_work | dont_work | work2 | dont_work);

    let a = b"abcd";
    assert_eq!(alt1(a), Error(1));
    assert_eq!(alt2(a), Done(b"", a));
    assert_eq!(alt3(a), Done(a, b""));

    named!(alt4<&[u8],&[u8]>, alt!(tag!("abcd") | tag!("efgh")));
    let b = b"efgh";
    assert_eq!(alt4(a), Done(b"", a));
    assert_eq!(alt4(b), Done(b"", b));
  }

  #[test]
  fn opt() {
    named!(o<&[u8],Option<&[u8]> >, opt!(tag!("abcd")));

    let a = b"abcdef";
    let b = b"bcdefg";
    assert_eq!(o(a), Done(b"ef", Some(b"abcd")));
    assert_eq!(o(b), Done(b"bcdefg", None));
  }

  #[test]
  fn peek() {
    named!(ptag<&[u8],&[u8]>, peek!(tag!("abcd")));

    let r1 = ptag(b"abcdefgh");
    assert_eq!(r1, Done(b"abcdefgh", b"abcd"));

    let r1 = ptag(b"efgh");
    assert_eq!(r1, Error(0));
  }

  #[test]
  fn many0() {
    named!(multi<&[u8],Vec<&[u8]> >, many0!(tag!("abcd")));

    let a = b"abcdef";
    let b = b"abcdabcdef";
    let c = b"azerty";

    let res1 = vec![b"abcd"];
    assert_eq!(multi(a), Done(b"ef", res1));
    let res2 = vec![b"abcd", b"abcd"];
    assert_eq!(multi(b), Done(b"ef", res2));
    assert_eq!(multi(c), Done(b"azerty", Vec::new()));
  }

  #[test]
  fn many1() {
    named!(multi<&[u8],Vec<&[u8]> >, many1!(tag!("abcd")));

    let a = b"abcdef";
    let b = b"abcdabcdef";
    let c = b"azerty";
    let res1 = vec![b"abcd"];
    assert_eq!(multi(a), Done(b"ef", res1));
    let res2 = vec![b"abcd", b"abcd"];
    assert_eq!(multi(b), Done(b"ef", res2));
    assert_eq!(multi(c), Error(0));
  }

  #[test]
  fn take_until_test() {
    take_until!(x "efgh");
    let r = x(b"abcdabcdefghijkl");
    assert_eq!(r, Done(b"ijkl", b"abcdabcd"));

    println!("Done 1\n");

    let r2 = x(b"abcdabcdefgh");
    assert_eq!(r2, Done(b"", b"abcdabcd"));

    println!("Done 2\n");
    let r3 = x(b"abcefg");
    assert_eq!(r3, Incomplete(Needed::Size(7)));
  }

  use nom::{be_u8,be_u16};
  #[test]
  fn length_value_test() {
    length_value!(tst1<&[u8], u16 > be_u8 be_u16);
    length_value!(tst2<&[u8], u16 > be_u8 be_u16 2);

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
