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
    (pub $name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: $i ) -> $o {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: $i ) -> IResult<$i, $o> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: &[u8] ) -> IResult<&[u8], &[u8]> {
            $submac!(i, $($args)*)
        }
    );
);

#[macro_export]
macro_rules! call (
  ($i:expr, $fun:expr) => ( $fun( $i ) );
);

/// declares a byte array as a suite to recognize
///
/// consumes the recognized characters
///
/// ```ignore
///  named!(x, tag!("abcd"));
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
);

/// maps a function on the result of a parser
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
    map!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $f:expr, $g:expr) => (
    map!($i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    map!($i, call!($f), $submac!($($args)*));
  );
);

/// maps a function returning a Result on the output of a parser
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
    map_res!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $f:expr, $g:expr) => (
    map_res!($i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    map_res!($i, call!($f), $submac!($($args)*));
  );
);

/// maps a function returning an Option on the output of a parser
#[macro_export]
macro_rules! map_opt(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        Error(ref e) => Error(*e),
        Incomplete(Needed::Unknown) => Incomplete(Needed::Unknown),
        Incomplete(Needed::Size(i)) => Incomplete(Needed::Size(i)),
        Done(i, o) => match $submac2!(o, $($args2)*) {
          Some(output) => Done(i, output),
          None         => Error(0)
        }
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    map_opt!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $f:expr, $g:expr) => (
    map_opt!($i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    map_opt!($i, call!($f), $submac!($($args)*));
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
/// named!(y tag!("efgh"));
///
/// fn ret_int(i:&[u8]) -> IResult<&[u8], u8> { Done(i, 1) };
/// fn ret_y(i:&[u8]) -> IResult<&[u8], u8> { y(i).map(|_| 1) }; // return 1 if the "efgh" tag is found
///
///  named!(z<&[u8], u8>,
///    chain!(
///      tag!("abcd")  ~
///      aa: ret_int   ~     // the result of that parser will be used in the closure
///      tag!("abcd")? ~     // this parser is optional
///      bb: ret_y?    ,     // the result of that parser is an option
///      ||{B{a: aa, b: bb}}
///    )
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
    chaining_parser!($i, call!($e) ~ $($rest)*);
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
    chaining_parser!($i, call!($e) ? ~ $($rest)*);
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
    chaining_parser!($i, $field: call!($e) ~ $($rest)*);
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
    chaining_parser!($i, $field : call!($e) ? ~ $($rest)*);
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
    chaining_parser!($i, call!($e), $assemble);
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
    chaining_parser!($i, call!($e) ?, $assemble);
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
    chaining_parser!($i, $field: call!($e), $assemble);
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
    chaining_parser!($i, $field : call!($e) ? , $assemble);
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
///  named!( test, alt!( tag!( "abcd" ) | tag!( "efgh" ) ) );
///  let r1 = test(b"abcdefgh"));
///  assert_eq!(r1, Done(b"efgh", b"abcd"));
///  let r2 = test(b"efghijkl"));
///  assert_eq!(r2, Done(b"ijkl", b"efgh"));
/// ```
#[macro_export]
macro_rules! alt (
  ($i:expr, $($rest:tt)*) => (
    {
      alt_parser!($i, $($rest)*)
    }
  );
);

#[macro_export]
macro_rules! alt_parser (
  ($i:expr, $e:ident | $($rest:tt)*) => (
    alt_parser!($i, call!($e) | $($rest)*);
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

  ($i:expr, $subrule:ident!( $args:tt ) => { $gen:expr } | $($rest:tt)+) => (
    match $subrule!( $i, $args ) {
      IResult::Error(_) => alt!( $i, $($rest)+ ),
      IResult::Incomplete(_) => alt!( $i, $($rest)+ ),
      IResult::Done(i,o) => IResult::Done(i, $gen( o ))
    }
  );

  ($i:expr, $e:ident => { $gen:expr } | $($rest:tt)*) => (
    alt_parser!($i, call!($e) => { $gen } | $($rest)*);
  );

  ($i:expr, $e:ident => { $gen:expr }) => (
    alt_parser!($i, call!($e) => { $gen });
  );

  ($i:expr, $subrule:ident!( $args:tt ) => { $gen:expr }) => (
    match $subrule!( $i, $args ) {
      IResult::Incomplete(x) => IResult::Incomplete(x),
      IResult::Error(e) => IResult::Error(e),
      IResult::Done(i,o) => IResult::Done(i, $gen( o )),
    }
  );

  ($i:expr, $e:ident) => (
    alt_parser!($i, call!($e));
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
///  named!( not_space, is_not!( b" \t\r\n" ) );
///
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
        IResult::Error(0)
      } else {
        IResult::Done(&$input[index..], &$input[0..index])
      }
    }
  );
);

/// returns the longest list of bytes that appear in the provided array
///
/// ```ignore
///  named!(abcd, is_a!( b"abcd" ));
///
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
        IResult::Error(0)
      } else {
        IResult::Done(&$input[index..], &$input[0..index])
      }
    }
  );
);

/// returns the longest list of bytes until the provided parser fails
///
/// ```ignore
///  named!( alpha, filter!( is_alphanumeric ) );
///
///  let r = alpha(b"abcd\nefgh"));
///  assert_eq!(r, Done(b"\nefgh", b"abcd"));
/// ```
#[macro_export]
macro_rules! filter(
  ($input:expr, $arr:expr) => (
    filter!($i, call!($f));
  );
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let mut index = 0;
      for idx in 0..$input.len() {
        index = idx;
        if !$submac!($input[idx], $($args)*) {
          break;
        }
      }
      if index == 0 {
        IResult::Error(0)
      } else {
        IResult::Done(&$input[index..], &$input[0..index])
      }
    }
  );
);

/// make the underlying parser optional
///
/// returns an Option of the returned type
///
/// ```ignore
///  named!( o, opt!( tag!( "abcd" ) ) );
///
///  let a = b"abcdef";
///  let b = b"bcdefg";
///  assert_eq!(o(a), Done(b"ef", Some(b"abcd")));
///  assert_eq!(o(b), Done(b"bcdefg", None));
/// ```
#[macro_export]
macro_rules! opt(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        IResult::Done(i,o)     => IResult::Done(i, Some(o)),
        IResult::Error(_)      => IResult::Done($i, None),
        IResult::Incomplete(i) => IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $f:expr) => (
    opt!($i, call!($f));
  );
);

#[macro_export]
macro_rules! cond(
  ($i:expr, $cond:expr, $submac:ident!( $($args:tt)* )) => (
    {
      if $cond {
        match $submac!($i, $($args)*) {
          IResult::Done(i,o)     => IResult::Done(i, Some(o)),
          IResult::Error(_)      => IResult::Done($i, None),
          IResult::Incomplete(i) => IResult::Incomplete(i)
        }
      } else {
        IResult::Done($i, None)
      }
    }
  );
  ($i:expr, $cond:expr, $f:expr) => (
    cond!($i, $cond, call($f));
  );
);


/// returns a result without consuming the input
///
/// the embedded parser may return Incomplete
///
/// ```ignore
///  named!(ptag, peek!( tag!( "abcd" ) ) );
///
///  let r = ptag(b"abcdefgh"));
///  assert_eq!(r, Done(b"abcdefgh", b"abcd"));
/// ```
#[macro_export]
macro_rules! peek(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        IResult::Done(_,o)     => IResult::Done($i, o),
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $f:expr) => (
    peek!($i, call!(f));
  );
);

/// pair(X,Y), returns (x,y)
#[macro_export]
macro_rules! pair(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i1,o1)     => {
          match $submac2!(i1, $($args2)*) {
            IResult::Error(a)      => IResult::Error(a),
            IResult::Incomplete(i) => IResult::Incomplete(i),
            IResult::Done(i2,o2)   => {
              IResult::Done(i2, (o1, o2))
            }
          }
        },
      }
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    pair!($i, $submac!($($args)*), call!($g));
  );

  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    pair!($i, call!($f), $submac!($($args)*));
  );

  ($i:expr, $f:expr, $g:expr) => (
    pair!($i, call!($f), call!($g));
  );
);

/// separated_pair(X,sep,Y) returns (x,y)
#[macro_export]
macro_rules! separated_pair(
  ($i:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)+) => (
    {
      match $submac!($i, $($args)*) {
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i1,o1)   => {
          separated_pair1!(i1, o1,  $($rest)*)
        }
      }
    }
  );

  ($i:expr, $f:expr, $($rest:tt)+) => (
    separated_pair!($i, call!($f), $($rest)*);
  );
);

macro_rules! separated_pair1(
  ($i:expr, $res1:ident, $submac2:ident!( $($args2:tt)* ), $($rest:tt)+) => (
    {
      match $submac2!($i, $($args2)*) {
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i2,_)    => {
          separated_pair2!(i2, $res1,  $($rest)*)
        }
      }
    }
  );
  ($i:expr, $res1:ident, $g:expr, $($rest:tt)+) => (
    separated_pair1!($i, $res1, call!($g), $($rest)*);
  );
);

macro_rules! separated_pair2(
  ($i:expr, $res1:ident, $submac3:ident!( $($args3:tt)* )) => (
    {
      match $submac3!($i, $($args3)*) {
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i3,o3)   => {
          IResult::Done(i3, ($res1, o3))
        }
      }
    }
  );

  ($i:expr, $res1:ident, $h:expr) => (
    separated_pair2!($i, $res1, call!($h));
  );
);

/// preceded(opening, X) returns X
#[macro_export]
macro_rules! preceded(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i1,_)    => {
          match $submac2!(i1, $($args2)*) {
            IResult::Error(a)      => IResult::Error(a),
            IResult::Incomplete(i) => IResult::Incomplete(i),
            IResult::Done(i2,o2)   => {
              IResult::Done(i2, o2)
            }
          }
        },
      }
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    preceded!($i, $submac!($($args)*), call!($g));
  );

  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    preceded!($i, call!($f), $submac!($($args)*));
  );

  ($i:expr, $f:expr, $g:expr) => (
    preceded!($i, call!($f), call!($g));
  );
);

/// terminated(X, closing) returns X
#[macro_export]
macro_rules! terminated(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i1,o1)   => {
          match $submac2!(i1, $($args2)*) {
            IResult::Error(a)      => IResult::Error(a),
            IResult::Incomplete(i) => IResult::Incomplete(i),
            IResult::Done(i2,_)    => {
              IResult::Done(i2, o1)
            }
          }
        },
      }
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    terminated!($i, $submac!($($args)*), call!($g));
  );

  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    terminated!($i, call!($f), $submac!($($args)*));
  );

  ($i:expr, $f:expr, $g:expr) => (
    terminated!($i, call!($f), call!($g));
  );
);

/// delimited(opening, X, closing) returns X
#[macro_export]
macro_rules! delimited(
  ($i:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)+) => (
    {
      match $submac!($i, $($args)*) {
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i1,_)   => {
          delimited1!(i1,  $($rest)*)
        }
      }
    }
  );

  ($i:expr, $f:expr, $($rest:tt)+) => (
    delimited!($i, call!($f), $($rest)*);
  );
);

macro_rules! delimited1(
  ($i:expr, $submac2:ident!( $($args2:tt)* ), $($rest:tt)+) => (
    {
      match $submac2!($i, $($args2)*) {
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i2,o2)    => {
          delimited2!(i2, o2,  $($rest)*)
        }
      }
    }
  );
  ($i:expr, $g:expr, $($rest:tt)+) => (
    delimited1!($i, call!($g), $($rest)*);
  );
);

macro_rules! delimited2(
  ($i:expr, $res2:ident, $submac3:ident!( $($args3:tt)* )) => (
    {
      match $submac3!($i, $($args3)*) {
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i3,_)   => {
          IResult::Done(i3, $res2)
        }
      }
    }
  );

  ($i:expr, $res2:ident, $h:expr) => (
    delimited!($i, $res2, call!($h));
  );
);

/// separated_list(sep, X) returns Vec<X>
#[macro_export]
macro_rules! separated_list(
  ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res = Vec::new();

      // get the first element
      match $submac!($i, $($args2)*) {
        IResult::Error(_)      => IResult::Done($i, Vec::new()),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i,o)     => {
          if i.len() == $i.len() {
            IResult::Error(0)
          } else {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();

            loop {
              // get the separator first
              match $sep!(&$i[begin..], $($args)*) {
                IResult::Error(_)      => break,
                IResult::Incomplete(_) => break,
                IResult::Done(i2,_)    => {
                  if i2.len() == (&$i[begin..]).len() {
                    break;
                  }
                  begin += remaining - i2.len();
                  remaining = i2.len();

                  // get the element next
                  match $submac!(&$i[begin..], $($args2)*) {
                    IResult::Error(_)      => break,
                    IResult::Incomplete(_) => break,
                    IResult::Done(i3,o3)   => {
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
            IResult::Done(&$i[begin..], res)
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
        IResult::Error(a)      => IResult::Error(a),
        IResult::Incomplete(i) => IResult::Incomplete(i),
        IResult::Done(i,o)     => {
          if i.len() == $i.len() {
            IResult::Error(0)
          } else {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();

            loop {
              // get the separator first
              match $sep!(&$i[begin..], $($args)*) {
                IResult::Error(_)      => break,
                IResult::Incomplete(_) => break,
                IResult::Done(i2,_)    => {
                  if i2.len() == (&$i[begin..]).len() {
                    break;
                  }
                  begin += remaining - i2.len();
                  remaining = i2.len();

                  // get the element next
                  match $submac!(&$i[begin..], $($args2)*) {
                    IResult::Error(_)      => break,
                    IResult::Incomplete(_) => break,
                    IResult::Done(i3,o3)   => {
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
            IResult::Done(&$i[begin..], res)
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

/// Applies the parser 0 or more times and returns the list of results in a Vec
///
/// the embedded parser may return Incomplete
///
/// ```ignore
///  named!(multi, many0!( tag!( "abcd" ) ) );
///
///  let a = b"abcdabcdef";
///  let b = b"azerty";
///
///  let res = vec![b"abcd", b"abcd"];
///  assert_eq!(multi(a), Done(b"ef", res));
///  assert_eq!(multi(b), Done(b"azerty", Vec::new()));
/// ```
/// 0 or more
#[macro_export]
macro_rules! many0(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res = Vec::new();
      loop {
        match $submac!(&$i[begin..], $($args)*) {
          IResult::Done(i,o) => {
            if i.len() == $i[begin..].len() {
              break;
            }
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
          },
          _                  => {
            break;
          }
        }
      }
      IResult::Done(&$i[begin..], res)
    }
  );
  ($i:expr, $f:expr) => (
    many0!($i, call!($f));
  );
);

/// Applies the parser 1 or more times and returns the list of results in a Vec
///
/// the embedded parser may return Incomplete
///
/// ```ignore
///  named!(multi, many1!( tag!( "abcd" ) ) );
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
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res = Vec::new();
      loop {
        match $submac!(&$i[begin..], $($args)*) {
          IResult::Done(i,o) => {
            if i.len() == $i[begin..].len() {
              break;
            }
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
          },
          _                  => {
            break;
          }
        }
      }
      if res.len() == 0 {
        IResult::Error(0)
      } else {
        IResult::Done(&$i[begin..], res)
      }
    }
  );
  ($i:expr, $f:expr) => (
    many1!($i, call!($f));
  );
);

#[macro_export]
macro_rules! count(
  ($i:expr, $submac:ident!( $($args:tt)* ), $count: expr) => (
    {
      let mut begin = 0;
      let mut remaining = $i.len();
      let mut res = Vec::new();
      let mut cnt = 0;
      let mut err = false;
      loop {
        match $submac!(&$i[begin..], $($args)*) {
          IResult::Done(i,o) => {
            res.push(o);
            begin += remaining - i.len();
            remaining = i.len();
            cnt = cnt + 1;
            if cnt == $count {
              break
            }
          },
          IResult::Error(_)  => {
            err = true;
            break;
          },
          IResult::Incomplete(_) => {
            break;
          }
        }
      }
      if err {
        IResult::Error(0)
      } else if cnt == $count {
        IResult::Done(&$i[begin..], res)
      } else {
        IResult::Incomplete(Needed::Unknown)
      }
    }
  );
  ($i:expr, $f:expr, $count: expr) => (
    many0!($i, call!($f), $count);
  );
);
/// generates a parser consuming the specified number of bytes
///
/// ```ignore
///  // Desmond parser
///  named!(take5, take!( 5 ) );
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
);

/// generates a parser consuming bytes until the specified byte sequence is found
#[macro_export]
macro_rules! take_until_and_consume(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
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
        Incomplete(Needed::Size((index + bytes.len()) as u32))
      } else {
        if parsed {
          Done(&$i[(index + bytes.len())..], &$i[0..index])
        } else {
          Error(0)
        }
      }
    }
  );
);

#[macro_export]
macro_rules! take_until(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
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
        Incomplete(Needed::Size((index + bytes.len()) as u32))
      } else {
        if parsed {
          Done(&$i[index..], &$i[0..index])
        } else {
          Error(0)
        }
      }
    }
  );
);

#[macro_export]
macro_rules! take_until_either_and_consume(
  ($i:expr, $inp:expr) => (
    {
      #[inline(always)]
      fn as_bytes<T: $crate::util::AsBytes>(b: &T) -> &[u8] {
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
        Incomplete(Needed::Size((index + 1) as u32))
      } else {
        if parsed {
          Done(&$i[(index+1)..], &$i[0..index])
        } else {
          Error(0)
        }
      }
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
        Incomplete(Needed::Size((index + 1) as u32))
      } else {
        if parsed {
          Done(&$i[index..], &$i[0..index])
        } else {
          Error(0)
        }
      }
    }
  );
);

/// returns
#[macro_export]
macro_rules! length_value(
  ($i:expr, $f:expr, $g:expr) => (
    {
      match $f($i) {
        Error(a)      => Error(a),
        Incomplete(i) => Incomplete(i),
        Done(i1,nb)   => {
          let length_token     = $i.len() - i1.len();
          let mut begin        = 0;
          let mut remaining    = i1.len();
          let mut res          = Vec::new();
          let mut err          = false;
          let mut inc          = Needed::Unknown;

          loop {
            if res.len() == nb as usize {
              break;
            }
            match $g(&i1[begin..]) {
              Done(i2,o2) => {
              res.push(o2);
                let parsed  = remaining - i2.len();
                begin      += parsed;
                remaining   = i2.len();
              },
              Error(_)      => {
                err = true;
              },
              Incomplete(a) => {
                inc = a;
                break;
              }
            }
          }
          if err {
            Error(0)
          } else if res.len() < nb as usize {
            match inc {
              Needed::Unknown      => Incomplete(Needed::Unknown),
              Needed::Size(length) => Incomplete(Needed::Size(length_token as u32 + nb as u32 * length))
            }
          } else {
            Done(&i1[begin..], res)
          }

        }
      }
    }
  );
  ($i:expr, $f:expr, $g:expr, $length:expr) => (
    {
      match $f($i) {
        Error(a)      => Error(a),
        Incomplete(i) => Incomplete(i),
        Done(i1,nb)   => {
          let length_token     = $i.len() - i1.len();
          let mut begin        = 0;
          let mut remaining    = i1.len();
          let mut res          = Vec::new();
          let mut err          = false;
          let mut inc          = Needed::Unknown;

          loop {
            if res.len() == nb as usize {
              break;
            }
            match $g(&i1[begin..]) {
              Done(i2,o2) => {
              res.push(o2);
                let parsed  = remaining - i2.len();
                begin      += parsed;
                remaining   = i2.len();
              },
              Error(_)      => {
                err = true;
              },
              Incomplete(a) => {
                inc = a;
                break;
              }
            }
          }
          if err {
            Error(0)
          } else if res.len() < nb as usize {
            match inc {
              Needed::Unknown      => Incomplete(Needed::Unknown),
              Needed::Size(_) => Incomplete(Needed::Size(length_token as u32 + nb as u32 * $length))
            }
          } else {
            Done(&i1[begin..], res)
          }

        }
      }
    }
  );
);

#[cfg(test)]
mod tests {
  use map::*;
  use internal::Needed;
  use internal::IResult;
  use internal::IResult::*;

  mod pub_named_mod {
    use internal::Needed;
    use internal::IResult;
    use internal::IResult::*;

    named!(pub tst, tag!("abcd"));
  }

  #[test]
  fn pub_named_test() {
    let a = &b"abcd"[..];
    let res = pub_named_mod::tst(a);
    assert_eq!(res, Done(&b""[..], a));
  }

  #[test]
  fn is_a() {
    named!(a_or_b, is_a!(&b"ab"[..]));

    let a = &b"abcd"[..];
    assert_eq!(a_or_b(a), Done(&b"cd"[..], &b"ab"[..]));

    let b = &b"bcde"[..];
    assert_eq!(a_or_b(b), Done(&b"cde"[..], &b"b"[..]));

    let c = &b"cdef"[..];
    assert_eq!(a_or_b(c), Error(0));

    let d = &b"bacdef"[..];
    assert_eq!(a_or_b(d), Done(&b"cdef"[..], &b"ba"[..]));
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

    let r = f(&b"abcdabcdefghefghX"[..]);
    assert_eq!(r, Done(&b"X"[..], B{a: 1, b: 2}));

    let r2 = f(&b"abcdefghefghX"[..]);
    assert_eq!(r2, Done(&b"X"[..], B{a: 1, b: 2}));
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

    let r = f(&b"abcdabcdefghefghX"[..]);
    assert_eq!(r, Done(&b"X"[..], B{a: 1, b: 2}));

    let r2 = f(&b"abcdefghefghX"[..]);
    assert_eq!(r2, Done(&b"X"[..], B{a: 1, b: 2}));
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

    let r = f(&b"abcdefghX"[..]);
    assert_eq!(r, Done(&b"X"[..], C{a: 1, b: Some(2)}));

    let r2 = f(&b"abcdWXYZ"[..]);
    assert_eq!(r2, Done(&b"WXYZ"[..], C{a: 1, b: None}));

    let r3 = f(&b"abcdX"[..]);
    assert_eq!(r3, Incomplete(Needed::Size(4)));
  }

  #[test]
  fn alt() {
    fn work(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Done(&b""[..], input)
    }

    #[allow(unused_variables)]
    fn dont_work(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Error(3)
    }

    fn work2(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Done(input, &b""[..])
    }

    named!(alt1, alt!(dont_work | dont_work));
    named!(alt2, alt!(dont_work | work));
    named!(alt3, alt!(dont_work | dont_work | work2 | dont_work));

    let a = &b"abcd"[..];
    assert_eq!(alt1(a), Error(1));
    assert_eq!(alt2(a), Done(&b""[..], a));
    assert_eq!(alt3(a), Done(a, &b""[..]));

    named!(alt4, alt!(tag!("abcd") | tag!("efgh")));
    let b = &b"efgh"[..];
    assert_eq!(alt4(a), Done(&b""[..], a));
    assert_eq!(alt4(b), Done(&b""[..], b));
  }

  #[test]
  fn opt() {
    named!(o<&[u8],Option<&[u8]> >, opt!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    assert_eq!(o(a), Done(&b"ef"[..], Some(&b"abcd"[..])));
    assert_eq!(o(b), Done(&b"bcdefg"[..], None));
  }

  #[test]
  fn peek() {
    named!(ptag<&[u8],&[u8]>, peek!(tag!("abcd")));

    let r1 = ptag(&b"abcdefgh"[..]);
    assert_eq!(r1, Done(&b"abcdefgh"[..], &b"abcd"[..]));

    let r1 = ptag(&b"efgh"[..]);
    assert_eq!(r1, Error(0));
  }

  #[test]
  fn pair() {
    named!(p<&[u8],(&[u8], &[u8])>, pair!(tag!("abcd"), tag!("efgh")));

    let r1 = p(&b"abcdefghijkl"[..]);
    assert_eq!(r1, Done(&b"ijkl"[..], (&b"abcd"[..], &b"efgh"[..])));
  }

  #[test]
  fn separated_pair() {
    named!(p<&[u8],(&[u8], &[u8])>, separated_pair!(tag!("abcd"), tag!(","), tag!("efgh")));

    let r1 = p(&b"abcd,efghijkl"[..]);
    assert_eq!(r1, Done(&b"ijkl"[..], (&b"abcd"[..], &b"efgh"[..])));
  }

  #[test]
  fn preceded() {
    named!(p<&[u8], &[u8]>, preceded!(tag!("abcd"), tag!("efgh")));

    let r1 = p(&b"abcdefghijkl"[..]);
    assert_eq!(r1, Done(&b"ijkl"[..], &b"efgh"[..]));
  }

  #[test]
  fn terminated() {
    named!(p<&[u8], &[u8]>, terminated!(tag!("abcd"), tag!("efgh")));

    let r1 = p(&b"abcdefghijkl"[..]);
    assert_eq!(r1, Done(&b"ijkl"[..], &b"abcd"[..]));
  }

  #[test]
  fn delimited() {
    named!(p<&[u8], &[u8]>, delimited!(tag!("abcd"), tag!("efgh"), tag!("ij")));

    let r1 = p(&b"abcdefghijkl"[..]);
    assert_eq!(r1, Done(&b"kl"[..], &b"efgh"[..]));
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
    assert_eq!(multi(c), Error(0));
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
    assert_eq!(multi(c), Error(0));
  }

  #[test]
  fn infinite_many() {
    fn tst(input: &[u8]) -> IResult<&[u8], &[u8]> {
      Error(0)
    }

    // should not go into an infinite loop
    named!(multi0<&[u8],Vec<&[u8]> >, many0!(tst));
    let a = &b"abcdef"[..];
    assert_eq!(multi0(a), Done(a, Vec::new()));

    named!(multi1<&[u8],Vec<&[u8]> >, many1!(tst));
    let a = &b"abcdef"[..];
    assert_eq!(multi1(a), Error(0));
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
