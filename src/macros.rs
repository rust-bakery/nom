//! Macro combinators
//!
//! Macros are used to make combination easier,
//! since they often do not depend on the type
//! of the data they manipulate or return.
//!
//! There is a trick to make them easier to assemble,
//! combinators are defined like this:
//!
//! ```ignore
//! macro_rules! tag (
//!   ($i:expr, $inp: expr) => (
//!     {
//!       ...
//!     }
//!   );
//! );
//! ```
//!
//! But when used in other combinators, are Used
//! like this:
//!
//! ```ignore
//! named!(my_function, tag!("abcd"));
//! ```
//!
//! Internally, other combinators will rewrite
//! that call to pass the input as first argument:
//!
//! ```ignore
//! macro_rules! named (
//!   ($name:ident, $submac:ident!( $($args:tt)* )) => (
//!     fn $name<'a>( i: &'a [u8] ) -> $crate::IResult<'a,&[u8], &[u8]> {
//!       $submac!(i, $($args)*)
//!     }
//!   );
//! );
//! ```
//!
//! If you want to call a combinator directly, you can
//! do it like this:
//!
//! ```ignore
//! let res = { tag!(input, "abcd"); }
//! ```
//!
//! Combinators must have a specific variant for
//! non-macro arguments. Example: passing a function
//! to filter! instead of another combinator.
//!
//! ```ignore
//! macro_rules! filter(
//!   ($input:expr, $submac:ident!( $($args:tt)* )) => (
//!     {
//!       ...
//!     }
//!   );
//!
//!   // wrap the function in a macro to pass it to the main implementation
//!   ($input:expr, $f:expr) => (
//!     filter!($input, call!($f));
//!   );
//! );
//!

/// Wraps a parser in a closure
#[macro_export]
macro_rules! closure (
    ($ty:ty, $submac:ident!( $($args:tt)* )) => (
        |i: $ty| { $submac!(i, $($args)*) }
    );
    ($submac:ident!( $($args:tt)* )) => (
        |i| { $submac!(i, $($args)*) }
    );
);

/// Makes a function from a parser combination
///
/// The type can be set up if the compiler needs
/// more information
///
/// ```ignore
/// named!(my_function( &[u8] ) -> &[u8], tag!("abcd"));
/// // first type parameter is input, second is output
/// named!(my_function<&[u8], &[u8]>,     tag!("abcd"));
/// // will have &[u8] as input type, &[u8] as output type
/// named!(my_function,                   tag!("abcd"));
/// // will use &[u8] as input type (use this if the compiler
/// // complains about lifetime issues
/// named!(my_function<&[u8]>,            tag!("abcd"));
/// //prefix them with 'pub' to make the functions public
/// named!(pub my_function,               tag!("abcd"));
/// ```
#[macro_export]
macro_rules! named (
    ($name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        fn $name<'a>( i: $i ) -> $crate::IResult<'a,$i,$o> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: $i ) -> $crate::IResult<$i, $o> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
        fn $name<'a>( i: &'a[u8] ) -> $crate::IResult<'a, &'a [u8], $o> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$life:item,$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        fn $name<$life>( i: $i ) -> $crate::IResult<$life,$i, $o> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident, $submac:ident!( $($args:tt)* )) => (
        fn $name<'a>( i: &'a [u8] ) -> $crate::IResult<'a,&[u8], &[u8]> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        pub fn $name<'a>( i: $i ) -> $crate::IResult<'a,$i,$o> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: $i ) -> $crate::IResult<$i, $o> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
        pub fn $name<'a>( i: &'a[u8] ) -> $crate::IResult<'a, &'a [u8], $o> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident, $submac:ident!( $($args:tt)* )) => (
        pub fn $name<'a>( i: &'a [u8] ) -> $crate::IResult<'a,&[u8], &[u8]> {
            $submac!(i, $($args)*)
        }
    );
);

/// Used to wrap common expressions and function as macros
#[macro_export]
macro_rules! call (
  ($i:expr, $fun:expr) => ( $fun( $i ) );
);

#[macro_export]
macro_rules! apply (
  //($i:expr, $fun:ident( $($args:tt),*) ) => ($fun($i, $($args),*) );
  ($i:expr, $fun:expr, $arg:expr ) => ( $fun( $i, $arg ) );
  ($i:expr, $fun:expr, $arg:expr, $arg2:expr ) => ( $fun( $i, $arg, $arg2 ) );
  ($i:expr, $fun:expr, $arg:expr, $arg2:expr, $arg3:expr ) => ( $fun( $i, $arg, $arg2, $arg3 ) );
  ($i:expr, $fun:expr, $arg:expr, $arg2:expr, $arg3:expr, $arg4:expr ) => ( $fun( $i, $arg, $arg2, $arg3, $arg4 ) );
  ($i:expr, $fun:expr, $arg:expr, $arg2:expr, $arg3:expr, $arg4:expr, $arg5:expr ) => ( $fun( $i, $arg, $arg2, $arg3, $arg4, $arg5 ) );
  ($i:expr, $fun:expr, $arg:expr, $arg2:expr, $arg3:expr, $arg4:expr, $arg5:expr, $arg6:expr ) => ( $fun( $i, $arg, $arg2, $arg3, $arg4, $arg5, $arg6 ) );
);

/// Prevents backtracking if the child parser fails
///
/// This parser will do an early return instead of sending
/// its result to the parent parser.
///
/// If another `error!` combinator is present in the parent
/// chain, the error will be wrapped and another early
/// return will be made.
///
/// This makes it easy to build report on which parser failed,
/// where it failed in the input, and the chain of parsers
/// that led it there.
///
/// Additionally, the error chain contains number identifiers
/// that can be matched to provide useful error messages.
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use std::collections;
/// # use nom::IResult::Error;
/// # use nom::Err::{Position,NodePosition};
/// # fn main() {
///     named!(err_test, alt!(
///       tag!("abcd") |
///       preceded!(tag!("efgh"), error!(42,
///           chain!(
///                  tag!("ijkl")              ~
///             res: error!(128, tag!("mnop")) ,
///             || { res }
///           )
///         )
///       )
///     ));
///     let a = &b"efghblah"[..];
///     let b = &b"efghijklblah"[..];
///     let c = &b"efghijklmnop"[..];
///
///     let blah = &b"blah"[..];
///
///     let res_a = err_test(a);
///     let res_b = err_test(b);
///     let res_c = err_test(c);
///     assert_eq!(res_a, Error(NodePosition(42, blah, Box::new(Position(0, blah)))));
///     assert_eq!(res_b, Error(NodePosition(42, &b"ijklblah"[..], Box::new(NodePosition(128, blah, Box::new(Position(0, blah)))))));
/// # }
/// ```
///
#[macro_export]
macro_rules! error (
  ($i:expr, $code:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let cl = || {
        $submac!($i, $($args)*)
      };

      match cl() {
      //match cl($i) {
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
        $crate::IResult::Error(e)      => {
          return $crate::IResult::Error($crate::Err::NodePosition($code, $i, Box::new(e)))
        }
      }
    }
  );
  ($i:expr, $code:expr, $f:expr) => (
    error!($i, $code, call!($f));
  );
);

/// `flat_map!(R -> IResult<R,S>, S -> IResult<S,T>) => R -> IResult<R, T>`
///
/// combines a parser R -> IResult<R,S> and
/// a parser S -> IResult<S,T> to return another
/// parser R -> IResult<R,T>
#[macro_export]
macro_rules! flat_map(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done(i, o)                          => match $submac2!(o, $($args2)*) {
          $crate::IResult::Error(e)                                 => $crate::IResult::Error(e),
          $crate::IResult::Incomplete($crate::Needed::Unknown)      => $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::IResult::Incomplete($crate::Needed::Size(ref i2)) => $crate::IResult::Incomplete($crate::Needed::Size(*i2)),
          $crate::IResult::Done(_, o2)                              => $crate::IResult::Done(i, o2)
        }
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    flat_map!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $f:expr, $g:expr) => (
    flat_map!($i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    flat_map!($i, call!($f), $submac!($($args)*));
  );
);

/// `map!(I -> IResult<I,O>, O -> P) => I -> IResult<I, P>`
/// maps a function on the result of a parser
#[macro_export]
macro_rules! map(
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    map_impl!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    map_impl!($i, $submac!($($args)*), $submac2!($($args2)*),);
  );
  ($i:expr, $f:expr, $g:expr) => (
    map_impl!($i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    map_impl!($i, call!($f), $submac!($($args)*));
  );
);

/// Internal parser, do not use directly
#[macro_export]
macro_rules! map_impl(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done(i, o)                          => $crate::IResult::Done(i, $submac2!(o, $($args2)*))
      }
    }
  );
);

/// `map_res!(I -> IResult<I,O>, O -> Result<P>) => I -> IResult<I, P>`
/// maps a function returning a Result on the output of a parser
#[macro_export]
macro_rules! map_res (
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    map_res_impl!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    map_res_impl!($i, $submac!($($args)*), $submac2!($($args2)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    map_res_impl!($i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    map_res_impl!($i, call!($f), $submac!($($args)*));
  );
);

/// Internal parser, do not use directly
#[macro_export]
macro_rules! map_res_impl (
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done(i, o)                          => match $submac2!(o, $($args2)*) {
          Ok(output) => $crate::IResult::Done(i, output),
          Err(_)     => $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::MapRes as u32, $i))
        }
      }
    }
  );
);


/// `map_res!(I -> IResult<I,O>, O -> Option<P>) => I -> IResult<I, P>`
/// maps a function returning an Option on the output of a parser
#[macro_export]
macro_rules! map_opt (
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    map_opt_impl!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    map_opt_impl!($i, $submac!($($args)*), $submac2!($($args2)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    map_opt_impl!($i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    map_opt_impl!($i, call!($f), $submac!($($args)*));
  );
);

/// Internal parser, do not use directly
#[macro_export]
macro_rules! map_opt_impl (
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done(i, o)                          => match $submac2!(o, $($args2)*) {
          Some(output) => $crate::IResult::Done(i, output),
          None         => $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::MapOpt as u32, $i))
        }
      }
    }
  );
);

/// `expr_res!(Result<E,O>) => I -> IResult<I, O>`
/// evaluate an expression that returns a Result<T,E> and returns a IResult::Done(I,T) if Ok
///
/// See expr_opt for an example
#[macro_export]
macro_rules! expr_res (
  ($i:expr, $e:expr) => (
    {
      match $e {
        Ok(output) => $crate::IResult::Done($i, output),
        Err(_)     => $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::ExprRes as u32, $i))
      }
    }
  );
);

/// `expr_opt!(Option<O>) => I -> IResult<I, O>`
/// evaluate an expression that returns a Option<T> and returns a IResult::Done(I,T) if Ok
///
/// Useful when doing computations in a chain
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Error};
/// # use nom::Err::Position;
/// # use nom::{be_u8,ErrorCode};
///
///  fn take_add(input:&[u8], size: u8) -> IResult<&[u8],&[u8]> {
///    chain!(input,
///      sz:     be_u8                             ~
///      length: expr_opt!(size.checked_add(sz))   ~ // checking for integer overflow (returns an Option)
///      data:   take!(length)                     ,
///      ||{ data }
///    )
///  }
/// # fn main() {
/// let arr1 = [1, 2, 3, 4, 5];
/// let r1 = take_add(&arr1[..], 1);
/// assert_eq!(r1, Done(&[4,5][..], &[2,3][..]));
///
/// let arr2 = [0xFE, 2, 3, 4, 5];
/// // size is overflowing
/// let r1 = take_add(&arr2[..], 42);
/// assert_eq!(r1, Error(Position(ErrorCode::ExprOpt as u32,&[2,3,4,5][..])));
/// # }
/// ```
#[macro_export]
macro_rules! expr_opt (
  ($i:expr, $e:expr) => (
    {
      match $e {
        Some(output) => $crate::IResult::Done($i, output),
        None         => $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::ExprOpt as u32, $i))
      }
    }
  );
);

/// `chain!(I->IResult<I,A> ~ I->IResult<I,B> ~ ... I->IResult<I,X> , || { return O } ) => I -> IResult<I, O>`
/// chains parsers and assemble the results through a closure
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Error};
/// # use nom::Err::Position;
/// #[derive(PartialEq,Eq,Debug)]
/// struct B {
///   a: u8,
///   b: Option<u8>
/// }
///
/// named!(y, tag!("efgh"));
///
/// fn ret_int(i:&[u8]) -> IResult<&[u8], u8> { Done(i, 1) }
/// named!(ret_y<&[u8], u8>, map!(y, |_| 1)); // return 1 if the "efgh" tag is found
///
///  named!(z<&[u8], B>,
///    chain!(
///      tag!("abcd")  ~
///      aa: ret_int   ~     // the result of that parser will be used in the closure
///      tag!("abcd")? ~     // this parser is optional
///      bb: ret_y?    ,     // the result of that parser is an option
///      ||{B{a: aa, b: bb}}
///    )
///  );
///
/// # fn main() {
/// // the first "abcd" tag is not present, we have an error
/// let r1 = z(&b"efgh"[..]);
/// assert_eq!(r1, Error(Position(0,&b"efgh"[..])));
///
/// // everything is present, everything is parsed
/// let r2 = z(&b"abcdabcdefgh"[..]);
/// assert_eq!(r2, Done(&b""[..], B{a: 1, b: Some(1)}));
///
/// // the second "abcd" tag is optional
/// let r3 = z(&b"abcdefgh"[..]);
/// assert_eq!(r3, Done(&b""[..], B{a: 1, b: Some(1)}));
///
/// // the result of ret_y is optional, as seen in the B structure
/// let r4 = z(&b"abcdabcdwxyz"[..]);
/// assert_eq!(r4, Done(&b"wxyz"[..], B{a: 1, b: None}));
/// # }
/// ```
#[macro_export]
macro_rules! chain (
  ($i:expr, $($rest:tt)*) => (
    chaining_parser!($i, $($rest)*)
  );
);

/// Internal parser, do not use directly
#[macro_export]
macro_rules! chaining_parser (
  ($i:expr, $e:ident ~ $($rest:tt)*) => (
    chaining_parser!($i, call!($e) ~ $($rest)*);
  );
  ($i:expr, $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(i,_)     => {
        chaining_parser!(i, $($rest)*)
      }
    }
  );

  ($i:expr, $e:ident ? ~ $($rest:tt)*) => (
    chaining_parser!($i, call!($e) ? ~ $($rest)*);
  );

  ($i:expr, $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => ({
    let input = if let $crate::IResult::Done(i,_) = $submac!($i, $($args)*) {
      i
    } else {
      $i
    };
    chaining_parser!(input, $($rest)*)
  });

  ($i:expr, $field:ident : $e:ident ~ $($rest:tt)*) => (
    chaining_parser!($i, $field: call!($e) ~ $($rest)*);
  );

  ($i:expr, $field:ident : $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    match  $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(i,o)     => {
        let $field = o;
        chaining_parser!(i, $($rest)*)
      }
    }
  );

  ($i:expr, mut $field:ident : $e:ident ~ $($rest:tt)*) => (
    chaining_parser!($i, mut $field: call!($e) ~ $($rest)*);
  );

  ($i:expr, mut $field:ident : $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    match  $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(i,o)     => {
        let mut $field = o;
        chaining_parser!(i, $($rest)*)
      }
    }
  );

  ($i:expr, $field:ident : $e:ident ? ~ $($rest:tt)*) => (
    chaining_parser!($i, $field : call!($e) ? ~ $($rest)*);
  );

  ($i:expr, $field:ident : $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => ({
    let ($field, input) = if let $crate::IResult::Done(i,o) = $submac!($i, $($args)*) {
      (Some(o), i)
    } else {
      (None, $i)
    };
    chaining_parser!(input, $($rest)*)
  });

  ($i:expr, mut $field:ident : $e:ident ? ~ $($rest:tt)*) => (
    chaining_parser!($i, mut $field : call!($e) ? ~ $($rest)*);
  );

  ($i:expr, mut $field:ident : $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => ({
    let (mut $field, input) = if let $crate::IResult::Done(i,o) = $submac!($i, $($args)*) {
      (Some(o), i)
    } else {
      (None, $i)
    };
    chaining_parser!(input, $($rest)*)
  });

  // ending the chain
  ($i:expr, $e:ident, $assemble:expr) => (
    chaining_parser!($i, call!($e), $assemble);
  );

  ($i:expr, $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(i,_)     => {
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $e:ident ?, $assemble:expr) => (
    chaining_parser!($i, call!($e) ?, $assemble);
  );

  ($i:expr, $submac:ident!( $($args:tt)* ) ?, $assemble:expr) => ({
    let input = if let $crate::IResult::Done(i,_) = $submac!($i, $($args)*) {
      i
    } else {
      $i
    };
    $crate::IResult::Done(input, $assemble())
  });

  ($i:expr, $field:ident : $e:ident, $assemble:expr) => (
    chaining_parser!($i, $field: call!($e), $assemble);
  );

  ($i:expr, $field:ident : $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(i,o)     => {
        let $field = o;
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, mut $field:ident : $e:ident, $assemble:expr) => (
    chaining_parser!($i, mut $field: call!($e), $assemble);
  );

  ($i:expr, mut $field:ident : $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(i,o)     => {
        let mut $field = o;
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $field:ident : $e:ident ? , $assemble:expr) => (
    chaining_parser!($i, $field : call!($e) ? , $assemble);
  );

  ($i:expr, $field:ident : $submac:ident!( $($args:tt)* ) ? , $assemble:expr) => (
    match $submac!($i, $($args)*)  {
      $crate::IResult::Incomplete(_) | $crate::IResult::Error(_) => {
        let $field = None;
        $crate::IResult::Done($i, $assemble())
      },
      $crate::IResult::Done(i,o)     => {
        let $field = Some(o);
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, mut $field:ident : $e:ident ? , $assemble:expr) => (
    chaining_parser!($i, $field : call!($e) ? , $assemble);
  );

  ($i:expr, mut $field:ident : $submac:ident!( $($args:tt)* ) ? , $assemble:expr) => (
    match $submac!($i, $($args)*)  {
      $crate::IResult::Incomplete(_) | $crate::IResult::Error(_) => {
        let mut $field = None;
        $crate::IResult::Done($i, $assemble())
      },
      $crate::IResult::Done(i,o)     => {
        let mut $field = Some(o);
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $assemble:expr) => (
    $crate::IResult::Done($i, $assemble())
  )
);

/// `alt!(I -> IResult<I,O> | I -> IResult<I,O> | ... | I -> IResult<I,O> ) => I -> IResult<I, O>`
/// try a list of parsers, return the result of the first successful one
///
/// If one of the parser returns Incomplete, alt will return Incomplete, to retry
/// once you get more input. Note that it is better for performance to know the
/// minimum size of data you need before you get into alt.
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!( test, alt!( tag!( "abcd" ) | tag!( "efgh" ) ) );
///  let r1 = test(b"abcdefgh");
///  assert_eq!(r1, Done(&b"efgh"[..], &b"abcd"[..]));
///  let r2 = test(&b"efghijkl"[..]);
///  assert_eq!(r2, Done(&b"ijkl"[..], &b"efgh"[..]));
///  # }
/// ```
///
/// There is another syntax for alt allowing a block to manipulate the result:
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///     #[derive(Debug,PartialEq,Eq)]
///     enum Tagged {
///       Abcd,
///       Efgh,
///       Took(usize)
///     }
///     named!(test<Tagged>, alt!(
///         tag!("abcd") => { |_|          Tagged::Abcd }
///       | tag!("efgh") => { |_|          Tagged::Efgh }
///       | take!(5)     => { |res: &[u8]| Tagged::Took(res.len()) } // the closure takes the result as argument if the parser is successful
///     ));
///     let r1 = test(b"abcdefgh");
///     assert_eq!(r1, Done(&b"efgh"[..], Tagged::Abcd));
///     let r2 = test(&b"efghijkl"[..]);
///     assert_eq!(r2, Done(&b"ijkl"[..], Tagged::Efgh));
///     let r3 = test(&b"mnopqrst"[..]);
///     assert_eq!(r3, Done(&b"rst"[..],  Tagged::Took(5)));
/// # }
/// ```
#[macro_export]
macro_rules! alt (
  ($i:expr, $($rest:tt)*) => (
    {
      alt_parser!($i, $($rest)*)
    }
  );
);

/// Internal parser, do not use directly
#[macro_export]
macro_rules! alt_parser (
  ($i:expr, $e:ident | $($rest:tt)*) => (
    alt_parser!($i, call!($e) | $($rest)*);
  );

  ($i:expr, $subrule:ident!( $($args:tt)*) | $($rest:tt)*) => (
    {
      match $subrule!( $i, $($args)* ) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,o),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(_)      => {
          alt_parser!($i, $($rest)*)
        }
      }
    }
  );

  ($i:expr, $subrule:ident!( $($args:tt)* ) => { $gen:expr } | $($rest:tt)+) => (
    {
      match $subrule!( $i, $($args)* ) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,$gen(o)),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(_)      => {
          alt_parser!($i, $($rest)*)
        }
      }
    }
  );

  ($i:expr, $e:ident => { $gen:expr } | $($rest:tt)*) => (
    alt_parser!($i, call!($e) => { $gen } | $($rest)*);
  );

  ($i:expr, $e:ident => { $gen:expr }) => (
    alt_parser!($i, call!($e) => { $gen });
  );

  ($i:expr, $subrule:ident!( $($args:tt)* ) => { $gen:expr }) => (
    {
      match $subrule!( $i, $($args)* ) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,$gen(o)),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(_)      => {
          alt_parser!($i)
        }
      }
    }
  );

  ($i:expr, $e:ident) => (
    alt_parser!($i, call!($e));
  );

  ($i:expr, $subrule:ident!( $($args:tt)*)) => (
    {
      match $subrule!( $i, $($args)* ) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,o),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(_)      => {
          alt_parser!($i)
        }
      }
    }
  );

  ($i:expr) => (
    $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::Alt as u32,$i))
  );
);

/// `switch!(I -> IResult<I,P>, P => I -> IResult<I,O> | ... | P => I -> IResult<I,O> ) => I -> IResult<I, O>`
/// choose the next parser depending on the result of the first one, if successful
///
#[macro_export]
macro_rules! switch (
  ($i:expr, $submac:ident!( $($args:tt)*), $($p:pat => $subrule:ident!( $($args2:tt)* ))|*) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i, o)    => {
          match o {
            $($p => $subrule!(i, $($args2)*)),*,
            _    => $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::Switch as u32,i))
          }
        }
      }
    }
  );
  ($i:expr, $e:ident, $($rest:tt)*) => (
    {
      switch!($i, call!(e), $($rest)*)
    }
  );
);

/// `opt!(I -> IResult<I,O>) => I -> IResult<I, Option<O>>`
/// make the underlying parser optional
///
/// returns an Option of the returned type. This parser never fails
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!( o<&[u8], Option<&[u8]> >, opt!( tag!( "abcd" ) ) );
///
///  let a = b"abcdef";
///  let b = b"bcdefg";
///  assert_eq!(o(&a[..]), Done(&b"ef"[..], Some(&b"abcd"[..])));
///  assert_eq!(o(&b[..]), Done(&b"bcdefg"[..], None));
///  # }
/// ```
#[macro_export]
macro_rules! opt(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, Some(o)),
        $crate::IResult::Error(_)      => $crate::IResult::Done($i, None),
        $crate::IResult::Incomplete(_) => $crate::IResult::Done($i, None)
      }
    }
  );
  ($i:expr, $f:expr) => (
    opt!($i, call!($f));
  );
);

/// `opt_res!(I -> IResult<I,O>) => I -> IResult<I, Result<nom::Err,O>>`
/// make the underlying parser optional
///
/// returns a Result, with Err containing the parsing error
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # use nom::Err::Position;
/// # fn main() {
///  named!( o<&[u8], Result<&[u8], nom::Err> >, opt_res!( tag!( "abcd" ) ) );
///
///  let a = b"abcdef";
///  let b = b"bcdefg";
///  assert_eq!(o(&a[..]), Done(&b"ef"[..], Ok(&b"abcd"[..])));
///  assert_eq!(o(b), Done(&b"bcdefg"[..], Err(Position(0, b))));
///  # }
/// ```
#[macro_export]
macro_rules! opt_res (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,  Ok(o)),
        $crate::IResult::Error(e)      => $crate::IResult::Done($i, Err(e)),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $f:expr) => (
    opt_res!($i, call!($f));
  );
);

/// `cond!(bool, I -> IResult<I,O>) => I -> IResult<I, Option<O>>`
/// Conditional combinator
///
/// Wraps another parser and calls it if the
/// condition is met. This combinator returns
/// an Option of the return type of the child
/// parser.
///
/// This is especially useful if a parser depends
/// on the value return by a preceding parser in
/// a `chain!`.
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  let b = true;
///  let f = closure!(&'static[u8],
///    cond!( b, tag!("abcd") )
///  );
///
///  let a = b"abcdef";
///  assert_eq!(f(&a[..]), Done(&b"ef"[..], Some(&b"abcd"[..])));
///
///  let b2 = false;
///  let f2 = closure!(&'static[u8],
///    cond!( b2, tag!("abcd") )
///  );
///  assert_eq!(f2(&a[..]), Done(&b"abcdef"[..], None));
///  # }
/// ```
///
#[macro_export]
macro_rules! cond(
  ($i:expr, $cond:expr, $submac:ident!( $($args:tt)* )) => (
    {
      if $cond {
        match $submac!($i, $($args)*) {
          $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, Some(o)),
          $crate::IResult::Error(_)      => $crate::IResult::Done($i, None),
          $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
        }
      } else {
        $crate::IResult::Done($i, None)
      }
    }
  );
  ($i:expr, $cond:expr, $f:expr) => (
    cond!($i, $cond, call!($f));
  );
);

/// `cond_reduce!(bool, I -> IResult<I,O>) => I -> IResult<I, O>`
/// Conditional combinator with error
///
/// Wraps another parser and calls it if the
/// condition is met. This combinator returns
/// an error if the condition is false
///
/// This is especially useful if a parser depends
/// on the value return by a preceding parser in
/// a `chain!`.
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done,Error};
/// # use nom::{Err,ErrorCode};
/// # fn main() {
///  let b = true;
///  let f = closure!(&'static[u8],
///    cond_reduce!( b, tag!("abcd") )
///  );
///
///  let a = b"abcdef";
///  assert_eq!(f(&a[..]), Done(&b"ef"[..], &b"abcd"[..]));
///
///  let b2 = false;
///  let f2 = closure!(&'static[u8],
///    cond_reduce!( b2, tag!("abcd") )
///  );
///  assert_eq!(f2(&a[..]), Error(Err::Position(ErrorCode::CondReduce as u32, &a[..])));
///  # }
/// ```
///
#[macro_export]
macro_rules! cond_reduce(
  ($i:expr, $cond:expr, $submac:ident!( $($args:tt)* )) => (
    {
      if $cond {
        match $submac!($i, $($args)*) {
          $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, o),
          $crate::IResult::Error(e)      => $crate::IResult::Error(e),
          $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
        }
      } else {
        $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::CondReduce as u32, $i))
      }
    }
  );
  ($i:expr, $cond:expr, $f:expr) => (
    cond_reduce!($i, $cond, call!($f));
  );
);

/// `peek!(I -> IResult<I,O>) => I -> IResult<I, O>`
/// returns a result without consuming the input
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(ptag, peek!( tag!( "abcd" ) ) );
///
///  let r = ptag(&b"abcdefgh"[..]);
///  assert_eq!(r, Done(&b"abcdefgh"[..], &b"abcd"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! peek(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Done(_,o)     => $crate::IResult::Done($i, o),
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $f:expr) => (
    peek!($i, call!(f));
  );
);

/// `tap!(name: I -> IResult<I,O> => { block }) => I -> IResult<I, O>`
/// allows access to the parser's result without affecting it
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # use std::str;
/// # fn main() {
///  named!(ptag, tap!(res: tag!( "abcd" ) => { println!("recognized {}", str::from_utf8(res).unwrap()) } ) );
///
///  let r = ptag(&b"abcdefgh"[..]);
///  assert_eq!(r, Done(&b"efgh"[..], &b"abcd"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! tap (
  ($i:expr, $name:ident : $submac:ident!( $($args:tt)* ) => $e:expr) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Done(i,o)     => {
          let $name = o;
          $e;
          $crate::IResult::Done(i, $name)
        },
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $name: ident: $f:expr => $e:expr) => (
    tap!($i, $name: call!(f) => $e);
  );
);

/// `pair!(I -> IResult<I,O>, I -> IResult<I,P>) => I -> IResult<I, (O,P)>`
/// pair(X,Y), returns (x,y)
///
#[macro_export]
macro_rules! pair(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,o1)   => {
          match $submac2!(i1, $($args2)*) {
            $crate::IResult::Error(a)      => $crate::IResult::Error(a),
            $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
            $crate::IResult::Done(i2,o2)   => {
              $crate::IResult::Done(i2, (o1, o2))
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

/// `separated_pair!(I -> IResult<I,O>, I -> IResult<I, T>, I -> IResult<I,P>) => I -> IResult<I, (O,P)>`
/// separated_pair(X,sep,Y) returns (x,y)
#[macro_export]
macro_rules! separated_pair(
  ($i:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)+) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,o1)   => {
          separated_pair1!(i1, o1,  $($rest)*)
        }
      }
    }
  );

  ($i:expr, $f:expr, $($rest:tt)+) => (
    separated_pair!($i, call!($f), $($rest)*);
  );
);

/// Internal parser, do not use directly
#[macro_export]
macro_rules! separated_pair1(
  ($i:expr, $res1:ident, $submac2:ident!( $($args2:tt)* ), $($rest:tt)+) => (
    {
      match $submac2!($i, $($args2)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i2,_)    => {
          separated_pair2!(i2, $res1,  $($rest)*)
        }
      }
    }
  );
  ($i:expr, $res1:ident, $g:expr, $($rest:tt)+) => (
    separated_pair1!($i, $res1, call!($g), $($rest)*);
  );
);

/// Internal parser, do not use directly
#[macro_export]
macro_rules! separated_pair2(
  ($i:expr, $res1:ident, $submac3:ident!( $($args3:tt)* )) => (
    {
      match $submac3!($i, $($args3)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i3,o3)   => {
          $crate::IResult::Done(i3, ($res1, o3))
        }
      }
    }
  );

  ($i:expr, $res1:ident, $h:expr) => (
    separated_pair2!($i, $res1, call!($h));
  );
);

/// `preceded!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, O>`
/// preceded(opening, X) returns X
#[macro_export]
macro_rules! preceded(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,_)    => {
          match $submac2!(i1, $($args2)*) {
            $crate::IResult::Error(a)      => $crate::IResult::Error(a),
            $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
            $crate::IResult::Done(i2,o2)   => {
              $crate::IResult::Done(i2, o2)
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

/// `terminated!(I -> IResult<I,O>, I -> IResult<I,T>) => I -> IResult<I, O>`
/// terminated(X, closing) returns X
#[macro_export]
macro_rules! terminated(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,o1)   => {
          match $submac2!(i1, $($args2)*) {
            $crate::IResult::Error(a)      => $crate::IResult::Error(a),
            $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
            $crate::IResult::Done(i2,_)    => {
              $crate::IResult::Done(i2, o1)
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

/// `delimited!(I -> IResult<I,T>, I -> IResult<I,O>, I -> IResult<I,U>) => I -> IResult<I, O>`
/// delimited(opening, X, closing) returns X
#[macro_export]
macro_rules! delimited(
  ($i:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)+) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,_)    => {
          delimited1!(i1,  $($rest)*)
        }
      }
    }
  );

  ($i:expr, $f:expr, $($rest:tt)+) => (
    delimited!($i, call!($f), $($rest)*);
  );
);

/// Internal parser, do not use directly
#[macro_export]
macro_rules! delimited1(
  ($i:expr, $submac2:ident!( $($args2:tt)* ), $($rest:tt)+) => (
    {
      match $submac2!($i, $($args2)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i2,o2)   => {
          delimited2!(i2, o2,  $($rest)*)
        }
      }
    }
  );
  ($i:expr, $g:expr, $($rest:tt)+) => (
    delimited1!($i, call!($g), $($rest)*);
  );
);

/// Internal parser, do not use directly
#[macro_export]
macro_rules! delimited2(
  ($i:expr, $res2:ident, $submac3:ident!( $($args3:tt)* )) => (
    {
      match $submac3!($i, $($args3)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i3,_)    => {
          $crate::IResult::Done(i3, $res2)
        }
      }
    }
  );

  ($i:expr, $res2:ident, $h:expr) => (
    delimited2!($i, $res2, call!($h));
  );
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
              if let $crate::IResult::Done(i2,_) = $sep!(input, $($args)*) {
                if i2.len() == input.len() {
                  break;
                }
                input = i2;

                // get the element next
                if let $crate::IResult::Done(i3,o3) = $submac!(input, $($args2)*) {
                  if i3.len() == input.len() {
                    break;
                  }
                  res.push(o3);
                  input = i3;
                } else {
                  break;
                }
              } else {
                break;
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
      let mut res   = Vec::new();
      let mut input = $i;

      // get the first element
      match $submac!(input, $($args2)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i,o)     => {
          if i.len() == input.len() {
            $crate::IResult::Error($crate::Err::Position($crate::ErrorCode::SeparatedNonEmptyList as u32,input))
          } else {
            res.push(o);
            input = i;

            loop {
              if let $crate::IResult::Done(i2,_) = $sep!(input, $($args)*) {
                if i2.len() == input.len() {
                  break;
                }
                input = i2;

                if let $crate::IResult::Done(i3,o3) = $submac!(input, $($args2)*) {
                  if i3.len() == input.len() {
                    break;
                  }
                  res.push(o3);
                  input = i3;
                } else {
                  break;
                }
              } else {
                break;
              }
            }
            $crate::IResult::Done(input, res)
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
      while let $crate::IResult::Done(i,o) = $submac!(input, $($args)*) {
        if i.len() == input.len() {
          break;
        }
        res.push(o);
        input = i;
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
      while let $crate::IResult::Done(i,o) = $submac!(input, $($args)*) {
        if i.len() == input.len() {
          break;
        }
        res.push(o);
        input = i;
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
      let mut input      = $i;
      let mut res        = Vec::new();
      let mut cnt: usize = 0;
      let mut err        = false;
      loop {
        if cnt == $count {
          break
        }
        match $submac!(input, $($args)*) {
          $crate::IResult::Done(i,o) => {
            res.push(o);
            input = i;
            cnt = cnt + 1;
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
        $crate::IResult::Done(input, res)
      } else {
        $crate::IResult::Incomplete($crate::Needed::Unknown)
      }
    }
  );
  ($i:expr, $f:expr, $count: expr) => (
    count!($i, call!($f), $count);
  );
);

/// `count_fixed!(O, I -> IResult<I,O>, nb) => I -> IResult<I, [O; nb]>`
/// Applies the child parser a fixed number of times and returns a fixed size array
/// The type must be specified
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
macro_rules! count_fixed (
  ($i:expr, $typ:ty, $submac:ident!( $($args:tt)* ), $count: expr) => (
    {
      let mut input = $i;
      let mut res: [$typ; $count] = unsafe{[::std::mem::uninitialized(); $count as usize]};
      let mut cnt: usize = 0;
      let mut err = false;
      loop {
        if cnt == $count {
          break
        }
        match $submac!(input, $($args)*) {
          $crate::IResult::Done(i,o) => {
            res[cnt] = o;
            input = i;
            cnt = cnt + 1;
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
        $crate::IResult::Done(input, res)
      } else {
        $crate::IResult::Incomplete($crate::Needed::Unknown)
      }
    }
  );
  ($i:expr, $typ: ty, $f:ident, $count: expr) => (
    count_fixed!($i, $typ, call!($f), $count);
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
          let mut input        = i1;
          let mut res          = Vec::new();
          let mut err          = false;
          let mut inc          = $crate::Needed::Unknown;

          loop {
            if res.len() == nb as usize {
              break;
            }
            match $g(input) {
              $crate::IResult::Done(i2,o2) => {
                res.push(o2);
                input = i2;
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
            $crate::IResult::Done(input, res)
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
          let mut input        = i1;
          let mut res          = Vec::new();
          let mut err          = false;
          let mut inc          = $crate::Needed::Unknown;

          loop {
            if res.len() == nb as usize {
              break;
            }
            match $g(input) {
              $crate::IResult::Done(i2,o2) => {
                res.push(o2);
                input = i2;
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
            $crate::IResult::Done(input, res)
          }

        }
      }
    }
  );
);


#[cfg(test)]
mod tests {
  use internal::{Needed,IResult,Err};
  use internal::IResult::*;
  use internal::Err::*;
  use util::ErrorCode;

  // reproduce the tag and take macros, because of module import order
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


  mod pub_named_mod {
    named!(pub tst, tag!("abcd"));
  }

  #[test]
  fn pub_named_test() {
    let a = &b"abcd"[..];
    let res = pub_named_mod::tst(a);
    assert_eq!(res, Done(&b""[..], a));
  }

  #[test]
  fn apply_test() {
    fn sum2(a:u8, b:u8)       -> u8 { a + b }
    fn sum3(a:u8, b:u8, c:u8) -> u8 { a + b + c }
    let a = apply!(1, sum2, 2);
    let b = apply!(1, sum3, 2, 3);

    assert_eq!(a, 3);
    assert_eq!(b, 6);
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
  fn chain_mut() {
    fn ret_b1_2(i:&[u8]) -> IResult<&[u8], B> { Done(i,B{a:1,b:2}) };
    named!(f<&[u8],B>,
      chain!(
        tag!("abcd")     ~
        tag!("abcd")?    ~
        tag!("efgh")     ~
        mut bb: ret_b1_2 ~
        tag!("efgh")   ,
        ||{
          bb.b = 3;
          bb
        }
      )
    );

    let r = f(&b"abcdabcdefghefghX"[..]);
    assert_eq!(r, Done(&b"X"[..], B{a: 1, b: 3}));
  }

  #[test]
  fn chain_opt() {
    named!(y, tag!("efgh"));
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    named!(ret_y<&[u8], u8>, map!(y, |_| 2));

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
    assert_eq!(r3, Done(&b"X"[..], C{a: 1, b: None}));
  }

  use util::{error_to_list, add_error_pattern, print_error};

  fn error_to_string(e: &Err) -> &'static str {
    let v:Vec<u32> = error_to_list(e);
    // do it this way if you can use slice patterns
    /*
    match &v[..] {
      [42, 0]      => "missing `ijkl` tag",
      [42, 128, 0] => "missing `mnop` tag after `ijkl`",
      _            => "unrecognized error"
    }
    */
    if &v[..] == [42,0] {
      "missing `ijkl` tag"
    } else if &v[..] == [42, 128, 0] {
      "missing `mnop` tag after `ijkl`"
    } else {
      "unrecognized error"
    }
  }

  // do it this way if you can use box patterns
  /*use std::str;
  fn error_to_string(e:Err) -> String
    match e {
      NodePosition(42, i1, box Position(0, i2)) => {
        format!("missing `ijkl` tag, found '{}' instead", str::from_utf8(i2).unwrap())
      },
      NodePosition(42, i1, box NodePosition(128, i2,  box Position(0, i3))) => {
        format!("missing `mnop` tag after `ijkl`, found '{}' instead", str::from_utf8(i3).unwrap())
      },
      _ => "unrecognized error".to_string()
    }
  }*/
  use std::collections;
  #[test]
  fn err() {
    named!(err_test, alt!(
      tag!("abcd") |
      preceded!(tag!("efgh"), error!(42,
          chain!(
                 tag!("ijkl")              ~
            res: error!(128, tag!("mnop")) ,
            || { res }
          )
        )
      )
    ));
    let a = &b"efghblah"[..];
    let b = &b"efghijklblah"[..];
    let c = &b"efghijklmnop"[..];

    let blah = &b"blah"[..];

    let res_a = err_test(a);
    let res_b = err_test(b);
    let res_c = err_test(c);
    assert_eq!(res_a, Error(NodePosition(42, blah, Box::new(Position(0, blah)))));
    assert_eq!(res_b, Error(NodePosition(42, &b"ijklblah"[..], Box::new(NodePosition(128, blah, Box::new(Position(0, blah)))))));
    assert_eq!(res_c, Done(&b""[..], &b"mnop"[..]));

    // Merr-like error matching
    let mut err_map = collections::HashMap::new();
    assert!(add_error_pattern(&mut err_map, err_test(&b"efghpouet"[..]), "missing `ijkl` tag"));
    assert!(add_error_pattern(&mut err_map, err_test(&b"efghijklpouet"[..]), "missing `mnop` tag after `ijkl`"));

    let res_a2 = res_a.clone();
    match res_a {
      Error(e) => {
        assert_eq!(error_to_list(&e), [42, 0]);
        assert_eq!(error_to_string(&e), "missing `ijkl` tag");
        assert_eq!(err_map.get(&error_to_list(&e)), Some(&"missing `ijkl` tag"));
      },
      _ => panic!()
    };

    let res_b2 = res_b.clone();
    match res_b {
      Error(e) => {
        assert_eq!(error_to_list(&e), [42, 128, 0]);
        assert_eq!(error_to_string(&e), "missing `mnop` tag after `ijkl`");
        assert_eq!(err_map.get(&error_to_list(&e)), Some(&"missing `mnop` tag after `ijkl`"));
      },
      _ => panic!()
    };

    print_error(a, res_a2);
    print_error(b, res_b2);
  }

  #[test]
  fn alt() {
    fn work(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Done(&b""[..], input)
    }

    #[allow(unused_variables)]
    fn dont_work(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Error(Code(42))
    }

    fn work2(input: &[u8]) -> IResult<&[u8],&[u8]> {
      Done(input, &b""[..])
    }

    named!(alt1, alt!(dont_work | dont_work));
    named!(alt2, alt!(dont_work | work));
    named!(alt3, alt!(dont_work | dont_work | work2 | dont_work));

    let a = &b"abcd"[..];
    assert_eq!(alt1(a), Error(Position(ErrorCode::Alt as u32, a)));
    assert_eq!(alt2(a), Done(&b""[..], a));
    assert_eq!(alt3(a), Done(a, &b""[..]));

    named!(alt4, alt!(tag!("abcd") | tag!("efgh")));
    let b = &b"efgh"[..];
    assert_eq!(alt4(a), Done(&b""[..], a));
    assert_eq!(alt4(b), Done(&b""[..], b));
  }

  #[test]
  fn alt_incomplete() {
    named!(alt1, alt!(tag!("a") | tag!("bc") | tag!("def")));

    let a = &b""[..];
    assert_eq!(alt1(a), Incomplete(Needed::Size(1)));
    let a = &b"b"[..];
    assert_eq!(alt1(a), Incomplete(Needed::Size(2)));
    let a = &b"bcd"[..];
    assert_eq!(alt1(a), Done(&b"d"[..], &b"bc"[..]));
    let a = &b"cde"[..];
    assert_eq!(alt1(a), Error(Position(ErrorCode::Alt as u32, a)));
    let a = &b"de"[..];
    assert_eq!(alt1(a), Incomplete(Needed::Size(3)));
    let a = &b"defg"[..];
    assert_eq!(alt1(a), Done(&b"g"[..], &b"def"[..]));
  }

  #[test]
  fn switch() {
    named!(sw,
      switch!(take!(4),
        b"abcd" => take!(2) |
        b"efgh" => take!(4)
      )
    );

    let a = &b"abcdefgh"[..];
    assert_eq!(sw(a), Done(&b"gh"[..], &b"ef"[..]));

    let b = &b"efghijkl"[..];
    assert_eq!(sw(b), Done(&b""[..], &b"ijkl"[..]));
    let c = &b"afghijkl"[..];
    assert_eq!(sw(c), Error(Position(ErrorCode::Switch as u32, &b"ijkl"[..])));
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
  fn opt_res() {
    named!(o<&[u8], Result<&[u8], Err> >, opt_res!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    assert_eq!(o(a), Done(&b"ef"[..], Ok(&b"abcd"[..])));
    assert_eq!(o(b), Done(&b"bcdefg"[..], Err(Position(0, b))));
  }

  #[test]
  fn cond() {
    let b = true;
    let f = closure!(&'static [u8], cond!( b, tag!("abcd") ) );

    let a = b"abcdef";
    assert_eq!(f(&a[..]), Done(&b"ef"[..], Some(&b"abcd"[..])));

    let b2 = false;
    let f2 = closure!(&'static [u8], cond!( b2, tag!("abcd") ) );

    assert_eq!(f2(&a[..]), Done(&b"abcdef"[..], None));
  }

  #[test]
  fn cond_wrapping() {
    // Test that cond!() will wrap a given identifier in the call!() macro.

    named!(silly, tag!("foo"));

    let b = true;
    let f = closure!(&'static [u8], cond!( b, silly ) );
    assert_eq!(f(b"foobar"), Done(&b"bar"[..], Some(&b"foo"[..])));
  }

  #[test]
  fn peek() {
    named!(ptag<&[u8],&[u8]>, peek!(tag!("abcd")));

    let r1 = ptag(&b"abcdefgh"[..]);
    assert_eq!(r1, Done(&b"abcdefgh"[..], &b"abcd"[..]));

    let r1 = ptag(&b"efgh"[..]);
    assert_eq!(r1, Error(Position(0,&b"efgh"[..])));
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

  #[cfg(feature = "nightly")]
  use test::Bencher;

  #[cfg(feature = "nightly")]
  #[bench]
  fn many0_bench(b: &mut Bencher) {
    named!(multi<&[u8],Vec<&[u8]> >, many0!(tag!("abcd")));
    b.iter(|| {
      multi(&b"abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"[..])
    });
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
  fn count_zero() {
    fn counter(input: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
      let size: usize = 0;
      count!(input, tag!( "abcd" ), size )
    }

    let a = b"abcdabcdabcdef";
    let res: Vec<&[u8]> = Vec::new();

    assert_eq!(counter(&a[..]), Done(&b"abcdabcdabcdef"[..], res));
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
    named!(counter< [&[u8]; 2] >, count_fixed!( &[u8], tag!( "abcd" ), 2 ) );

    let a = b"abcdabcdabcdef";
    let b = b"abcdefgh";
    let res = [&b"abcd"[..], &b"abcd"[..]];

    assert_eq!(counter(&a[..]), Done(&b"abcdef"[..], res));
    assert_eq!(counter(&b[..]), Error(Position(ErrorCode::Count as u32, &b[..])));
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
