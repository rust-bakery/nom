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
//! to take_while! instead of another combinator.
//!
//! ```ignore
//! macro_rules! take_while(
//!   ($input:expr, $submac:ident!( $($args:tt)* )) => (
//!     {
//!       ...
//!     }
//!   );
//!
//!   // wrap the function in a macro to pass it to the main implementation
//!   ($input:expr, $f:expr) => (
//!     take_while!($input, call!($f));
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
        fn $name( i: $i ) -> $crate::IResult<$i,$o,u32> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$i:ty,$o:ty,$e:ty>, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: $i ) -> $crate::IResult<$i, $o, $e> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: $i ) -> $crate::IResult<$i, $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
        fn $name<'a>( i: &'a[u8] ) -> $crate::IResult<&'a [u8], $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: &[u8] ) -> $crate::IResult<&[u8], &[u8], u32> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: $i ) -> $crate::IResult<$i,$o, u32> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$i:ty,$o:ty,$e:ty>, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: $i ) -> $crate::IResult<$i, $o, $e> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: $i ) -> $crate::IResult<$i, $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: &[u8] ) -> $crate::IResult<&[u8], $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident, $submac:ident!( $($args:tt)* )) => (
        pub fn $name<'a>( i: &'a [u8] ) -> $crate::IResult<&[u8], &[u8], u32> {
            $submac!(i, $($args)*)
        }
    );
);

/// Used to wrap common expressions and function as macros
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult;
/// # fn main() {
///   fn take_wrapper(input: &[u8], i: u8) -> IResult<&[u8],&[u8]> { take!(input, i * 10) }
///
///   // will make a parser taking 20 bytes
///   named!(parser, apply!(take_wrapper, 2));
/// # }
/// ```
#[macro_export]
macro_rules! call (
  ($i:expr, $fun:expr) => ( $fun( $i ) );
  ($i:expr, $fun:expr, $($args:expr),* ) => ( $fun( $i, $($args),* ) );
);

/// emulate function currying: `apply!(my_function, arg1, arg2, ...)` becomes `my_function(input, arg1, arg2, ...)`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult;
/// # fn main() {
///   fn take_wrapper(input: &[u8], i: u8) -> IResult<&[u8],&[u8]> { take!(input, i * 10) }
///
///   // will make a parser taking 20 bytes
///   named!(parser, apply!(take_wrapper, 2));
/// # }
/// ```
#[macro_export]
macro_rules! apply (
  ($i:expr, $fun:expr, $($args:expr),* ) => ( $fun( $i, $($args),* ) );
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
/// # use nom::ErrorKind;
/// # fn main() {
///     named!(err_test, alt!(
///       tag!("abcd") |
///       preceded!(tag!("efgh"), error!(ErrorKind::Custom(42),
///           chain!(
///                  tag!("ijkl")              ~
///             res: error!(ErrorKind::Custom(128), tag!("mnop")) ,
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
///     assert_eq!(res_a, Error(NodePosition(ErrorKind::Custom(42), blah, Box::new(Position(ErrorKind::Tag, blah)))));
///     assert_eq!(res_b, Error(NodePosition(ErrorKind::Custom(42), &b"ijklblah"[..],
///       Box::new(NodePosition(ErrorKind::Custom(128), blah, Box::new(Position(ErrorKind::Tag, blah))))))
///     );
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

/// Add an error if the child parser fails
///
/// While error! does an early return and avoids backtracking,
/// add_error! backtracks normally. It just provides more context
/// for an error
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use std::collections;
/// # use nom::IResult::Error;
/// # use nom::Err::{Position,NodePosition};
/// # use nom::ErrorKind;
/// # fn main() {
///     named!(err_test, add_error!(ErrorKind::Custom(42), tag!("abcd")));
///
///     let a = &b"efghblah"[..];
///     let res_a = err_test(a);
///     assert_eq!(res_a, Error(NodePosition(ErrorKind::Custom(42), a, Box::new(Position(ErrorKind::Tag, a)))));
/// # }
/// ```
///
#[macro_export]
macro_rules! add_error (
  ($i:expr, $code:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
        $crate::IResult::Error(e)      => {
          $crate::IResult::Error($crate::Err::NodePosition($code, $i, Box::new(e)))
        }
      }
    }
  );
  ($i:expr, $code:expr, $f:expr) => (
    add_error!($i, $code, call!($f));
  );
);


/// translate parser result from IResult<I,O,u32> to IResult<I,O,E> with a custom type
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use std::collections;
/// # use nom::IResult::Error;
/// # use nom::Err::{Position,NodePosition};
/// # use nom::ErrorKind;
/// # fn main() {
///     // will add a Custom(42) error to the error chain
///     named!(err_test, add_error!(ErrorKind::Custom(42), tag!("abcd")));
///     // Convert to IREsult<&[u8], &[u8], &str>
///     named!(parser<&[u8], &[u8], &str>, add_error!(ErrorKind::Custom("custom error message"), fix_error!(&str, err_test)));
///
///     let a = &b"efghblah"[..];
///     let res_a = parser(a);
///     assert_eq!(res_a,  Error(NodePosition( ErrorKind::Custom("custom error message"), a, Box::new(Position(ErrorKind::Fix, a)))));
/// # }
/// ```
#[macro_export]
macro_rules! fix_error (
  ($i:expr, $t:ty, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
        $crate::IResult::Error(e) => {
          let err = match e {
            $crate::Err::Code($crate::ErrorKind::Custom(_)) |
              $crate::Err::Node($crate::ErrorKind::Custom(_), _) => {
              let e: $crate::ErrorKind<$t> = $crate::ErrorKind::Fix;
              $crate::Err::Code(e)
            },
            $crate::Err::Position($crate::ErrorKind::Custom(_), p) |
              $crate::Err::NodePosition($crate::ErrorKind::Custom(_), p, _) => {
              let e: $crate::ErrorKind<$t> = $crate::ErrorKind::Fix;
              $crate::Err::Position(e, p)
            },
            $crate::Err::Code(_) |
              $crate::Err::Node(_, _) => {
              let e: $crate::ErrorKind<$t> = $crate::ErrorKind::Fix;
              $crate::Err::Code(e)
            },
            $crate::Err::Position(_, p) |
              $crate::Err::NodePosition(_, p, _) => {
              let e: $crate::ErrorKind<$t> = $crate::ErrorKind::Fix;
              $crate::Err::Position(e, p)
            },
          };
          $crate::IResult::Error(err)
        }
      }
    }
  );
  ($i:expr, $t:ty, $f:expr) => (
    fix_error!($i, $t, call!($f));
  );
);

/// replaces a `Incomplete` returned by the child parser
/// with an `Error`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use std::collections;
/// # use nom::IResult::Error;
/// # use nom::Err::{Position,NodePosition};
/// # use nom::ErrorKind;
/// # fn main() {
///     named!(take_5, complete!(take!(5)));
///
///     let a = &b"abcd"[..];
///     let res_a = take_5(a);
///     assert_eq!(res_a,  Error(Position(ErrorKind::Complete, a)));
/// # }
/// ```
///
#[macro_export]
macro_rules! complete (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete(_) =>  {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Complete, $i))
        },
      }
    }
  );
  ($i:expr, $f:expr) => (
    complete!($i, call!($f));
  );
);

/// A bit like `std::try!`, this macro will return the remaining input and parsed value if the child parser returned `Done`,
/// and will do an early return for `Error` and `Incomplete`
/// this can provide more flexibility than `chain!` if needed
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Error};
/// # use nom::Err::Position;
/// # use nom::{be_u8,ErrorKind};
///
///  fn take_add(input:&[u8], size: u8) -> IResult<&[u8],&[u8]> {
///    let (i1, sz)     = try_parse!(input, be_u8);
///    let (i2, length) = try_parse!(i1, expr_opt!(size.checked_add(sz)));
///    let (i3, data)   = try_parse!(i2, take!(length));
///    return Done(i3, data);
///  }
/// # fn main() {
/// let arr1 = [1, 2, 3, 4, 5];
/// let r1 = take_add(&arr1[..], 1);
/// assert_eq!(r1, Done(&[4,5][..], &[2,3][..]));
///
/// let arr2 = [0xFE, 2, 3, 4, 5];
/// // size is overflowing
/// let r1 = take_add(&arr2[..], 42);
/// assert_eq!(r1, Error(Position(ErrorKind::ExprOpt,&[2,3,4,5][..])));
/// # }
/// ```
#[macro_export]
macro_rules! try_parse (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Done(i,o)     => (i,o),
      $crate::IResult::Error(e)      => return $crate::IResult::Error(e),
      $crate::IResult::Incomplete(i) => return $crate::IResult::Incomplete(i)
    }
  );
  ($i:expr, $f:expr) => (
    try_parse!($i, call!($f))
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
          $crate::IResult::Error(e)                                 => {
            let err = match e {
              $crate::Err::Code(k) | $crate::Err::Node(k, _) | $crate::Err::Position(k, _) | $crate::Err::NodePosition(k, _, _) => {
                $crate::Err::Position(k, $i)
              }
            };
            $crate::IResult::Error(err)
          },
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
    map_impl!($i, $submac!($($args)*), $submac2!($($args2)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    map_impl!($i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    map_impl!($i, call!($f), $submac!($($args)*));
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
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
#[doc(hidden)]
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
          Err(_)     => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::MapRes, $i))
        }
      }
    }
  );
);


/// `map_opt!(I -> IResult<I,O>, O -> Option<P>) => I -> IResult<I, P>`
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
#[doc(hidden)]
#[macro_export]
macro_rules! map_opt_impl (
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done(i, o)                          => match $submac2!(o, $($args2)*) {
          ::std::option::Option::Some(output) => $crate::IResult::Done(i, output),
          ::std::option::Option::None         => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::MapOpt, $i))
        }
      }
    }
  );
);

/// `value!(T, R -> IResult<R, S> ) => R -> IResult<R, T>`
///
/// or `value!(T) => R -> IResult<R, T>`
///
/// If the child parser was successful, return the value.
/// If no child parser is provided, always return the value
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(x<u8>, value!(42, delimited!(tag!("<!--"), take!(5), tag!("-->"))));
///  named!(y<u8>, delimited!(tag!("<!--"), value!(42), tag!("-->")));
///  let r = x(&b"<!-- abc --> aaa"[..]);
///  assert_eq!(r, Done(&b" aaa"[..], 42));
///
///  let r2 = y(&b"<!----> aaa"[..]);
///  assert_eq!(r2, Done(&b" aaa"[..], 42));
/// # }
/// ```
#[macro_export]
macro_rules! value (
  ($i:expr, $res:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Done(i,_)     => {
          $crate::IResult::Done(i, $res)
        },
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $res:expr, $f:expr) => (
    value!($i, $res, call!($f))
  );
  ($i:expr, $res:expr) => (
    $crate::IResult::Done($i, $res)
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
        Err(_)     => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::ExprRes, $i))
      }
    }
  );
);

/// `expr_opt!(Option<O>) => I -> IResult<I, O>`
/// evaluate an expression that returns a Option<T> and returns a IResult::Done(I,T) if Some
///
/// Useful when doing computations in a chain
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Error};
/// # use nom::Err::Position;
/// # use nom::{be_u8,ErrorKind};
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
/// assert_eq!(r1, Error(Position(ErrorKind::ExprOpt,&[2,3,4,5][..])));
/// # }
/// ```
#[macro_export]
macro_rules! expr_opt (
  ($i:expr, $e:expr) => (
    {
      match $e {
        ::std::option::Option::Some(output) => $crate::IResult::Done($i, output),
        ::std::option::Option::None         => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::ExprOpt, $i))
      }
    }
  );
);

/// `chain!(I->IResult<I,A> ~ I->IResult<I,B> ~ ... I->IResult<I,X> , || { return O } ) => I -> IResult<I, O>`
/// chains parsers and assemble the results through a closure
///
/// The input type `I` must implement `nom::InputLength`.
///
/// This combinator will count how much data is consumed by every child parser and take it into account if
/// there is not enough data
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Error};
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
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
///      tag!("abcd")  ~     // the '~' character is used as separator
///      aa: ret_int   ~     // the result of that parser will be used in the closure
///      tag!("abcd")? ~     // this parser is optional
///      bb: ret_y?    ,     // the result of that parser is an option
///                          // the last parser in the chain is followed by a ','
///      ||{B{a: aa, b: bb}}
///    )
///  );
///
/// # fn main() {
/// // the first "abcd" tag is not present, we have an error
/// let r1 = z(&b"efgh"[..]);
/// assert_eq!(r1, Error(Position(ErrorKind::Tag,&b"efgh"[..])));
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
    {
      chaining_parser!($i, 0usize, $($rest)*)
    }
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! chaining_parser (
  ($i:expr, $consumed:expr, $e:ident ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, call!($e) ~ $($rest)*);
  );
  ($i:expr, $consumed:expr, $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,_)     => {
          chaining_parser!(i, $consumed + ($crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i)), $($rest)*)
        }
      }
    }
);

  ($i:expr, $consumed:expr, $e:ident ? ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, call!($e) ? ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => (
    {
      let res = $submac!($i, $($args)*);
      if let $crate::IResult::Incomplete(inc) = res {
        match inc {
          $crate::Needed::Unknown => $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::Needed::Size(i) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        }
      } else {
        let input = if let $crate::IResult::Done(i,_) = res {
          i
        } else {
          $i
        };
        chaining_parser!(input, $consumed + ($crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&input)), $($rest)*)
      }
    }
  );

  ($i:expr, $consumed:expr, $field:ident : $e:ident ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, $field: call!($e) ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    {
      match  $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          let $field = o;
          chaining_parser!(i, $consumed + ($crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i)), $($rest)*)
        }
      }
    }
  );

  ($i:expr, $consumed:expr, mut $field:ident : $e:ident ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, mut $field: call!($e) ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, mut $field:ident : $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    {
      match  $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          let mut $field = o;
          chaining_parser!(i, $consumed + $crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i), $($rest)*)
        }
      }
    }
  );

  ($i:expr, $consumed:expr, $field:ident : $e:ident ? ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, $field : call!($e) ? ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => (
    {
      let res = $submac!($i, $($args)*);
      if let $crate::IResult::Incomplete(inc) = res {
        match inc {
          $crate::Needed::Unknown => $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::Needed::Size(i) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        }
      } else {
        let ($field,input) = if let $crate::IResult::Done(i,o) = res {
          (::std::option::Option::Some(o),i)
        } else {
          (::std::option::Option::None,$i)
        };
        chaining_parser!(input, $consumed + $crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&input), $($rest)*)
      }
    }
  );

  ($i:expr, $consumed:expr, mut $field:ident : $e:ident ? ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, mut $field : call!($e) ? ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, mut $field:ident : $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => (
    {
      let res = $submac!($i, $($args)*);
      if let $crate::IResult::Incomplete(inc) = res {
        match inc {
          $crate::Needed::Unknown => $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::Needed::Size(i) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        }
      } else {
        let (mut $field,input) = if let $crate::IResult::Done(i,o) = res {
          (::std::option::Option::Some(o),i)
        } else {
          (::std::option::Option::None,$i)
        };
        chaining_parser!(input, $consumed + $crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&input), $($rest)*)
      }
    }
  );

  // ending the chain
  ($i:expr, $consumed:expr, $e:ident, $assemble:expr) => (
    chaining_parser!($i, $consumed, call!($e), $assemble);
  );

  ($i:expr, $consumed:expr, $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
      $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
      $crate::IResult::Done(i,_)     => {
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $consumed:expr, $e:ident ?, $assemble:expr) => (
    chaining_parser!($i, $consumed, call!($e) ?, $assemble);
  );

  ($i:expr, $consumed:expr, $submac:ident!( $($args:tt)* ) ?, $assemble:expr) => ({
    let res = $submac!($i, $($args)*);
    if let $crate::IResult::Incomplete(inc) = res {
      match inc {
        $crate::Needed::Unknown => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::Needed::Size(i) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
      }
    } else {
      let input = if let $crate::IResult::Done(i,_) = res {
        i
      } else {
        $i
      };
      $crate::IResult::Done(input, $assemble())
    }
  });

  ($i:expr, $consumed:expr, $field:ident : $e:ident, $assemble:expr) => (
    chaining_parser!($i, $consumed, $field: call!($e), $assemble);
  );

  ($i:expr, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
      $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
      $crate::IResult::Done(i,o)     => {
        let $field = o;
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $consumed:expr, mut $field:ident : $e:ident, $assemble:expr) => (
    chaining_parser!($i, $consumed, mut $field: call!($e), $assemble);
  );

  ($i:expr, $consumed:expr, mut $field:ident : $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
      $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
      $crate::IResult::Done(i,o)     => {
        let mut $field = o;
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $consumed:expr, $field:ident : $e:ident ? , $assemble:expr) => (
    chaining_parser!($i, $consumed, $field : call!($e) ? , $assemble);
  );

  ($i:expr, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ) ? , $assemble:expr) => ({
    let res = $submac!($i, $($args)*);
    if let $crate::IResult::Incomplete(inc) = res {
      match inc {
        $crate::Needed::Unknown => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::Needed::Size(i) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
      }
    } else {
      let ($field,input) = if let $crate::IResult::Done(i,o) = res {
        (::std::option::Option::Some(o), i)
      } else {
        (::std::option::Option::None, $i)
      };
      $crate::IResult::Done(input, $assemble())
    }
  });

  ($i:expr, $consumed:expr, mut $field:ident : $e:ident ? , $assemble:expr) => (
    chaining_parser!($i, $consumed, $field : call!($e) ? , $assemble);
  );

  ($i:expr, $consumed:expr, mut $field:ident : $submac:ident!( $($args:tt)* ) ? , $assemble:expr) => ({
    let res = $submac!($i, $($args)*);
    if let $crate::IResult::Incomplete(inc) = res {
      match inc {
        $crate::Needed::Unknown => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::Needed::Size(i) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
      }
    } else {
      let (mut $field,input) = if let $crate::IResult::Done(i,o) = res {
        (::std::option::Option::Some(o), i)
      } else {
        (::std::option::Option::None, $i)
      };
      $crate::IResult::Done(input, $assemble())
    }
  });

  ($i:expr, $consumed:expr, $assemble:expr) => (
    $crate::IResult::Done($i, $assemble())
  )
);


/// `tuple!(I->IResult<I,A>, I->IResult<I,B>, ... I->IResult<I,X>) => I -> IResult<I, (A, B, ..., X)>`
/// chains parsers and assemble the sub results in a tuple.
///
/// The input type `I` must implement `nom::InputLength`.
///
/// This combinator will count how much data is consumed by every child parser and take it into account if
/// there is not enough data
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Error};
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # use nom::be_u16;
/// // the return type depends of the children parsers
/// named!(parser<&[u8], (u16, &[u8], &[u8]) >,
///   tuple!(
///     be_u16 ,
///     take!(3),
///     tag!("fg")
///   )
/// );
///
/// # fn main() {
/// assert_eq!(
///   parser(&b"abcdefgh"[..]),
///   Done(
///     &b"h"[..],
///     (0x6162u16, &b"cde"[..], &b"fg"[..])
///   )
/// );
/// # }
/// ```
#[macro_export]
macro_rules! tuple (
  ($i:expr, $($rest:tt)*) => (
    {
      tuple_parser!($i, 0usize, (), $($rest)*)
    }
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! tuple_parser (
  ($i:expr, $consumed:expr, ($($parsed:tt),*), $e:ident, $($rest:tt)*) => (
    tuple_parser!($i, $consumed, ($($parsed),*), call!($e), $($rest)*);
  );
  ($i:expr, $consumed:expr, (), $submac:ident!( $($args:tt)* ), $($rest:tt)*) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          tuple_parser!(i, $consumed + ($crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i)), (o), $($rest)*)
        }
      }
    }
  );
  ($i:expr, $consumed:expr, ($($parsed:tt)*), $submac:ident!( $($args:tt)* ), $($rest:tt)*) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          tuple_parser!(i, $consumed + ($crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i)), ($($parsed)* , o), $($rest)*)
        }
      }
    }
  );
  ($i:expr, $consumed:expr, ($($parsed:tt),*), $e:ident) => (
    tuple_parser!($i, $consumed, ($($parsed),*), call!($e));
  );
  ($i:expr, $consumed:expr, (), $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          $crate::IResult::Done(i, (o))
        }
      }
    }
  );
  ($i:expr, $consumed:expr, ($($parsed:expr),*), $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          $crate::IResult::Done(i, ($($parsed),* , o))
        }
      }
    }
  );
  ($i:expr, $consumed:expr, ($($parsed:expr),*)) => (
    {
      $crate::IResult::Done($i, ($($parsed),*))
    }
  );
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
///
/// **BE CAREFUL** there is a case where the behaviour of `alt!` can be confusing:
///
/// when the alternatives have different lengths, like this case:
///
/// ```ignore
///  named!( test, alt!( tag!( "abcd" ) | tag!( "ef" ) | tag!( "ghi" ) | tag!( "kl" ) ) );
/// ```
///
/// With this parser, if you pass `"abcd"` as input, the first alternative parses it correctly,
/// but if you pass `"efg"`, the first alternative will return `Incomplete`, since it needs an input
/// of 4 bytes. This behaviour of `alt!` is expected: if you get a partial input that isn't matched
/// by the first alternative, but would match if the input was complete, you want `alt!` to indicate
/// that it cannot decide with limited information.
///
/// There are two ways to fix this behaviour. The first one consists in ordering the alternatives
/// by size, like this:
///
/// ```ignore
///  named!( test, alt!( tag!( "ef" ) | tag!( "kl") | tag!( "ghi" ) | tag!( "abcd" ) ) );
/// ```
///
/// With this solution, the largest alternative will be tested last.
///
/// The other solution uses the `complete!` combinator, which transforms an `Incomplete` in an
/// `Error`. If one of the alternatives returns `Incomplete` but is wrapped by `complete!`,
/// `alt!` will try the next alternative. This is useful when you know that
/// you will not get partial input:
///
/// ```ignore
///  named!( test,
///    alt!(
///      complete!( tag!( "abcd" ) ) |
///      complete!( tag!( "ef"   ) ) |
///      complete!( tag!( "ghi"  ) ) |
///      complete!( tag!( "kl"   ) )
///    )
///  );
/// ```
///
/// If you want the `complete!` combinator to be applied to all rules then use the convenience
/// `alt_complete!` macro (see below).
///
/// This behaviour of `alt!` can get especially confusing if multiple alternatives have different
/// sizes but a common prefix, like this:
///
/// ```ignore
///  named!( test, alt!( tag!( "abcd" ) | tag!( "ab" ) | tag!( "ef" ) ) );
/// ```
///
/// in that case, if you order by size, passing `"abcd"` as input will always be matched by the
/// smallest parser, so the solution using `complete!` is better suited.
///
/// You can also nest multiple `alt!`, like this:
///
/// ```ignore
///  named!( test,
///    alt!(
///      preceded!(
///        tag!("ab"),
///        alt!(
///          tag!( "cd" ) |
///          eof
///        )
///      )
///    | tag!( "ef" )
///    )
///  );
/// ```
///
///  `preceded!` will first parse `"ab"` then, if successful, try the alternatives "cd",
///  or empty input (End Of File). If none of them work, `preceded!` will fail and
///  "ef" will be tested.
///
#[macro_export]
macro_rules! alt (
  ($i:expr, $($rest:tt)*) => (
    {
      alt_parser!($i, $($rest)*)
    }
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! alt_parser (
  ($i:expr, $e:ident | $($rest:tt)*) => (
    alt_parser!($i, call!($e) | $($rest)*);
  );

  ($i:expr, $subrule:ident!( $($args:tt)*) | $($rest:tt)*) => (
    {
      let res = $subrule!($i, $($args)*);
      match res {
        $crate::IResult::Done(_,_)     => res,
        $crate::IResult::Incomplete(_) => res,
        _                              => alt_parser!($i, $($rest)*)
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
    $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Alt,$i))
  );
);

/// This is a combination of the `alt!` and `complete!` combinators. Rather
/// than returning `Incomplete` on partial input, `alt_complete!` will try the
/// next alternative in the chain. You should use this only if you know you
/// will not receive partial input for the rules you're trying to match (this
/// is almost always the case for parsing programming languages).
#[macro_export]
macro_rules! alt_complete (
  // Recursive rules (must include `complete!` around the head)

  ($i:expr, $e:ident | $($rest:tt)*) => (
    alt_complete!($i, complete!(call!($e)) | $($rest)*);
  );

  ($i:expr, $subrule:ident!( $($args:tt)*) | $($rest:tt)*) => (
    {
      let res = complete!($i, $subrule!($($args)*));
      match res {
        $crate::IResult::Done(_,_) => res,
        _ => alt_complete!($i, $($rest)*),
      }
    }
  );

  ($i:expr, $subrule:ident!( $($args:tt)* ) => { $gen:expr } | $($rest:tt)+) => (
    {
      match complete!($i, $subrule!($($args)*)) {
        $crate::IResult::Done(i,o) => $crate::IResult::Done(i,$gen(o)),
        _ => alt_complete!($i, $($rest)*),
      }
    }
  );

  ($i:expr, $e:ident => { $gen:expr } | $($rest:tt)*) => (
    alt_complete!($i, complete!(call!($e)) => { $gen } | $($rest)*);
  );

  // Tail (non-recursive) rules

  ($i:expr, $e:ident => { $gen:expr }) => (
    alt_complete!($i, call!($e) => { $gen });
  );

  ($i:expr, $subrule:ident!( $($args:tt)* ) => { $gen:expr }) => (
    alt_parser!($i, $subrule!($($args)*) => { $gen })
  );

  ($i:expr, $e:ident) => (
    alt_complete!($i, call!($e));
  );

  ($i:expr, $subrule:ident!( $($args:tt)*)) => (
    alt_parser!($i, $subrule!($($args)*))
  );
);

/// `switch!(I -> IResult<I,P>, P => I -> IResult<I,O> | ... | P => I -> IResult<I,O> ) => I -> IResult<I, O>`
/// choose the next parser depending on the result of the first one, if successful,
/// and returns the result of the second parser
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done,Error};
/// # use nom::Err::{Position, NodePosition};
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(sw,
///    switch!(take!(4),
///      b"abcd" => tag!("XYZ") |
///      b"efgh" => tag!("123")
///    )
///  );
///
///  let a = b"abcdXYZ123";
///  let b = b"abcdef";
///  let c = b"efgh123";
///  let d = b"blah";
///
///  assert_eq!(sw(&a[..]), Done(&b"123"[..], &b"XYZ"[..]));
///  assert_eq!(sw(&b[..]), Error(NodePosition(ErrorKind::Switch, &b"abcdef"[..], Box::new(Position(ErrorKind::Tag, &b"ef"[..])))));
///  assert_eq!(sw(&c[..]), Done(&b""[..], &b"123"[..]));
///  assert_eq!(sw(&d[..]), Error(Position(ErrorKind::Switch, &b"blah"[..])));
///  # }
/// ```
///
/// Due to limitations in Rust macros, it is not possible to have simple functions on the right hand
/// side of pattern, like this:
///
/// ```ignore
///  named!(sw,
///    switch!(take!(4),
///      b"abcd" => tag!("XYZ") |
///      b"efgh" => tag!("123")
///    )
///  );
/// ```
///
/// If you want to pass your own functions instead, you can use the `call!` combinator as follows:
///
/// ```ignore
///  named!(xyz, tag!("XYZ"));
///  named!(num, tag!("123"));
///  named!(sw,
///    switch!(take!(4),
///      b"abcd" => call!(xyz) |
///      b"efgh" => call!(num)
///    )
///  );
/// ```
///
#[macro_export]
macro_rules! switch (
  ($i:expr, $submac:ident!( $($args:tt)*), $($rest:tt)*) => (
    {
      switch_impl!($i, $submac!($($args)*), $($rest)*)
    }
  );
  ($i:expr, $e:ident, $($rest:tt)*) => (
    {
      switch_impl!($i, call!($e), $($rest)*)
    }
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! switch_impl (
  ($i:expr, $submac:ident!( $($args:tt)* ), $($p:pat => $subrule:ident!( $($args2:tt)* ))|* ) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error($crate::Err::NodePosition(
            $crate::ErrorKind::Switch, $i, ::std::boxed::Box::new(e)
        )),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i, o)    => {
          match o {
            $($p => match $subrule!(i, $($args2)*) {
              $crate::IResult::Error(e) => $crate::IResult::Error($crate::Err::NodePosition(
                  $crate::ErrorKind::Switch, $i, ::std::boxed::Box::new(e)
              )),
              a => a,
            }),*,
            _    => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Switch,$i))
          }
        }
      }
    }
  );
);
/// `opt!(I -> IResult<I,O>) => I -> IResult<I, Option<O>>`
/// make the underlying parser optional
///
/// returns an Option of the returned type. This parser returns `Some(result)` if the child parser
/// succeeds,`None` if it fails, and `Incomplete` if it did not have enough data to decide
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
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, ::std::option::Option::Some(o)),
        $crate::IResult::Error(_)      => $crate::IResult::Done($i, ::std::option::Option::None),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
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
/// # use nom::ErrorKind;
/// # fn main() {
///  named!( o<&[u8], Result<&[u8], nom::Err<&[u8]> > >, opt_res!( tag!( "abcd" ) ) );
///
///  let a = b"abcdef";
///  let b = b"bcdefg";
///  assert_eq!(o(&a[..]), Done(&b"ef"[..], Ok(&b"abcd"[..])));
///  assert_eq!(o(&b[..]), Done(&b"bcdefg"[..], Err(Position(ErrorKind::Tag, &b[..]))));
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

/// `cond_with_error!(bool, I -> IResult<I,O>) => I -> IResult<I, Option<O>>`
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
/// # use nom::IResult;
/// # fn main() {
///  let b = true;
///  let f: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>>> = Box::new(closure!(&'static[u8],
///    cond!( b, tag!("abcd") ))
///  );
///
///  let a = b"abcdef";
///  assert_eq!(f(&a[..]), Done(&b"ef"[..], Some(&b"abcd"[..])));
///
///  let b2 = false;
///  let f2:Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>>> = Box::new(closure!(&'static[u8],
///    cond!( b2, tag!("abcd") ))
///  );
///  assert_eq!(f2(&a[..]), Done(&b"abcdef"[..], None));
///  # }
/// ```
///
#[macro_export]
macro_rules! cond_with_error(
  ($i:expr, $cond:expr, $submac:ident!( $($args:tt)* )) => (
    {
      if $cond {
        match $submac!($i, $($args)*) {
          $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, ::std::option::Option::Some(o)),
          $crate::IResult::Error(e)      => $crate::IResult::Error(e),
          $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
        }
      } else {
        $crate::IResult::Done($i, ::std::option::Option::None)
      }
    }
  );
  ($i:expr, $cond:expr, $f:expr) => (
    cond!($i, $cond, call!($f));
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
/// # use nom::IResult;
/// # fn main() {
///  let b = true;
///  let f: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>>> = Box::new(closure!(&'static[u8],
///    cond!( b, tag!("abcd") ))
///  );
///
///  let a = b"abcdef";
///  assert_eq!(f(&a[..]), Done(&b"ef"[..], Some(&b"abcd"[..])));
///
///  let b2 = false;
///  let f2:Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>>> = Box::new(closure!(&'static[u8],
///    cond!( b2, tag!("abcd") ))
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
          $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, ::std::option::Option::Some(o)),
          $crate::IResult::Error(_)      => $crate::IResult::Done($i, ::std::option::Option::None),
          $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
        }
      } else {
        $crate::IResult::Done($i, ::std::option::Option::None)
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
/// # use nom::{Err,ErrorKind};
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
///  assert_eq!(f2(&a[..]), Error(Err::Position(ErrorKind::CondReduce, &a[..])));
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
        $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::CondReduce, $i))
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
    peek!($i, call!($f));
  );
);

/// `not!(I -> IResult<I,0>) => I -> IResult<I, O>`
/// returns a result only if the embedded parser returns Error or Incomplete
/// does not consume the input
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # use nom::Err::{Position};
/// # use nom::ErrorKind;
/// # fn main() {
/// named!(not_e, chain!(
///     res: tag!("abc") ~ 
///          not!(char!('e')),
///     || { res }));
///
/// let r = not_e(&b"abcd"[..]); 
/// assert_eq!(r, Done(&b"d"[..], &b"abc"[..]));
///
/// let r2 = not_e(&b"abce"[..]);
/// assert_eq!(r2, Error(Position(ErrorKind::Not, &b"e"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! not(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Done(_, _)    => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Not, $i)),
        $crate::IResult::Error(_)      => $crate::IResult::Done($i, &($i)[..0]),
        $crate::IResult::Incomplete(_) => $crate::IResult::Done($i, &($i)[..0])
      }
    }
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
    tap!($i, $name: call!($f) => $e);
  );
);

/// `pair!(I -> IResult<I,O>, I -> IResult<I,P>) => I -> IResult<I, (O,P)>`
/// pair(X,Y), returns (x,y)
///
#[macro_export]
macro_rules! pair(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      tuple!($i, $submac!($($args)*), $submac2!($($args2)*))
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
      match tuple_parser!($i, 0usize, (), $submac!($($args)*), $($rest)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1, (o1, _, o2))   => {
          $crate::IResult::Done(i1, (o1, o2))
        }
      }
    }
  );

  ($i:expr, $f:expr, $($rest:tt)+) => (
    separated_pair!($i, call!($f), $($rest)*);
  );
);

/// `preceded!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, O>`
/// preceded(opening, X) returns X
#[macro_export]
macro_rules! preceded(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match tuple!($i, $submac!($($args)*), $submac2!($($args2)*)) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(remaining, (_,o))    => {
          $crate::IResult::Done(remaining, o)
        }
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
      match tuple!($i, $submac!($($args)*), $submac2!($($args2)*)) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(remaining, (o,_))    => {
          $crate::IResult::Done(remaining, o)
        }
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
      match tuple_parser!($i, 0usize, (), $submac!($($args)*), $($rest)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1, (_, o, _))   => {
          $crate::IResult::Done(i1, o)
        }
      }
    }
  );

  ($i:expr, $f:expr, $($rest:tt)+) => (
    delimited!($i, call!($f), $($rest)*);
  );
);

/// `separated_list!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// separated_list(sep, X) returns Vec<X>
#[macro_export]
macro_rules! separated_list(
  ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => (
    {
      let mut res   = ::std::vec::Vec::new();
      let mut input = $i;

      // get the first element
      match $submac!(input, $($args2)*) {
        $crate::IResult::Error(_)      => $crate::IResult::Done(input, ::std::vec::Vec::new()),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i,o)     => {
          if i.len() == input.len() {
            $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::SeparatedList,input))
          } else {
            res.push(o);
            input = i;

            loop {
              // get the separator first
              if let $crate::IResult::Done(i2,_) = $sep!(input, $($args)*) {
                if i2.len() == input.len() {
                  break;
                }

                // get the element next
                if let $crate::IResult::Done(i3,o3) = $submac!(i2, $($args2)*) {
                  if i3.len() == i2.len() {
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
      let mut res   = ::std::vec::Vec::new();
      let mut input = $i;

      // get the first element
      match $submac!(input, $($args2)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i,o)     => {
          if i.len() == input.len() {
            $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::SeparatedNonEmptyList,input))
          } else {
            res.push(o);
            input = i;

            loop {
              if let $crate::IResult::Done(i2,_) = $sep!(input, $($args)*) {
                if i2.len() == input.len() {
                  break;
                }

                if let $crate::IResult::Done(i3,o3) = $submac!(i2, $($args2)*) {
                  if i3.len() == i2.len() {
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
///  let a = b"abcdabcdefgh";
///  let b = b"azerty";
///
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&a[..]), Done(&b"efgh"[..], res));
///  assert_eq!(multi(&b[..]), Done(&b"azerty"[..], Vec::new()));
/// # }
/// ```
/// 0 or more
#[macro_export]
macro_rules! many0(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::InputLength;

      let ret;
      let mut res   = ::std::vec::Vec::new();
      let mut input = $i;

      loop {
        if input.input_len() == 0 {
          ret = $crate::IResult::Done(input, res); break;
        }

        match $submac!(input, $($args)*) {
          $crate::IResult::Error(_)                            => {
            ret = $crate::IResult::Done(input, res); break;
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown) => {
            ret = $crate::IResult::Incomplete($crate::Needed::Unknown); break;
          },
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
            let size = i + ($i).input_len() - input.input_len();
            ret = $crate::IResult::Incomplete($crate::Needed::Size(size)); break;
          },
          $crate::IResult::Done(i, o)                          => {
            // loop trip must always consume (otherwise infinite loops)
            if i == input {
              ret = $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Many0,input)); break;
            }

            res.push(o);
            input = i;
          }
        }
      }

      ret
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
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >, many1!( tag!( "abcd" ) ) );
///
///  let a = b"abcdabcdefgh";
///  let b = b"azerty";
///
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&a[..]), Done(&b"efgh"[..], res));
///  assert_eq!(multi(&b[..]), Error(Position(ErrorKind::Many1,&b[..])));
/// # }
/// ```
#[macro_export]
macro_rules! many1(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::InputLength;
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(_)      => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Many1,$i)),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,o1)   => {
          if i1.input_len() == 0 {
            $crate::IResult::Done(i1,vec![o1])
          } else {

            let mut res    = ::std::vec::Vec::with_capacity(4);
            res.push(o1);
            let mut input  = i1;
            let mut incomplete: ::std::option::Option<$crate::Needed> = ::std::option::Option::None;
            loop {
              if input.input_len() == 0 {
                break;
              }
              match $submac!(input, $($args)*) {
                $crate::IResult::Error(_)                    => {
                  break;
                },
                $crate::IResult::Incomplete($crate::Needed::Unknown) => {
                  incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
                  break;
                },
                $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
                  incomplete = ::std::option::Option::Some($crate::Needed::Size(i + ($i).input_len() - input.input_len()));
                  break;
                },
                $crate::IResult::Done(i, o) => {
                  if i.input_len() == input.input_len() {
                    break;
                  }
                  res.push(o);
                  input = i;
                }
              }
            }

            match incomplete {
              ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
              ::std::option::Option::None    => $crate::IResult::Done(input, res)
            }
          }
        }
      }
    }
  );
  ($i:expr, $f:expr) => (
    many1!($i, call!($f));
  );
);

/// `many_m_n!(usize, usize, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// Applies the parser between m and n times (n included) and returns the list of results in a Vec
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >, many_m_n!(2, 4, tag!( "abcd" ) ) );
///
///  let a = b"abcdefgh";
///  let b = b"abcdabcdefgh";
///  let c = b"abcdabcdabcdabcdabcdefgh";
///
///  assert_eq!(multi(&a[..]),Error(Position(ErrorKind::ManyMN,&a[..])));
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&b[..]), Done(&b"efgh"[..], res));
///  let res2 = vec![&b"abcd"[..], &b"abcd"[..], &b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&c[..]), Done(&b"abcdefgh"[..], res2));
/// # }
/// ```
#[macro_export]
macro_rules! many_m_n(
  ($i:expr, $m:expr, $n: expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::InputLength;
      let mut res          = ::std::vec::Vec::with_capacity($m);
      let mut input        = $i;
      let mut count: usize = 0;
      let mut err          = false;
      let mut incomplete: ::std::option::Option<$crate::Needed> = ::std::option::Option::None;
      loop {
        if count == $n { break }
        match $submac!(input, $($args)*) {
          $crate::IResult::Done(i, o) => {
            // do not allow parsers that do not consume input (causes infinite loops)
            if i.input_len() == input.input_len() {
              break;
            }
            res.push(o);
            input  = i;
            count += 1;
          }
          $crate::IResult::Error(_)                    => {
            err = true;
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown) => {
            incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
            incomplete = ::std::option::Option::Some($crate::Needed::Size(i + ($i).input_len() - input.input_len()));
            break;
          },
        }
        if input.input_len() == 0 {
          break;
        }
      }

      if count < $m {
        if err {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::ManyMN,$i))
        } else {
          match incomplete {
            ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
            ::std::option::Option::None    => $crate::IResult::Incomplete($crate::Needed::Unknown)
          }
        }
      } else {
        match incomplete {
          ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
          ::std::option::Option::None    => $crate::IResult::Done(input, res)
        }
      }
    }
  );
  ($i:expr, $m:expr, $n: expr, $f:expr) => (
    many_m_n!($i, $m, $n, call!($f));
  );
);

/// `count!(I -> IResult<I,O>, nb) => I -> IResult<I, Vec<O>>`
/// Applies the child parser a specified number of times
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done,Error};
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(counter< Vec<&[u8]> >, count!( tag!( "abcd" ), 2 ) );
///
///  let a = b"abcdabcdabcdef";
///  let b = b"abcdefgh";
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///
///  assert_eq!(counter(&a[..]), Done(&b"abcdef"[..], res));
///  assert_eq!(counter(&b[..]), Error(Position(ErrorKind::Count, &b[..])));
/// # }
/// ```
///
#[macro_export]
macro_rules! count(
  ($i:expr, $submac:ident!( $($args:tt)* ), $count: expr) => (
    {
      let ret;
      let mut input = $i;
      let mut res   = ::std::vec::Vec::with_capacity($count);

      loop {
        if res.len() == $count {
          ret = $crate::IResult::Done(input, res); break;
        }

        match $submac!(input, $($args)*) {
          $crate::IResult::Done(i,o) => {
            res.push(o);
            input = i;
          },
          $crate::IResult::Error(_)  => {
            ret = $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Count,$i)); break;
          },
          $crate::IResult::Incomplete(_) => {
            ret = $crate::IResult::Incomplete($crate::Needed::Unknown); break;
          }
        }
      }

      ret
    }
  );
  ($i:expr, $f:expr, $count: expr) => (
    count!($i, call!($f), $count);
  );
);

/// `count_fixed!(O, I -> IResult<I,O>, nb) => I -> IResult<I, [O; nb]>`
/// Applies the child parser a fixed number of times and returns a fixed size array
/// The type must be specified and it must be `Copy`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done,Error};
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
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
///  assert_eq!(counter(&b[..]), Error(Position(ErrorKind::Count, &b[..])));
/// # }
/// ```
///
#[macro_export]
macro_rules! count_fixed (
  ($i:expr, $typ:ty, $submac:ident!( $($args:tt)* ), $count: expr) => (
    {
      let ret;
      let mut input = $i;
      // `$typ` must be Copy, and thus having no destructor, this is panic safe
      let mut res: [$typ; $count] = unsafe{[::std::mem::uninitialized(); $count as usize]};
      let mut cnt: usize = 0;

      loop {
        if cnt == $count {
          ret = $crate::IResult::Done(input, res); break;
        }

        match $submac!(input, $($args)*) {
          $crate::IResult::Done(i,o) => {
            res[cnt] = o;
            cnt += 1;
            input = i;
          },
          $crate::IResult::Error(_)  => {
            ret = $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Count,$i)); break;
          },
          $crate::IResult::Incomplete(_) => {
            ret = $crate::IResult::Incomplete($crate::Needed::Unknown); break;
          }
        }
      }

      ret
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
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Done(inum, onum)   => {
          let ret;
          let length_token = $i.len() - inum.len();
          let mut input    = inum;
          let mut res      = ::std::vec::Vec::new();

          loop {
            if res.len() == onum as usize {
              ret = $crate::IResult::Done(input, res); break;
            }

            match $g(input) {
              $crate::IResult::Done(iparse, oparse) => {
                res.push(oparse);
                input = iparse;
              },
              $crate::IResult::Error(_)      => {
                ret = $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::LengthValue,$i)); break;
              },
              $crate::IResult::Incomplete(a) => {
                ret = match a {
                  $crate::Needed::Unknown      => $crate::IResult::Incomplete($crate::Needed::Unknown),
                  $crate::Needed::Size(length) => $crate::IResult::Incomplete($crate::Needed::Size(length_token + onum as usize * length))
                };
                break;
              }
            }
          }

          ret
        }
      }
    }
  );
  ($i:expr, $f:expr, $g:expr, $length:expr) => (
    {
      match $f($i) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Done(inum, onum)   => {
          let ret;
          let length_token = $i.len() - inum.len();
          let mut input    = inum;
          let mut res      = ::std::vec::Vec::new();

          loop {
            if res.len() == onum as usize {
              ret = $crate::IResult::Done(input, res); break;
            }

            match $g(input) {
              $crate::IResult::Done(iparse, oparse) => {
                res.push(oparse);
                input = iparse;
              },
              $crate::IResult::Error(_)      => {
                ret = $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::LengthValue,$i)); break;
              },
              $crate::IResult::Incomplete(a) => {
                ret = match a {
                  $crate::Needed::Unknown => $crate::IResult::Incomplete($crate::Needed::Unknown),
                  $crate::Needed::Size(_) => $crate::IResult::Incomplete($crate::Needed::Size(length_token + onum as usize * $length))
                };
                break;
              }
            }
          }

          ret
        }
      }
    }
  );
);

/// `fold_many0!(I -> IResult<I,O>, R, Fn(R, O) -> R) => I -> IResult<I, R>`
/// Applies the parser 0 or more times and folds the list of return values
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >, fold_many0!( tag!( "abcd" ), Vec::new(), |mut acc: Vec<_>, item| {
///      acc.push(item);
///      acc
///  }));
///
///  let a = b"abcdabcdefgh";
///  let b = b"azerty";
///
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&a[..]), Done(&b"efgh"[..], res));
///  assert_eq!(multi(&b[..]), Done(&b"azerty"[..], Vec::new()));
/// # }
/// ```
/// 0 or more
#[macro_export]
macro_rules! fold_many0(
  ($i:expr, $submac:ident!( $($args:tt)* ), $init:expr, $f:expr) => (
    {
      use $crate::InputLength;
      let ret;
      let f         = $f;
      let mut res   = $init;
      let mut input = $i;

      loop {
        if input.input_len() == 0 {
          ret = $crate::IResult::Done(input, res); break;
        }

        match $submac!(input, $($args)*) {
          $crate::IResult::Error(_)                            => {
            ret = $crate::IResult::Done(input, res); break;
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown) => {
            ret = $crate::IResult::Incomplete($crate::Needed::Unknown); break;
          },
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
            let size = i + ($i).input_len() - input.input_len();
            ret = $crate::IResult::Incomplete($crate::Needed::Size(size)); break;
          },
          $crate::IResult::Done(i, o)                          => {
            // loop trip must always consume (otherwise infinite loops)
            if i == input {
              ret = $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Many0,input)); break;
            }

            res = f(res, o);
            input = i;
          }
        }
      }

      ret
    }
  );
  ($i:expr, $f:expr, $init:expr, $fold_f:expr) => (
    fold_many0!($i, call!($f), $init, $fold_f);
  );
);

/// `fold_many1!(I -> IResult<I,O>, R, Fn(R, O) -> R) => I -> IResult<I, R>`
/// Applies the parser 1 or more times and folds the list of return values
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >, fold_many1!( tag!( "abcd" ), Vec::new(), |mut acc: Vec<_>, item| {
///      acc.push(item);
///      acc
///  }));
///
///  let a = b"abcdabcdefgh";
///  let b = b"azerty";
///
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&a[..]), Done(&b"efgh"[..], res));
///  assert_eq!(multi(&b[..]), Error(Position(ErrorKind::Many1,&b[..])));
/// # }
/// ```
#[macro_export]
macro_rules! fold_many1(
  ($i:expr, $submac:ident!( $($args:tt)* ), $init:expr, $f:expr) => (
    {
      use $crate::InputLength;
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(_)      => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Many1,$i)),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,o1)   => {
          let acc = $init;
          let f = $f;
          if i1.len() == 0 {
            let acc = f(acc, o1);
            $crate::IResult::Done(i1,acc)
          } else {
            let mut acc = f(acc, o1);
            let mut input  = i1;
            let mut incomplete: ::std::option::Option<$crate::Needed> = ::std::option::Option::None;
            loop {
              if input.input_len() == 0 {
                break;
              }
              match $submac!(input, $($args)*) {
                $crate::IResult::Error(_)                    => {
                  break;
                },
                $crate::IResult::Incomplete($crate::Needed::Unknown) => {
                  incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
                  break;
                },
                $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
                  incomplete = ::std::option::Option::Some($crate::Needed::Size(i + ($i).input_len() - input.input_len()));
                  break;
                },
                $crate::IResult::Done(i, o) => {
                  if i.input_len() == input.input_len() {
                    break;
                  }
                  acc = f(acc, o);
                  input = i;
                }
              }
            }

            match incomplete {
              ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
              ::std::option::Option::None    => $crate::IResult::Done(input, acc)
            }
          }
        }
      }
    }
  );
  ($i:expr, $f:expr, $init:expr, $fold_f:expr) => (
    fold_many1!($i, call!($f), $init, $fold_f);
  );
);

/// `fold_many_m_n!(usize, usize, I -> IResult<I,O>, R, Fn(R, O) -> R) => I -> IResult<I, R>`
/// Applies the parser between m and n times (n included) and folds the list of return value
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >, fold_many_m_n!(2, 4, tag!( "abcd" ), Vec::new(), |mut acc: Vec<_>, item| {
///      acc.push(item);
///      acc
///  }));
///
///  let a = b"abcdefgh";
///  let b = b"abcdabcdefgh";
///  let c = b"abcdabcdabcdabcdabcdefgh";
///
///  assert_eq!(multi(&a[..]),Error(Position(ErrorKind::ManyMN,&a[..])));
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&b[..]), Done(&b"efgh"[..], res));
///  let res2 = vec![&b"abcd"[..], &b"abcd"[..], &b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&c[..]), Done(&b"abcdefgh"[..], res2));
/// # }
/// ```
#[macro_export]
macro_rules! fold_many_m_n(
  ($i:expr, $m:expr, $n: expr, $submac:ident!( $($args:tt)* ), $init:expr, $f:expr) => (
    {
      use $crate::InputLength;
      let mut acc          = $init;
      let     f            = $f;
      let mut input        = $i;
      let mut count: usize = 0;
      let mut err          = false;
      let mut incomplete: ::std::option::Option<$crate::Needed> = ::std::option::Option::None;
      loop {
        if count == $n { break }
        match $submac!(input, $($args)*) {
          $crate::IResult::Done(i, o) => {
            // do not allow parsers that do not consume input (causes infinite loops)
            if i.input_len() == input.input_len() {
              break;
            }
            acc = f(acc, o);
            input  = i;
            count += 1;
          }
          $crate::IResult::Error(_)                    => {
            err = true;
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown) => {
            incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
            incomplete = ::std::option::Option::Some($crate::Needed::Size(i + ($i).input_len() - input.input_len()));
            break;
          },
        }
        if input.input_len() == 0 {
          break;
        }
      }

      if count < $m {
        if err {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::ManyMN,$i))
        } else {
          match incomplete {
            ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
            ::std::option::Option::None    => $crate::IResult::Incomplete($crate::Needed::Unknown)
          }
        }
      } else {
        match incomplete {
          ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
          ::std::option::Option::None    => $crate::IResult::Done(input, acc)
        }
      }
    }
  );
  ($i:expr, $m:expr, $n: expr, $f:expr, $init:expr, $fold_f:expr) => (
    fold_many_m_n!($i, $m, $n, call!($f), $init, $fold_f);
  );
);

#[cfg(test)]
mod tests {
  use internal::{Needed,IResult,Err};
  use internal::IResult::*;
  use internal::Err::*;
  use util::ErrorKind;

  // reproduce the tag and take macros, because of module import order
  macro_rules! tag (
    ($i:expr, $inp: expr) => (
      {
        #[inline(always)]
        fn as_bytes<T: $crate::AsBytes>(b: &T) -> &[u8] {
          b.as_bytes()
        }

        let expected = $inp;
        let bytes    = as_bytes(&expected);

        tag_bytes!($i,bytes)
      }
    );
  );

  macro_rules! tag_bytes (
    ($i:expr, $bytes: expr) => (
      {
        use std::cmp::min;
        let len = $i.len();
        let blen = $bytes.len();
        let m   = min(len, blen);
        let reduced = &$i[..m];
        let b       = &$bytes[..m];

        let res: $crate::IResult<_,_> = if reduced != b {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Tag, $i))
        } else if m < blen {
          $crate::IResult::Incomplete($crate::Needed::Size(blen))
        } else {
          $crate::IResult::Done(&$i[blen..], reduced)
        };
        res
      }
    );
  );

  macro_rules! take(
    ($i:expr, $count:expr) => (
      {
        let cnt = $count as usize;
        let res:$crate::IResult<&[u8],&[u8]> = if $i.len() < cnt {
          $crate::IResult::Incomplete($crate::Needed::Size(cnt))
        } else {
          $crate::IResult::Done(&$i[cnt..],&$i[0..cnt])
        };
        res
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

    named!(chain_parser<&[u8],B>,
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

    assert_eq!(chain_parser(&b"abcdabcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(chain_parser(&b"abcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(chain_parser(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(chain_parser(&b"abcdefghef"[..]), Incomplete(Needed::Size(12)));
  }

  #[test]
  fn nested_chain() {
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };

    named!(chain_parser<&[u8],B>,
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

    assert_eq!(chain_parser(&b"abcdabcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(chain_parser(&b"abcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(chain_parser(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(chain_parser(&b"abcdefghef"[..]), Incomplete(Needed::Size(12)));
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

    named!(chain_parser<&[u8],C>,
      chain!(
        tag!("abcd") ~
        aa: ret_int1 ~
        bb: ret_y?   ,
        ||{C{a: aa, b: bb}}
      )
    );

    assert_eq!(chain_parser(&b"abcdefghX"[..]), Done(&b"X"[..], C{a: 1, b: Some(2)}));
    assert_eq!(chain_parser(&b"abcdWXYZ"[..]), Done(&b"WXYZ"[..], C{a: 1, b: None}));
    assert_eq!(chain_parser(&b"abcdX"[..]), Done(&b"X"[..], C{ a: 1, b: None }));
    assert_eq!(chain_parser(&b"abcdef"[..]), Incomplete(Needed::Size(8)));
  }

  use util::{error_to_list, add_error_pattern, print_error};

  fn error_to_string<P>(e: &Err<P>) -> &'static str {
    let v:Vec<ErrorKind> = error_to_list(e);
    // do it this way if you can use slice patterns
    /*
    match &v[..] {
      [ErrorKind::Custom(42), ErrorKind::Tag]                         => "missing `ijkl` tag",
      [ErrorKind::Custom(42), ErrorKind::Custom(128), ErrorKind::Tag] => "missing `mnop` tag after `ijkl`",
      _            => "unrecognized error"
    }
    */
    if &v[..] == [ErrorKind::Custom(42),ErrorKind::Tag] {
      "missing `ijkl` tag"
    } else if &v[..] == [ErrorKind::Custom(42), ErrorKind::Custom(128), ErrorKind::Tag] {
      "missing `mnop` tag after `ijkl`"
    } else {
      "unrecognized error"
    }
  }

  // do it this way if you can use box patterns
  /*use std::str;
  fn error_to_string(e:Err) -> String
    match e {
      NodePosition(ErrorKind::Custom(42), i1, box Position(ErrorKind::Tag, i2)) => {
        format!("missing `ijkl` tag, found '{}' instead", str::from_utf8(i2).unwrap())
      },
      NodePosition(ErrorKind::Custom(42), i1, box NodePosition(ErrorKind::Custom(128), i2,  box Position(ErrorKind::Tag, i3))) => {
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
      preceded!(tag!("efgh"), error!(ErrorKind::Custom(42),
          chain!(
                 tag!("ijkl")              ~
            res: error!(ErrorKind::Custom(128), tag!("mnop")) ,
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
    assert_eq!(res_a, Error(NodePosition(ErrorKind::Custom(42), blah, Box::new(Position(ErrorKind::Tag, blah)))));
    assert_eq!(res_b, Error(NodePosition(ErrorKind::Custom(42), &b"ijklblah"[..], Box::new(NodePosition(ErrorKind::Custom(128), blah, Box::new(Position(ErrorKind::Tag, blah)))))));
    assert_eq!(res_c, Done(&b""[..], &b"mnop"[..]));

    // Merr-like error matching
    let mut err_map = collections::HashMap::new();
    assert!(add_error_pattern(&mut err_map, err_test(&b"efghpouet"[..]), "missing `ijkl` tag"));
    assert!(add_error_pattern(&mut err_map, err_test(&b"efghijklpouet"[..]), "missing `mnop` tag after `ijkl`"));

    let res_a2 = res_a.clone();
    match res_a {
      Error(e) => {
        assert_eq!(error_to_list(&e), [ErrorKind::Custom(42), ErrorKind::Tag]);
        assert_eq!(error_to_string(&e), "missing `ijkl` tag");
        assert_eq!(err_map.get(&error_to_list(&e)), Some(&"missing `ijkl` tag"));
      },
      _ => panic!()
    };

    let res_b2 = res_b.clone();
    match res_b {
      Error(e) => {
        assert_eq!(error_to_list(&e), [ErrorKind::Custom(42), ErrorKind::Custom(128), ErrorKind::Tag]);
        assert_eq!(error_to_string(&e), "missing `mnop` tag after `ijkl`");
        assert_eq!(err_map.get(&error_to_list(&e)), Some(&"missing `mnop` tag after `ijkl`"));
      },
      _ => panic!()
    };

    print_error(a, res_a2);
    print_error(b, res_b2);
  }

  #[test]
  fn add_err() {
    named!(err_test,
      preceded!(tag!("efgh"), add_error!(ErrorKind::Custom(42),
          chain!(
                 tag!("ijkl")              ~
            res: add_error!(ErrorKind::Custom(128), tag!("mnop")) ,
            || { res }
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
    assert_eq!(res_a, Error(NodePosition(ErrorKind::Custom(42), blah, Box::new(Position(ErrorKind::Tag, blah)))));
    assert_eq!(res_b, Error(NodePosition(ErrorKind::Custom(42), &b"ijklblah"[..], Box::new(NodePosition(ErrorKind::Custom(128), blah, Box::new(Position(ErrorKind::Tag, blah)))))));
    assert_eq!(res_c, Done(&b""[..], &b"mnop"[..]));
  }

  #[test]
  fn complete() {
    named!(err_test,
      chain!(
             tag!("ijkl")              ~
        res: complete!(tag!("mnop")) ,
        || { res }
      )
    );
    let a = &b"ijklmn"[..];

    let res_a = err_test(a);
    assert_eq!(res_a, Error(Position(ErrorKind::Complete, &b"mn"[..])));
  }
  #[test]
  fn alt() {
    fn work(input: &[u8]) -> IResult<&[u8],&[u8], &'static str> {
      Done(&b""[..], input)
    }

    #[allow(unused_variables)]
    fn dont_work(input: &[u8]) -> IResult<&[u8],&[u8],&'static str> {
      Error(Code(ErrorKind::Custom("abcd")))
    }

    fn work2(input: &[u8]) -> IResult<&[u8],&[u8], &'static str> {
      Done(input, &b""[..])
    }

    fn alt1(i:&[u8]) ->  IResult<&[u8],&[u8], &'static str> {
      alt!(i, dont_work | dont_work)
    }
    fn alt2(i:&[u8]) ->  IResult<&[u8],&[u8], &'static str> {
      alt!(i, dont_work | work)
    }
    fn alt3(i:&[u8]) ->  IResult<&[u8],&[u8], &'static str> {
      alt!(i, dont_work | dont_work | work2 | dont_work)
    }
    //named!(alt1, alt!(dont_work | dont_work));
    //named!(alt2, alt!(dont_work | work));
    //named!(alt3, alt!(dont_work | dont_work | work2 | dont_work));

    let a = &b"abcd"[..];
    assert_eq!(alt1(a), Error(Position(ErrorKind::Alt, a)));
    assert_eq!(alt2(a), Done(&b""[..], a));
    assert_eq!(alt3(a), Done(a, &b""[..]));

    named!(alt4, alt!(tag!("abcd") | tag!("efgh")));
    let b = &b"efgh"[..];
    assert_eq!(alt4(a), Done(&b""[..], a));
    assert_eq!(alt4(b), Done(&b""[..], b));

    // test the alternative syntax
    named!(alt5<bool>, alt!(tag!("abcd") => { |_| false } | tag!("efgh") => { |_| true }));
    assert_eq!(alt5(a), Done(&b""[..], false));
    assert_eq!(alt5(b), Done(&b""[..], true));

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
    assert_eq!(alt1(a), Error(Position(ErrorKind::Alt, a)));
    let a = &b"de"[..];
    assert_eq!(alt1(a), Incomplete(Needed::Size(3)));
    let a = &b"defg"[..];
    assert_eq!(alt1(a), Done(&b"g"[..], &b"def"[..]));
  }

  #[test]
  fn alt_complete() {
    named!(ac<&[u8], &[u8]>,
      alt_complete!(tag!("abcd") | tag!("ef") | tag!("ghi") | tag!("kl"))
    );

    let a = &b""[..];
    assert_eq!(ac(a), Incomplete(Needed::Size(2)));
    let a = &b"ef"[..];
    assert_eq!(ac(a), Done(&b""[..], &b"ef"[..]));
    let a = &b"cde"[..];
    assert_eq!(ac(a), Error(Position(ErrorKind::Alt, a)));
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
    assert_eq!(sw(c), Error(Position(ErrorKind::Switch, &b"afghijkl"[..])));
  }

  #[test]
  fn opt() {
    named!(opt_abcd<&[u8],Option<&[u8]> >, opt!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    let c = &b"ab"[..];
    assert_eq!(opt_abcd(a), Done(&b"ef"[..], Some(&b"abcd"[..])));
    assert_eq!(opt_abcd(b), Done(&b"bcdefg"[..], None));
    assert_eq!(opt_abcd(c), Incomplete(Needed::Size(4)));
  }

  #[test]
  fn opt_res() {
    named!(opt_res_abcd<&[u8], Result<&[u8], Err<&[u8]>> >, opt_res!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    let c = &b"ab"[..];
    assert_eq!(opt_res_abcd(a), Done(&b"ef"[..], Ok(&b"abcd"[..])));
    assert_eq!(opt_res_abcd(b), Done(&b"bcdefg"[..], Err(Position(ErrorKind::Tag, b))));
    assert_eq!(opt_res_abcd(c), Incomplete(Needed::Size(4)));
  }

  #[test]
  fn cond() {
    let f_true: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> = Box::new(closure!(&'static [u8], cond!( true, tag!("abcd") ) ));
    let f_false: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> = Box::new(closure!(&'static [u8], cond!( false, tag!("abcd") ) ));
    //let f_false = closure!(&'static [u8], cond!( false, tag!("abcd") ) );

    assert_eq!(f_true(&b"abcdef"[..]), Done(&b"ef"[..], Some(&b"abcd"[..])));
    assert_eq!(f_true(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(f_true(&b"xxx"[..]), Done(&b"xxx"[..], None));

    assert_eq!(f_false(&b"abcdef"[..]), Done(&b"abcdef"[..], None));
    assert_eq!(f_false(&b"ab"[..]), Done(&b"ab"[..], None));
    assert_eq!(f_false(&b"xxx"[..]), Done(&b"xxx"[..], None));
  }

  #[test]
  fn cond_wrapping() {
    // Test that cond!() will wrap a given identifier in the call!() macro.
    named!( tag_abcd, tag!("abcd") );
    let f_true: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> = Box::new(closure!(&'static [u8], cond!( true, tag_abcd ) ));
    let f_false: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> = Box::new(closure!(&'static [u8], cond!( false, tag_abcd ) ));
    //let f_false = closure!(&'static [u8], cond!( b2, tag!("abcd") ) );

    assert_eq!(f_true(&b"abcdef"[..]), Done(&b"ef"[..], Some(&b"abcd"[..])));
    assert_eq!(f_true(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(f_true(&b"xxx"[..]), Done(&b"xxx"[..], None));

    assert_eq!(f_false(&b"abcdef"[..]), Done(&b"abcdef"[..], None));
    assert_eq!(f_false(&b"ab"[..]), Done(&b"ab"[..], None));
    assert_eq!(f_false(&b"xxx"[..]), Done(&b"xxx"[..], None));
  }

  #[test]
  fn peek() {
    named!(peek_tag<&[u8],&[u8]>, peek!(tag!("abcd")));

    assert_eq!(peek_tag(&b"abcdef"[..]), Done(&b"abcdef"[..], &b"abcd"[..]));
    assert_eq!(peek_tag(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(peek_tag(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn pair() {
    named!( tag_abc, tag!("abc") );
    named!( tag_def, tag!("def") );
    named!( pair_abc_def<&[u8],(&[u8], &[u8])>, pair!(tag_abc, tag_def) );

    assert_eq!(pair_abc_def(&b"abcdefghijkl"[..]), Done(&b"ghijkl"[..], (&b"abc"[..], &b"def"[..])));
    assert_eq!(pair_abc_def(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(pair_abc_def(&b"abcd"[..]), Incomplete(Needed::Size(6)));
    assert_eq!(pair_abc_def(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(pair_abc_def(&b"xxxdef"[..]), Error(Position(ErrorKind::Tag, &b"xxxdef"[..])));
    assert_eq!(pair_abc_def(&b"abcxxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn separated_pair() {
    named!( tag_abc, tag!("abc") );
    named!( tag_def, tag!("def") );
    named!( tag_separator, tag!(",") );
    named!( sep_pair_abc_def<&[u8],(&[u8], &[u8])>, separated_pair!(tag_abc, tag_separator, tag_def) );

    assert_eq!(sep_pair_abc_def(&b"abc,defghijkl"[..]), Done(&b"ghijkl"[..], (&b"abc"[..], &b"def"[..])));
    assert_eq!(sep_pair_abc_def(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(sep_pair_abc_def(&b"abc,d"[..]), Incomplete(Needed::Size(7)));
    assert_eq!(sep_pair_abc_def(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(sep_pair_abc_def(&b"xxx,def"[..]), Error(Position(ErrorKind::Tag, &b"xxx,def"[..])));
    assert_eq!(sep_pair_abc_def(&b"abc,xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn preceded() {
    named!( tag_abcd, tag!("abcd") );
    named!( tag_efgh, tag!("efgh") );
    named!( preceded_abcd_efgh<&[u8], &[u8]>, preceded!(tag_abcd, tag_efgh) );

    assert_eq!(preceded_abcd_efgh(&b"abcdefghijkl"[..]), Done(&b"ijkl"[..], &b"efgh"[..]));
    assert_eq!(preceded_abcd_efgh(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(preceded_abcd_efgh(&b"abcde"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(preceded_abcd_efgh(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(preceded_abcd_efgh(&b"xxxxdef"[..]), Error(Position(ErrorKind::Tag, &b"xxxxdef"[..])));
    assert_eq!(preceded_abcd_efgh(&b"abcdxxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn terminated() {
    named!( tag_abcd, tag!("abcd") );
    named!( tag_efgh, tag!("efgh") );
    named!( terminated_abcd_efgh<&[u8], &[u8]>, terminated!(tag_abcd, tag_efgh) );

    assert_eq!(terminated_abcd_efgh(&b"abcdefghijkl"[..]), Done(&b"ijkl"[..], &b"abcd"[..]));
    assert_eq!(terminated_abcd_efgh(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(terminated_abcd_efgh(&b"abcde"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(terminated_abcd_efgh(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(terminated_abcd_efgh(&b"xxxxdef"[..]), Error(Position(ErrorKind::Tag, &b"xxxxdef"[..])));
    assert_eq!(terminated_abcd_efgh(&b"abcdxxxx"[..]), Error(Position(ErrorKind::Tag, &b"xxxx"[..])));
  }

  #[test]
  fn delimited() {
    named!( tag_abc, tag!("abc") );
    named!( tag_def, tag!("def") );
    named!( tag_ghi, tag!("ghi") );
    named!( delimited_abc_def_ghi<&[u8], &[u8]>, delimited!(tag_abc, tag_def, tag_ghi) );

    assert_eq!(delimited_abc_def_ghi(&b"abcdefghijkl"[..]), Done(&b"jkl"[..], &b"def"[..]));
    assert_eq!(delimited_abc_def_ghi(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(delimited_abc_def_ghi(&b"abcde"[..]), Incomplete(Needed::Size(6)));
    assert_eq!(delimited_abc_def_ghi(&b"abcdefgh"[..]), Incomplete(Needed::Size(9)));
    assert_eq!(delimited_abc_def_ghi(&b"xxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(delimited_abc_def_ghi(&b"xxxdefghi"[..]), Error(Position(ErrorKind::Tag, &b"xxxdefghi"[..])));
    assert_eq!(delimited_abc_def_ghi(&b"abcxxxghi"[..]), Error(Position(ErrorKind::Tag, &b"xxxghi"[..])));
    assert_eq!(delimited_abc_def_ghi(&b"abcdefxxx"[..]), Error(Position(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn separated_list() {
    named!(multi<&[u8],Vec<&[u8]> >, separated_list!(tag!(","), tag!("abcd")));
    named!(multi_empty<&[u8],Vec<&[u8]> >, separated_list!(tag!(","), tag!("")));

    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"azerty"[..];
    let d = &b",,abc"[..];
    let e = &b"abcd,abcd,ef"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"ef"[..], res2));
    assert_eq!(multi(c), Done(&b"azerty"[..], Vec::new()));
    assert_eq!(multi_empty(d), Error(Position(ErrorKind::SeparatedList, d)));
    //let res3 = vec![&b""[..], &b""[..], &b""[..]];
    //assert_eq!(multi_empty(d), Done(&b"abc"[..], res3));
    let res4 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(e), Done(&b",ef"[..], res4));
  }

  #[test]
  fn separated_nonempty_list() {
    named!(multi<&[u8],Vec<&[u8]> >, separated_nonempty_list!(tag!(","), tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"azerty"[..];
    let d = &b"abcd,abcd,ef"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"ef"[..], res2));
    assert_eq!(multi(c), Error(Position(ErrorKind::Tag,c)));
    let res3 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(d), Done(&b",ef"[..], res3));
  }

  #[test]
  fn many0() {
    named!( tag_abcd, tag!("abcd") );
    named!( tag_empty, tag!("") );
    named!( multi<&[u8],Vec<&[u8]> >, many0!(tag_abcd) );
    named!( multi_empty<&[u8],Vec<&[u8]> >, many0!(tag_empty) );

    assert_eq!(multi(&b"abcdef"[..]), Done(&b"ef"[..], vec![&b"abcd"[..]]));
    assert_eq!(multi(&b"abcdabcdefgh"[..]), Done(&b"efgh"[..], vec![&b"abcd"[..], &b"abcd"[..]]));
    assert_eq!(multi(&b"azerty"[..]), Done(&b"azerty"[..], Vec::new()));
    assert_eq!(multi(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(multi(&b"abcd"[..]), Done(&b""[..], vec![&b"abcd"[..]]));
    assert_eq!(multi(&b""[..]), Done(&b""[..], Vec::new()));
    assert_eq!(multi_empty(&b"abcdef"[..]), Error(Position(ErrorKind::Many0, &b"abcdef"[..])));
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
    let b = &b"abcdabcdefgh"[..];
    let c = &b"azerty"[..];
    let d = &b"abcdab"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res2));
    assert_eq!(multi(c), Error(Position(ErrorKind::Many1,c)));
    assert_eq!(multi(d), Incomplete(Needed::Size(8)));
  }

  #[test]
  fn infinite_many() {
    fn tst(input: &[u8]) -> IResult<&[u8], &[u8]> {
      println!("input: {:?}", input);
      Error(Position(ErrorKind::Custom(0),input))
    }

    // should not go into an infinite loop
    named!(multi0<&[u8],Vec<&[u8]> >, many0!(tst));
    let a = &b"abcdef"[..];
    assert_eq!(multi0(a), Done(a, Vec::new()));

    named!(multi1<&[u8],Vec<&[u8]> >, many1!(tst));
    let a = &b"abcdef"[..];
    assert_eq!(multi1(a), Error(Position(ErrorKind::Many1,a)));
  }

  #[test]
  fn many_m_n() {
    named!(multi<&[u8],Vec<&[u8]> >, many_m_n!(2, 4, tag!("Abcd")));

    let a = &b"Abcdef"[..];
    let b = &b"AbcdAbcdefgh"[..];
    let c = &b"AbcdAbcdAbcdAbcdefgh"[..];
    let d = &b"AbcdAbcdAbcdAbcdAbcdefgh"[..];
    let e = &b"AbcdAb"[..];

    assert_eq!(multi(a), Error(Err::Position(ErrorKind::ManyMN,a)));
    let res1 = vec![&b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res1));
    let res2 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(c), Done(&b"efgh"[..], res2));
    let res3 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(d), Done(&b"Abcdefgh"[..], res3));
    assert_eq!(multi(e), Incomplete(Needed::Size(8)));
  }

  #[test]
  fn count() {
    const TIMES: usize = 2;
    named!( tag_abc, tag!("abc") );
    named!( cnt_2<&[u8], Vec<&[u8]> >, count!(tag_abc, TIMES ) );

    assert_eq!(cnt_2(&b"abcabcabcdef"[..]), Done(&b"abcdef"[..], vec![&b"abc"[..], &b"abc"[..]]));
    assert_eq!(cnt_2(&b"ab"[..]), Incomplete(Needed::Unknown));
    assert_eq!(cnt_2(&b"abcab"[..]), Incomplete(Needed::Unknown));
    assert_eq!(cnt_2(&b"xxx"[..]), Error(Position(ErrorKind::Count, &b"xxx"[..])));
    assert_eq!(cnt_2(&b"xxxabcabcdef"[..]), Error(Position(ErrorKind::Count, &b"xxxabcabcdef"[..])));
    assert_eq!(cnt_2(&b"abcxxxabcdef"[..]), Error(Position(ErrorKind::Count, &b"abcxxxabcdef"[..])));
  }

  #[test]
  fn count_zero() {
    const TIMES: usize = 0;
    named!( tag_abc, tag!("abc") );
    named!( counter_2<&[u8], Vec<&[u8]> >, count!(tag_abc, TIMES ) );

    let done = &b"abcabcabcdef"[..];
    let parsed_done = Vec::new();
    let rest = done;
    let incomplete_1 = &b"ab"[..];
    let parsed_incompl_1 = Vec::new();
    let incomplete_2 = &b"abcab"[..];
    let parsed_incompl_2 = Vec::new();
    let error = &b"xxx"[..];
    let error_remain = &b"xxx"[..];
    let parsed_err = Vec::new();
    let error_1 = &b"xxxabcabcdef"[..];
    let parsed_err_1 = Vec::new();
    let error_1_remain = &b"xxxabcabcdef"[..];
    let error_2 = &b"abcxxxabcdef"[..];
    let parsed_err_2 = Vec::new();
    let error_2_remain = &b"abcxxxabcdef"[..];

    assert_eq!(counter_2(done), Done(rest, parsed_done));
    assert_eq!(counter_2(incomplete_1), Done(incomplete_1, parsed_incompl_1));
    assert_eq!(counter_2(incomplete_2), Done(incomplete_2, parsed_incompl_2));
    assert_eq!(counter_2(error), Done(error_remain, parsed_err));
    assert_eq!(counter_2(error_1), Done(error_1_remain, parsed_err_1));
    assert_eq!(counter_2(error_2), Done(error_2_remain, parsed_err_2));
  }

  #[test]
  fn count_fixed() {
    const TIMES: usize = 2;
    named!( tag_abc, tag!("abc") );
    named!( cnt_2<&[u8], [&[u8]; TIMES] >, count_fixed!(&[u8], tag_abc, TIMES ) );

    assert_eq!(cnt_2(&b"abcabcabcdef"[..]), Done(&b"abcdef"[..], [&b"abc"[..], &b"abc"[..]]));
    assert_eq!(cnt_2(&b"ab"[..]), Incomplete(Needed::Unknown));
    assert_eq!(cnt_2(&b"abcab"[..]), Incomplete(Needed::Unknown));
    assert_eq!(cnt_2(&b"xxx"[..]), Error(Position(ErrorKind::Count, &b"xxx"[..])));
    assert_eq!(cnt_2(&b"xxxabcabcdef"[..]), Error(Position(ErrorKind::Count, &b"xxxabcabcdef"[..])));
    assert_eq!(cnt_2(&b"abcxxxabcdef"[..]), Error(Position(ErrorKind::Count, &b"abcxxxabcdef"[..])));
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
    const TIMES: usize = 2;
    named!( tag_abc, tag!("abc") );
    named!( counter_2<&[u8], [&[u8]; TIMES], () >, count_fixed!(&[u8], tag_abc, TIMES ) );

    let done = &b"abcabcabcdef"[..];
    let parsed_main = [&b"abc"[..], &b"abc"[..]];
    let rest = &b"abcdef"[..];
    let incomplete_1 = &b"ab"[..];
    let incomplete_2 = &b"abcab"[..];
    let error = &b"xxx"[..];
    let error_1 = &b"xxxabcabcdef"[..];
    let error_1_remain = &b"xxxabcabcdef"[..];
    let error_2 = &b"abcxxxabcdef"[..];
    let error_2_remain = &b"abcxxxabcdef"[..];

    assert_eq!(counter_2(done), Done(rest, parsed_main));
    assert_eq!(counter_2(incomplete_1), Incomplete(Needed::Unknown));
    assert_eq!(counter_2(incomplete_2), Incomplete(Needed::Unknown));
    assert_eq!(counter_2(error), Error(Position(ErrorKind::Count, error)));
    assert_eq!(counter_2(error_1), Error(Position(ErrorKind::Count, error_1_remain)));
    assert_eq!(counter_2(error_2), Error(Position(ErrorKind::Count, error_2_remain)));
  }

  use nom::{be_u8,be_u16};
  #[test]
  fn length_value_test() {
    named!(length_value_1<&[u8], Vec<u16> >, length_value!(be_u8, be_u16));
    named!(length_value_2<&[u8], Vec<u16> >, length_value!(be_u8, be_u16, 2));

    let i1 = vec![0, 5, 6];
    assert_eq!(length_value_1(&i1), IResult::Done(&i1[1..], vec![]));
    assert_eq!(length_value_2(&i1), IResult::Done(&i1[1..], vec![]));

    let i2 = vec![1, 5, 6, 3];
    assert_eq!(length_value_1(&i2), IResult::Done(&i2[3..], vec![1286]));
    assert_eq!(length_value_2(&i2), IResult::Done(&i2[3..], vec![1286]));

    let i3 = vec![2, 5, 6, 3, 4, 5, 7];
    assert_eq!(length_value_1(&i3), IResult::Done(&i3[5..], vec![1286, 772]));
    assert_eq!(length_value_2(&i3), IResult::Done(&i3[5..], vec![1286, 772]));

    let i4 = vec![2, 5, 6, 3];
    assert_eq!(length_value_1(&i4), IResult::Incomplete(Needed::Size(5)));
    assert_eq!(length_value_2(&i4), IResult::Incomplete(Needed::Size(5)));

    let i5 = vec![3, 5, 6, 3, 4, 5];
    assert_eq!(length_value_1(&i5), IResult::Incomplete(Needed::Size(7)));
    assert_eq!(length_value_2(&i5), IResult::Incomplete(Needed::Size(7)));
  }

  #[test]
  fn fold_many0() {
    fn fold_into_vec<T>(mut acc: Vec<T>, item: T) -> Vec<T> {
      acc.push(item);
      acc
    };
    named!( tag_abcd, tag!("abcd") );
    named!( tag_empty, tag!("") );
    named!( multi<&[u8],Vec<&[u8]> >, fold_many0!(tag_abcd, Vec::new(), fold_into_vec) );
    named!( multi_empty<&[u8],Vec<&[u8]> >, fold_many0!(tag_empty, Vec::new(), fold_into_vec) );

    assert_eq!(multi(&b"abcdef"[..]), Done(&b"ef"[..], vec![&b"abcd"[..]]));
    assert_eq!(multi(&b"abcdabcdefgh"[..]), Done(&b"efgh"[..], vec![&b"abcd"[..], &b"abcd"[..]]));
    assert_eq!(multi(&b"azerty"[..]), Done(&b"azerty"[..], Vec::new()));
    assert_eq!(multi(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(multi(&b"abcd"[..]), Done(&b""[..], vec![&b"abcd"[..]]));
    assert_eq!(multi(&b""[..]), Done(&b""[..], Vec::new()));
    assert_eq!(multi_empty(&b"abcdef"[..]), Error(Position(ErrorKind::Many0, &b"abcdef"[..])));
  }

  #[test]
  fn fold_many1() {
    fn fold_into_vec<T>(mut acc: Vec<T>, item: T) -> Vec<T> {
      acc.push(item);
      acc
    };
    named!(multi<&[u8],Vec<&[u8]> >, fold_many1!(tag!("abcd"), Vec::new(), fold_into_vec));

    let a = &b"abcdef"[..];
    let b = &b"abcdabcdefgh"[..];
    let c = &b"azerty"[..];
    let d = &b"abcdab"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res2));
    assert_eq!(multi(c), Error(Position(ErrorKind::Many1,c)));
    assert_eq!(multi(d), Incomplete(Needed::Size(8)));
  }

  #[test]
  fn fold_many_m_n() {
    fn fold_into_vec<T>(mut acc: Vec<T>, item: T) -> Vec<T> {
      acc.push(item);
      acc
    };
    named!(multi<&[u8],Vec<&[u8]> >, fold_many_m_n!(2, 4, tag!("Abcd"), Vec::new(), fold_into_vec));

    let a = &b"Abcdef"[..];
    let b = &b"AbcdAbcdefgh"[..];
    let c = &b"AbcdAbcdAbcdAbcdefgh"[..];
    let d = &b"AbcdAbcdAbcdAbcdAbcdefgh"[..];
    let e = &b"AbcdAb"[..];

    assert_eq!(multi(a), Error(Err::Position(ErrorKind::ManyMN,a)));
    let res1 = vec![&b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res1));
    let res2 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(c), Done(&b"efgh"[..], res2));
    let res3 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(d), Done(&b"Abcdefgh"[..], res3));
    assert_eq!(multi(e), Incomplete(Needed::Size(8)));
  }

  #[test]
  fn chain_incomplete() {
    let res = chain!(&b"abcdefgh"[..],
      a: take!(4) ~
      b: take!(8),
      ||{(a,b )}
    );

    assert_eq!(res, IResult::Incomplete(Needed::Size(12)));
  }

  #[test]
  fn tuple_test() {
    named!(tuple_3<&[u8], (u16, &[u8], &[u8]) >,
    tuple!( be_u16 , take!(3), tag!("fg") ) );

    assert_eq!(tuple_3(&b"abcdefgh"[..]), Done(&b"h"[..], (0x6162u16, &b"cde"[..], &b"fg"[..])));
    assert_eq!(tuple_3(&b"abcd"[..]), Incomplete(Needed::Size(5)));
    assert_eq!(tuple_3(&b"abcde"[..]), Incomplete(Needed::Size(7)));
    assert_eq!(tuple_3(&b"abcdejk"[..]), Error(Position(ErrorKind::Tag, &b"jk"[..])));
  }
  
  #[test]
  fn not() {
    named!(not_aaa, not!(tag!("aaa")));
    assert_eq!(not_aaa(&b"aaa"[..]), Error(Position(ErrorKind::Not, &b"aaa"[..])));
    assert_eq!(not_aaa(&b"aa"[..]), Done(&b"aa"[..], &b""[..]));
    assert_eq!(not_aaa(&b"abcd"[..]), Done(&b"abcd"[..], &b""[..]));
  }
}
