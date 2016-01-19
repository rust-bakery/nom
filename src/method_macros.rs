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
//!   ($input:expr, $obj:ident.$method:ident) => (
//!     take_while!($input, call_m!($obj.$method));
//!   );
//! );
//!

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
macro_rules! method (
    ($name:ident<$a:ty>( $i:ty ) -> $o:ty, $object:ident, $submac:ident!( $($args:tt)* )) => (
        fn $name<'nom>( $object: $a, i: $i ) -> $crate::IResult<$i,$o> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$a:ty,$i:ty,$o:ty>, $object:ident, $submac:ident!( $($args:tt)* )) => (
        fn $name<'nom>( $object: $a, i: $i ) -> $crate::IResult<$i, $o> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$a:ty, $o:ty>, $object:ident, $submac:ident!( $($args:tt)* )) => (
        fn $name<'a>( $object: $a, i: &'a[u8] ) -> $crate::IResult<&'a [u8], $o> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$life:item,$a:ty,$i:ty,$o:ty>, $object:ident, $submac:ident!( $($args:tt)* )) => (
        fn $name<$life>( $object: $a, i: $i ) -> $crate::IResult<$life, $i, $o> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$a:ty>, $object:ident, $submac:ident!( $($args:tt)* )) => (
        fn $name<'nom>( $object: $a, i: &[u8] ) -> $crate::IResult<&[u8], &[u8]> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$a:ty>( $i:ty ) -> $o:ty, $object:ident, $submac:ident!( $($args:tt)* )) => (
        pub fn $name<'nom>( $object: $a, i: $i ) -> $crate::IResult<$i,$o> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$a:ty,$i:ty,$o:ty>, $object:ident, $submac:ident!( $($args:tt)* )) => (
        pub fn $name<'nom>( $object: $a, i: $i ) -> $crate::IResult<$i, $o> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$a:ty,$o:ty>, $object:ident, $submac:ident!( $($args:tt)* )) => (
        pub fn $name<'nom>( $object: $a, i: &[u8] ) -> $crate::IResult<&[u8], $o> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$a:ty>, $object:ident, $submac:ident!( $($args:tt)* )) => (
        pub fn $name<'a>( $object: $a, i: &'a [u8] ) -> $crate::IResult<&[u8], &[u8]> {
            $submac!(i, $($args)*)
        }
    );
);

/// Used to wrap common expressions and function as macros
#[macro_export]
macro_rules! call_m (
  ($i:expr, $obj:ident.$method:ident) => ( $obj.$method( $i ) );
  ($i:expr, $obj:ident.$method1:ident.$method2:ident) => ( $obj.$method1().$method2( $i ) );
  ($i:expr, $obj:ident.$method:ident, $($args:expr),* ) => ( $obj.$method( $i, $($args),* ) );
);

/// emulate function currying: `apply!(my_function, arg1, arg2, ...)` becomes `my_function(input, arg1, arg2, ...)`
///
/// Supports up to 6 arguments
#[macro_export]
macro_rules! apply_m (
  ($i:expr, $obj:ident.$method:ident, $($args:expr),* ) => ( $obj.$method( $i, $($args),* ) );
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
macro_rules! error_m (
  // ($i:expr, $code:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     let cl = || {
  //       $submac!($i, $($args)*)
  //     };

  //     match cl() {
  //       $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
  //       $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
  //       $crate::IResult::Error(e)      => {
  //         return $crate::IResult::Error($crate::Err::NodePosition($code, $i, Box::new(e)))
  //       }
  //     }
  //   }
  // );
  ($i:expr, $code:expr, $obj:ident.$method:ident) => (
    error!($i, $code, call_m!($obj.$method));
  );
);

/// Add an error if the child parser fails
///
/// While error! does an early return and avoids backtracking,
/// add_error! backtracks normally. It just provides more context
/// for an error
///
#[macro_export]
macro_rules! add_error_m (
  // ($i:expr, $code:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
  //       $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
  //       $crate::IResult::Error(e)      => {
  //         $crate::IResult::Error($crate::Err::NodePosition($code, $i, Box::new(e)))
  //       }
  //     }
  //   }
  // );
  ($i:expr, $code:expr, $obj:ident.$method:ident) => (
    add_error!($i, $code, call_m!($obj.$method));
  );
);


/// translate parser result from IResult<I,O,u32> to IResult<I,O,E> woth a custom type
///
#[macro_export]
macro_rules! fix_error_m (
  // ($i:expr, $t:ty, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
  //       $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
  //       $crate::IResult::Error($crate::Err::Code(ErrorKind::Custom(_))) |
  //         $crate::IResult::Error($crate::Err::Node(ErrorKind::Custom(_), _))=> {
  //         let e: ErrorKind<$t> = ErrorKind::Fix;
  //         $crate::IResult::Error($crate::Err::Code(e))
  //       },
  //       $crate::IResult::Error($crate::Err::Position(ErrorKind::Custom(_), p)) |
  //         $crate::IResult::Error($crate::Err::NodePosition(ErrorKind::Custom(_), p, _)) => {
  //         let e: ErrorKind<$t> = ErrorKind::Fix;
  //         $crate::IResult::Error($crate::Err::Position(e, p))
  //       },
  //       $crate::IResult::Error($crate::Err::Code(_)) |
  //         $crate::IResult::Error($crate::Err::Node(_, _))=> {
  //         let e: ErrorKind<$t> = ErrorKind::Fix;
  //         $crate::IResult::Error($crate::Err::Code(e))
  //       },
  //       $crate::IResult::Error($crate::Err::Position(_, p)) |
  //         $crate::IResult::Error($crate::Err::NodePosition(_, p, _)) => {
  //         let e: ErrorKind<$t> = ErrorKind::Fix;
  //         $crate::IResult::Error($crate::Err::Position(e, p))
  //       },
  //     }
  //   }
  // );
  ($i:expr, $t:ty, $obj:ident.$method:ident) => (
    fix_error!($i, $t, call_m!($obj.$method));
  );
);

/// replaces a `Incomplete` returned by the child parser
/// with an `Error`
///
#[macro_export]
macro_rules! complete_m (
  // ($i:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
  //       $crate::IResult::Error(e)      => $crate::IResult::Error(e),
  //       $crate::IResult::Incomplete(_) =>  {
  //         $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Complete, $i))
  //       },
  //     }
  //   }
  // );
  ($i:expr, $obj:ident.$method:ident) => (
    complete!($i, call_m!($obj.$method));
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
macro_rules! try_parse_m (
  // ($i:expr, $submac:ident!( $($args:tt)* )) => (
  //   match $submac!($i, $($args)*) {
  //     $crate::IResult::Done(i,o)     => (i,o),
  //     $crate::IResult::Error(e)      => return $crate::IResult::Error(e),
  //     $crate::IResult::Incomplete(i) => return $crate::IResult::Incomplete(i)
  //   }
  // );
  ($i:expr, $obj:ident.$method:ident) => (
    try_parse!($i, call_m!($obj.$method))
  );
);

/// `flat_map!(R -> IResult<R,S>, S -> IResult<S,T>) => R -> IResult<R, T>`
///
/// combines a parser R -> IResult<R,S> and
/// a parser S -> IResult<S,T> to return another
/// parser R -> IResult<R,T>
#[macro_export]
macro_rules! flat_map_m (
  // ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
  //       $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
  //       $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
  //       $crate::IResult::Done(i, o)                          => match $submac2!(o, $($args2)*) {
  //         $crate::IResult::Error(e)                                 => {
  //           let err = match e {
  //             $crate::Err::Code(k) | $crate::Err::Node(k, _) | $crate::Err::Position(k, _) | $crate::Err::NodePosition(k, _, _) => {
  //               $crate::Err::Position(k, $i)
  //             }
  //           };
  //           $crate::IResult::Error(err)
  //         },
  //         $crate::IResult::Incomplete($crate::Needed::Unknown)      => $crate::IResult::Incomplete($crate::Needed::Unknown),
  //         $crate::IResult::Incomplete($crate::Needed::Size(ref i2)) => $crate::IResult::Incomplete($crate::Needed::Size(*i2)),
  //         $crate::IResult::Done(_, o2)                              => $crate::IResult::Done(i, o2)
  //       }
  //     }
  //   }
  // );
  ($i:expr, $submac:ident!( $($args:tt)* ), $obj:ident.$method:ident) => (
    flat_map!($i, $submac!($($args)*), call_m!($obj.$method));
  );
  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident) => (
    flat_map!($i, call_m!($obj1.$method1), call_m!($obj2.$method2));
  );
  ($i:expr, $obj:ident.$method:ident, $submac:ident!( $($args:tt)* )) => (
    flat_map!($i, call_m!($obj.$method), $submac!($($args)*));
  );
);

/// `map!(I -> IResult<I,O>, O -> P) => I -> IResult<I, P>`
/// maps a function on the result of a parser
#[macro_export]
macro_rules! map_m(
  ($i:expr, $submac:ident!( $($args:tt)* ), $obj:ident.$method:ident) => (
    map_impl!($i, $submac!($($args)*), call!($obj.$method));
  );
  // ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
  //   map_impl!($i, $submac!($($args)*), $submac2!($($args2)*));
  // );
  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident) => (
    map_impl!($i, call_m!($obj.$method), call_m!($obj2.$method2));
  );
  ($i:expr, $obj:ident.$method:ident, $submac:ident!( $($args:tt)* )) => (
    map_impl!($i, call_m!($obj.$method), $submac!($($args)*));
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
// macro_rules! map_impl_m(
//   ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
//     {
//       match $submac!($i, $($args)*) {
//         $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
//         $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
//         $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
//         $crate::IResult::Done(i, o)                          => $crate::IResult::Done(i, $submac2!(o, $($args2)*))
//       }
//     }
//   );
// );

/// `map_res!(I -> IResult<I,O>, O -> Result<P>) => I -> IResult<I, P>`
/// maps a function returning a Result on the output of a parser
#[macro_export]
macro_rules! map_res_m (
  ($i:expr, $submac:ident!( $($args:tt)* ), $obj:ident.$method:ident) => (
    map_res_impl!($i, $submac!($($args)*), call!($obj.$method));
  );
  // ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
  //   map_res_impl!($i, $submac!($($args)*), $submac2!($($args2)*));
  // );
  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident,) => (
    map_res_impl!($i, call_m!($obj1.$method1), call!($obj2.$method2));
  );
  ($i:expr, $obj:ident.$method:ident, $submac:ident!( $($args:tt)* )) => (
    map_res_impl!($i, call_m!($obj.$method), $submac!($($args)*));
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
// macro_rules! map_res_impl_m (
//   ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
//     {
//       match $submac!($i, $($args)*) {
//         $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
//         $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
//         $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
//         $crate::IResult::Done(i, o)                          => match $submac2!(o, $($args2)*) {
//           Ok(output) => $crate::IResult::Done(i, output),
//           Err(_)     => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::MapRes, $i))
//         }
//       }
//     }
//   );
// );


/// `map_opt!(I -> IResult<I,O>, O -> Option<P>) => I -> IResult<I, P>`
/// maps a function returning an Option on the output of a parser
#[macro_export]
macro_rules! map_opt_m (
  ($i:expr, $submac:ident!( $($args:tt)* ), $obj:ident.$method:ident) => (
    map_opt_impl!($i, $submac!($($args)*), call!($obj.$method));
  );
  // ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
  //   map_opt_impl!($i, $submac!($($args)*), $submac2!($($args2)*));
  // );
  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident) => (
    map_opt_impl!($i, call_m!($obj.$method), call!($obj.$method));
  );
  ($i:expr, $obj:ident.$method:ident, $submac:ident!( $($args:tt)* )) => (
    map_opt_impl!($i, call_m!($obj.$method), $submac!($($args)*));
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
// macro_rules! map_opt_impl_m (
//   ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
//     {
//       match $submac!($i, $($args)*) {
//         $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
//         $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
//         $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
//         $crate::IResult::Done(i, o)                          => match $submac2!(o, $($args2)*) {
//           ::std::option::Option::Some(output) => $crate::IResult::Done(i, output),
//           ::std::option::Option::None         => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::MapOpt, $i))
//         }
//       }
//     }
//   );
// );

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
macro_rules! value_m (
  // ($i:expr, $res:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     use $crate::HexDisplay;
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Done(i,_)     => {
  //         $crate::IResult::Done(i, $res)
  //       },
  //       $crate::IResult::Error(e)      => return $crate::IResult::Error(e),
  //       $crate::IResult::Incomplete(i) => return $crate::IResult::Incomplete(i)
  //     }
  //   }
  // );
  ($i:expr, $res:expr, $obj:ident.$method:ident) => (
    value!($i, $res, call_m!($obj.$method))
  );
  // ($i:expr, $res:expr) => (
  //   $crate::IResult::Done($i, $res)
  // );
);

// /// `expr_res!(Result<E,O>) => I -> IResult<I, O>`
// /// evaluate an expression that returns a Result<T,E> and returns a IResult::Done(I,T) if Ok
// ///
// /// See expr_opt for an example
// #[macro_export]
// macro_rules! expr_res (
//   ($i:expr, $e:expr) => (
//     {
//       match $e {
//         Ok(output) => $crate::IResult::Done($i, output),
//         Err(_)     => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::ExprRes, $i))
//       }
//     }
//   );
// );

/// `expr_opt!(Option<O>) => I -> IResult<I, O>`
/// evaluate an expression that returns a Option<T> and returns a IResult::Done(I,T) if Ok
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
// macro_rules! expr_opt (
//   ($i:expr, $e:expr) => (
//     {
//       match $e {
//         ::std::option::Option::Some(output) => $crate::IResult::Done($i, output),
//         ::std::option::Option::None         => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::ExprOpt, $i))
//       }
//     }
//   );
// );

/// `chain!(I->IResult<I,A> ~ I->IResult<I,B> ~ ... I->IResult<I,X> , || { return O } ) => I -> IResult<I, O>`
/// chains parsers and assemble the results through a closure
/// the input type I must implement nom::InputLength
/// this combinator will count how much data is consumed by every child parser and take it into account if
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
macro_rules! chain_m (
  ($i:expr, $obj:ident, $($rest:tt)*) => (
    {
      //use $crate::InputLength;

      use std::cell::RefCell;
      let object_cell = RefCell::new($obj);
      chaining_parser_m!($i, 0usize, object_cell, $($rest)*)
    }
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! chaining_parser_m (
  ($i:expr, $consumed:expr, $cell:ident, $method:ident ~ $($rest:tt)*) => (
    chaining_parser_m!($i, $consumed, $cell, call_m!($cell.borrow_mut.$method) ~ $($rest)*);
  );
  ($i:expr, $consumed:expr, $cell:ident, $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    {
      use $crate::InputLength;
      let input = {
        let res = $submac!($i, $($args)*);
        match res {
          $crate::IResult::Error(e)      => return $crate::IResult::Error(e),
          $crate::IResult::Incomplete($crate::Needed::Unknown) => return $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => return $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
          $crate::IResult::Done(i,_)     => i,
        }
      };
      {
        chaining_parser_m!(input, $consumed + (($i).input_len() - input.input_len()), $cell, $($rest)*)
      }
    }
  );

  ($i:expr, $consumed:expr, $cell:ident, $method:ident  ? ~ $($rest:tt)*) => (
    chaining_parser_m!($i, $consumed, $cell, call_m!($cell.borrow_mut.$method) ? ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $cell:ident, $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => ({
    {
      use $crate::InputLength;
      let input = {
        let res = $submac!($i, $($args)*);
        if let $crate::IResult::Incomplete(inc) = res {
          match inc {
            $crate::Needed::Unknown => return $crate::IResult::Incomplete($crate::Needed::Unknown),
            $crate::Needed::Size(i) => return $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
          }
        }
        if let $crate::IResult::Done(i,_) = res {
          i
        } else {
          $i
        }
      };
      {
        chaining_parser_m!(input, $consumed + (($i).input_len() - input.input_len()), $cell, $($rest)*)
      }
    }
  });

  ($i:expr, $consumed:expr, $cell:ident, $field:ident : $method:ident  ~ $($rest:tt)*) => (
    chaining_parser_m!($i, $consumed, $cell, $field: call_m!($cell.borrow_mut.$method) ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $cell:ident, $field:ident : $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    {
      use $crate::InputLength;
      let (input, $field) = {
        let res = $submac!($i, $($args)*);
        match res {
          $crate::IResult::Error(e)      => return $crate::IResult::Error(e),
          $crate::IResult::Incomplete($crate::Needed::Unknown) => return $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => return $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
          $crate::IResult::Done(i,o)     => (i, o)
        }
      };
      {
        chaining_parser_m!(input, $consumed + (($i).input_len() - input.input_len()), $cell, $($rest)*)
      }
    }
  );

  ($i:expr, $consumed:expr, $cell:ident, mut $field:ident : $method:ident  ~ $($rest:tt)*) => (
    chaining_parser_m!($i, $consumed, $cell, mut $field: call_m!($cell.borrow_mut.$method) ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $cell:ident, mut $field:ident : $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    {
      use $crate::InputLength;
      let (input, $field) = {
        let res = $submac!($i, $($args)*);
        match res {
          $crate::IResult::Error(e)      => return $crate::IResult::Error(e),
          $crate::IResult::Incomplete($crate::Needed::Unknown) => return $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => return $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
          $crate::IResult::Done(i,o)     => (i, o)
        }
      };
      {
        chaining_parser_m!(input, $consumed + ($i).input_len() - input.input_len(), $cell, $($rest)*)
      }
    }
  );

  ($i:expr, $consumed:expr, $cell:ident, $field:ident : $method:ident  ? ~ $($rest:tt)*) => (
    chaining_parser_m!($i, $consumed, $cell, $field : call_m!($cell.borrow_mut.$method) ? ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $cell:ident, $field:ident : $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => ({
    {
      use $crate::InputLength;
      let ($field, input) = {
        let res = $submac!($i, $($args)*);
        if let $crate::IResult::Incomplete(inc) = res {
          match inc {
            $crate::Needed::Unknown => return $crate::IResult::Incomplete($crate::Needed::Unknown),
            $crate::Needed::Size(i) => return $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
          }
        }
        if let $crate::IResult::Done(i,o) = res {
          (::std::option::Option::Some(o),i)
        } else {
          (::std::option::Option::None,$i)
        }
      };
      {
        chaining_parser_m!(input, $consumed + ($i).input_len() - input.input_len(), $cell, $($rest)*)
      }
    }
  });

  ($i:expr, $consumed:expr, $cell:ident, mut $field:ident : $method:ident  ? ~ $($rest:tt)*) => (
    chaining_parser_m!($i, $consumed, $cell, mut $field : call_m!($cell.borrow_mut.$method) ? ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $cell:ident, mut $field:ident : $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => ({
    {
      use $crate::InputLength;
      let($field, input) = {
        let res = $submac!($i, $($args)*);
        if let $crate::IResult::Incomplete(inc) = res {
          match inc {
            $crate::Needed::Unknown => return $crate::IResult::Incomplete($crate::Needed::Unknown),
            $crate::Needed::Size(i) => return $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
          }
        }
        if let $crate::IResult::Done(i,o) = res {
          (::std::option::Option::Some(o),i)
        } else {
          (::std::option::Option::None,$i)
        }
      };
      {
        chaining_parser_m!(input, $consumed + ($i).input_len() - input.input_len(), $cell, $($rest)*)
      }
    }
  });

  // ending the chain
  ($i:expr, $consumed:expr, $cell:ident, $method:ident , $assemble:expr) => (
    chaining_parser!($i, $consumed, $cell, call_m!($cell.borrow_mut.$method), $assemble);
  );

  ($i:expr, $consumed:expr, $cell:ident, $submac:ident!( $($args:tt)* ), $assemble:expr) => ({
      let res = $submac!($i, $($args)*);
      match res {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,_)     => {
          $crate::IResult::Done(i, $assemble())
        }
      }
    }
  );

  ($i:expr, $consumed:expr, $cell:ident, $method:ident  ?, $assemble:expr) => (
    chaining_parser_m!($i, $consumed, $cell, call_m!($cell.borrow_mut.$method) ?, $assemble);
  );

  ($i:expr, $consumed:expr, $cell:ident, $submac:ident!( $($args:tt)* ) ?, $assemble:expr) => ({
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

  ($i:expr, $consumed:expr, $cell:ident, $field:ident : $method:ident , $assemble:expr) => (
    chaining_parser_m!($i, $consumed, $cell, $field: call_m!($cell.borrow_mut.$method), $assemble);
  );

  ($i:expr, $consumed:expr, $cell:ident, $field:ident : $submac:ident!( $($args:tt)* ), $assemble:expr) => ({
      let res = $submac!($i, $($args)*);
      match res {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          let $field = o;
          $crate::IResult::Done(i, $assemble())
        }
      }
    }
  );

  ($i:expr, $consumed:expr, $cell:ident, mut $field:ident : $method:ident , $assemble:expr) => (
    chaining_parser_m!($i, $consumed, $cell, mut $field: call_m!($cell.borrow_mut.$method), $assemble);
  );

  ($i:expr, $consumed:expr, $cell:ident, mut $field:ident : $submac:ident!( $($args:tt)* ), $assemble:expr) => ({
      let res = $submac!($i, $($args)*);
      match res {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          let mut $field = o;
          $crate::IResult::Done(i, $assemble())
        }
      }
    }
  );

  ($i:expr, $consumed:expr, $cell:ident, $field:ident : $method:ident  ? , $assemble:expr) => (
    chaining_parser_m!($i, $consumed, $cell, $field : call_m!($cell.borrow_mut.$method) ? , $assemble);
  );

  ($i:expr, $consumed:expr, $cell:ident, $field:ident : $submac:ident!( $($args:tt)* ) ? , $assemble:expr) => ({
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

  ($i:expr, $consumed:expr, $cell:ident, mut $field:ident : $method:ident  ? , $assemble:expr) => (
    chaining_parser_m!($i, $consumed, $cell, $field : call_m!($cell.borrow_mut.$method) ? , $assemble);
  );

  ($i:expr, $consumed:expr, $cell:ident, mut $field:ident : $submac:ident!( $($args:tt)* ) ? , $assemble:expr) => ({
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
macro_rules! alt_m (
  ($i:expr, $($rest:tt)*) => (
    {
      alt_parser_m!($i, $($rest)*)
    }
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! alt_parser_m (
  ($i:expr, $obj:ident.$method:ident | $($rest:tt)*) => (
    alt_parser_m!($i, call_m!($obj.$method) | $($rest)*);
  );

  ($i:expr, $subrule:ident!( $($args:tt)*) | $($rest:tt)*) => (
    {
      let res = $subrule!($i, $($args)*);
      match res {
        $crate::IResult::Done(_,_)     => res,
        $crate::IResult::Incomplete(_) => res,
        _                              => alt_parser_m!($i, $($rest)*)
      }
    }
  );

  ($i:expr, $subrule:ident!( $($args:tt)* ) => { $gen:expr } | $($rest:tt)+) => (
    {
      match $subrule!( $i, $($args)* ) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,$gen(o)),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(_)      => {
          alt_parser_m!($i, $($rest)*)
        }
      }
    }
  );

  ($i:expr, $obj:ident.$method:ident  => { $gen:expr } | $($rest:tt)*) => (
    alt_parser_m!($i, call_m!($obj.$method) => { $gen } | $($rest)*);
  );

  ($i:expr, $obj:ident.$method:ident  => { $gen:expr }) => (
    alt_parser_m!($i, call_m!($obj.$method) => { $gen });
  );

  ($i:expr, $subrule:ident!( $($args:tt)* ) => { $gen:expr }) => (
    {
      match $subrule!( $i, $($args)* ) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,$gen(o)),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(_)      => {
          alt_parser_m!($i)
        }
      }
    }
  );

  ($i:expr, $obj:ident.$method:ident ) => (
    alt_parser_m!($i, call_m!($obj.$method));
  );

  ($i:expr, $subrule:ident!( $($args:tt)*)) => (
    {
      match $subrule!( $i, $($args)* ) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,o),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(_)      => {
          alt_parser_m!($i)
        }
      }
    }
  );

  ($i:expr) => (
    $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Alt,$i))
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
#[macro_export]
macro_rules! switch_m (
  // ($i:expr, $submac:ident!( $($args:tt)*), $($p:pat => $subrule:ident!( $($args2:tt)* ))|*) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Error(e)      => $crate::IResult::Error($crate::Err::NodePosition(
  //           $crate::ErrorKind::Switch, $i, ::std::boxed::Box::new(e)
  //       )),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //       $crate::IResult::Done(i, o)    => {
  //         match o {
  //           $($p => match $subrule!(i, $($args2)*) {
  //             $crate::IResult::Error(e) => $crate::IResult::Error($crate::Err::NodePosition(
  //                 $crate::ErrorKind::Switch, $i, ::std::boxed::Box::new(e)
  //             )),
  //             a => a,
  //           }),*,
  //           _    => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Switch,$i))
  //         }
  //       }
  //     }
  //   }
  // );
  ($i:expr, $obj:ident.$method:ident , $($rest:tt)*) => (
    {
      switch!($i, call_m!($obj.$method), $($rest)*)
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
macro_rules! opt_m(
  // ($i:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, ::std::option::Option::Some(o)),
  //       $crate::IResult::Error(_)      => $crate::IResult::Done($i, ::std::option::Option::None),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
  //     }
  //   }
  // );
  ($i:expr, $obj:ident.$method:ident) => (
    opt!($i, call_m!($obj.$method));
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
macro_rules! opt_res_m (
  // ($i:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,  Ok(o)),
  //       $crate::IResult::Error(e)      => $crate::IResult::Done($i, Err(e)),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
  //     }
  //   }
  // );
  ($i:expr, $obj:ident.$method:ident) => (
    opt_res!($i, call_m!($obj.$method));
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
macro_rules! cond_m (
  // ($i:expr, $cond:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     if $cond {
  //       match $submac!($i, $($args)*) {
  //         $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, ::std::option::Option::Some(o)),
  //         $crate::IResult::Error(_)      => $crate::IResult::Done($i, ::std::option::Option::None),
  //         $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
  //       }
  //     } else {
  //       $crate::IResult::Done($i, ::std::option::Option::None)
  //     }
  //   }
  // );
  ($i:expr, $cond:expr, $obj:ident.$method:ident) => (
    cond!($i, $cond, call_m!($obj.$method));
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
macro_rules! cond_reduce_m (
  // ($i:expr, $cond:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     if $cond {
  //       match $submac!($i, $($args)*) {
  //         $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, o),
  //         $crate::IResult::Error(e)      => $crate::IResult::Error(e),
  //         $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
  //       }
  //     } else {
  //       $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::CondReduce, $i))
  //     }
  //   }
  // );
  ($i:expr, $cond:expr, $obj:ident.$method:ident) => (
    cond_reduce!($i, $cond, call_m!($obj.$method));
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
macro_rules! peek_m (
  // ($i:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Done(_,o)     => $crate::IResult::Done($i, o),
  //       $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
  //     }
  //   }
  // );
  ($i:expr, $obj:ident.$method:ident) => (
    peek!($i, call_m!($obj.$method));
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
macro_rules! tap_m (
  // ($i:expr, $name:ident : $submac:ident!( $($args:tt)* ) => $e:expr) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Done(i,o)     => {
  //         let $name = o;
  //         $e;
  //         $crate::IResult::Done(i, $name)
  //       },
  //       $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
  //     }
  //   }
  // );
  ($i:expr, $name:ident : $obj:ident.$method:ident => $e:expr) => (
    tap!($i, $name: call_m!($obj.$method) => $e);
  );
);

/// `pair!(I -> IResult<I,O>, I -> IResult<I,P>) => I -> IResult<I, (O,P)>`
/// pair(X,Y), returns (x,y)
///
#[macro_export]
macro_rules! pair_m (
  // ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //       $crate::IResult::Done(i1,o1)   => {
  //         match $submac2!(i1, $($args2)*) {
  //           $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //           $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //           $crate::IResult::Done(i2,o2)   => {
  //             $crate::IResult::Done(i2, (o1, o2))
  //           }
  //         }
  //       },
  //     }
  //   }
  // );

  ($i:expr, $submac:ident!( $($args:tt)* ), $obj:ident.$method:ident) => (
    pair!($i, $submac!($($args)*), call_m!($obj.$method));
  );

  ($i:expr, $obj:ident.$method:ident, $submac:ident!( $($args:tt)* )) => (
    pair!($i, call_m!($obj.$method), $submac!($($args)*));
  );

  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident) => (
    pair!($i, call_m!($obj1.$method1), call_m!($obj2.$method2));
  );
);

/// `separated_pair!(I -> IResult<I,O>, I -> IResult<I, T>, I -> IResult<I,P>) => I -> IResult<I, (O,P)>`
/// separated_pair(X,sep,Y) returns (x,y)
#[macro_export]
macro_rules! separated_pair_m (
  ($i:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)+) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,o1)   => {
          separated_pair1_m!(i1, o1,  $($rest)*)
        }
      }
    }
  );

  ($i:expr, $obj:ident.$method:ident, $($rest:tt)+) => (
    separated_pair_m!($i, call_m!($obj.$method), $($rest)*);
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! separated_pair1_m(
  ($i:expr, $res1:ident, $submac2:ident!( $($args2:tt)* ), $($rest:tt)+) => (
    {
      match $submac2!($i, $($args2)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i2,_)    => {
          separated_pair2_m!(i2, $res1,  $($rest)*)
        }
      }
    }
  );
  ($i:expr, $res1:ident, $obj:ident.$method:ident, $($rest:tt)+) => (
    separated_pair1_m!($i, $res1, call_m!($obj.$method), $($rest)*);
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! separated_pair2_m(
  // ($i:expr, $res1:ident, $submac3:ident!( $($args3:tt)* )) => (
  //   {
  //     match $submac3!($i, $($args3)*) {
  //       $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //       $crate::IResult::Done(i3,o3)   => {
  //         $crate::IResult::Done(i3, ($res1, o3))
  //       }
  //     }
  //   }
  // );

  ($i:expr, $res1:ident, $obj:ident.$method:ident) => (
    separated_pair2!($i, $res1, call_m!($obj.$method));
  );
);

/// `preceded!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, O>`
/// preceded(opening, X) returns X
#[macro_export]
macro_rules! preceded_m(
  // ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //       $crate::IResult::Done(i1,_)    => {
  //         match $submac2!(i1, $($args2)*) {
  //           $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //           $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //           $crate::IResult::Done(i2,o2)   => {
  //             $crate::IResult::Done(i2, o2)
  //           }
  //         }
  //       },
  //     }
  //   }
  // );

  ($i:expr, $submac:ident!( $($args:tt)* ), $obj:ident.$method:ident) => (
    preceded!($i, $submac!($($args)*), call_m!($obj.$method));
  );

  ($i:expr, $obj:ident.$method:ident, $submac:ident!( $($args:tt)* )) => (
    preceded!($i, call_m!($obj.$method), $submac!($($args)*));
  );

  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident) => (
    preceded!($i, call_m!($obj1.$method1), call_m!($obj2.$method2));
  );
);

/// `terminated!(I -> IResult<I,O>, I -> IResult<I,T>) => I -> IResult<I, O>`
/// terminated(X, closing) returns X
#[macro_export]
macro_rules! terminated_m (
  // ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
  //   {
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //       $crate::IResult::Done(i1,o1)   => {
  //         match $submac2!(i1, $($args2)*) {
  //           $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //           $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //           $crate::IResult::Done(i2,_)    => {
  //             $crate::IResult::Done(i2, o1)
  //           }
  //         }
  //       },
  //     }
  //   }
  // );

  ($i:expr, $submac:ident!( $($args:tt)* ), $obj:ident.$method:ident) => (
    terminated!($i, $submac!($($args)*), call_m!($obj.$method));
  );

  ($i:expr, $obj:ident.$method:ident, $submac:ident!( $($args:tt)* )) => (
    terminated!($i, call_m!($obj.$method), $submac!($($args)*));
  );

  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident) => (
    terminated!($i, call_m!($obj1.$method1), call_m!($obj2.$method2));
  );
);

/// `delimited!(I -> IResult<I,T>, I -> IResult<I,O>, I -> IResult<I,U>) => I -> IResult<I, O>`
/// delimited(opening, X, closing) returns X
#[macro_export]
macro_rules! delimited_m (
  ($i:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)+) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,_)    => {
          delimited1_m!(i1,  $($rest)*)
        }
      }
    }
  );

  ($i:expr, $obj:ident.$method:ident, $($rest:tt)+) => (
    delimited_m!($i, call_m!($obj.$method), $($rest)*);
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! delimited1_m (
  ($i:expr, $submac2:ident!( $($args2:tt)* ), $($rest:tt)+) => (
    {
      match $submac2!($i, $($args2)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i2,o2)   => {
          delimited2_m!(i2, o2,  $($rest)*)
        }
      }
    }
  );
  ($i:expr, $obj:ident.$method:ident, $($rest:tt)+) => (
    delimited1_m!($i, call_m!($obj.$method), $($rest)*);
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! delimited2_m (
  // ($i:expr, $res2:ident, $submac3:ident!( $($args3:tt)* )) => (
  //   {
  //     match $submac3!($i, $($args3)*) {
  //       $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //       $crate::IResult::Done(i3,_)    => {
  //         $crate::IResult::Done(i3, $res2)
  //       }
  //     }
  //   }
  // );

  ($i:expr, $res2:ident, $obj:ident.$method:ident) => (
    delimited2!($i, $res2, call_m!($obj.$method));
  );
);

/// `separated_list!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// separated_list(sep, X) returns Vec<X>
#[macro_export]
macro_rules! separated_list_m (
  // ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => (
  //   {
  //     let mut res   = ::std::vec::Vec::new();
  //     let mut input = $i;

  //     // get the first element
  //     match $submac!(input, $($args2)*) {
  //       $crate::IResult::Error(_)      => $crate::IResult::Done(input, ::std::vec::Vec::new()),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //       $crate::IResult::Done(i,o)     => {
  //         if i.len() == input.len() {
  //           $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::SeparatedList,input))
  //         } else {
  //           res.push(o);
  //           input = i;

  //           loop {
  //             // get the separator first
  //             if let $crate::IResult::Done(i2,_) = $sep!(input, $($args)*) {
  //               if i2.len() == input.len() {
  //                 break;
  //               }
  //               input = i2;

  //               // get the element next
  //               if let $crate::IResult::Done(i3,o3) = $submac!(input, $($args2)*) {
  //                 if i3.len() == input.len() {
  //                   break;
  //                 }
  //                 res.push(o3);
  //                 input = i3;
  //               } else {
  //                 break;
  //               }
  //             } else {
  //               break;
  //             }
  //           }
  //           $crate::IResult::Done(input, res)
  //         }
  //       },
  //     }
  //   }
  // );
  ($i:expr, $submac:ident!( $($args:tt)* ), $obj:ident.$method:ident) => (
    separated_list!($i, $submac!($($args)*), call_m!($obj.$method));
  );
  ($i:expr, $obj:ident.$method:ident, $submac:ident!( $($args:tt)* )) => (
    separated_list!($i, call_m!($obj.$method), $submac!($($args)*));
  );
  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident) => (
    separated_list!($i, call_m!($obj1.$method1), call_m!($obj2.$method2));
  );
);

/// `separated_nonempty_list!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// separated_nonempty_list(sep, X) returns Vec<X>
#[macro_export]
macro_rules! separated_nonempty_list_m (
  // ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => (
  //   {
  //     let mut res   = ::std::vec::Vec::new();
  //     let mut input = $i;

  //     // get the first element
  //     match $submac!(input, $($args2)*) {
  //       $crate::IResult::Error(a)      => $crate::IResult::Error(a),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //       $crate::IResult::Done(i,o)     => {
  //         if i.len() == input.len() {
  //           $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::SeparatedNonEmptyList,input))
  //         } else {
  //           res.push(o);
  //           input = i;

  //           loop {
  //             if let $crate::IResult::Done(i2,_) = $sep!(input, $($args)*) {
  //               if i2.len() == input.len() {
  //                 break;
  //               }
  //               input = i2;

  //               if let $crate::IResult::Done(i3,o3) = $submac!(input, $($args2)*) {
  //                 if i3.len() == input.len() {
  //                   break;
  //                 }
  //                 res.push(o3);
  //                 input = i3;
  //               } else {
  //                 break;
  //               }
  //             } else {
  //               break;
  //             }
  //           }
  //           $crate::IResult::Done(input, res)
  //         }
  //       },
  //     }
  //   }
  // );
  ($i:expr, $submac:ident!( $($args:tt)* ), $obj:ident.$method:ident) => (
    separated_nonempty_list!($i, $submac!($($args)*), call_m!($obj.$method));
  );
  ($i:expr, $obj:ident.$method:ident, $submac:ident!( $($args:tt)* )) => (
    separated_nonempty_list!($i, call_m!($obj.$method), $submac!($($args)*));
  );
  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident) => (
    separated_nonempty_list!($i, call_m!($obj1.$method1), call_m!($obj2.$method2));
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
macro_rules! many0_m (
  // ($i:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     use $crate::InputLength;
  //     if ($i).input_len() == 0 {
  //       $crate::IResult::Done($i, ::std::vec::Vec::new())
  //     } else {
  //       match $submac!($i, $($args)*) {
  //         $crate::IResult::Error(_)      => { 
  //           $crate::IResult::Done($i, ::std::vec::Vec::new())
  //         },
  //         $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //         $crate::IResult::Done(i1,o1)   => {
  //           if i1.input_len() == 0 {
  //             $crate::IResult::Done(i1,vec![o1])
  //           } else {
  //             let mut res    = ::std::vec::Vec::with_capacity(4);
  //             res.push(o1);
  //             let mut input  = i1;
  //             let mut incomplete: ::std::option::Option<$crate::Needed> = ::std::option::Option::None;
  //             loop {
  //               match $submac!(input, $($args)*) {
  //                 $crate::IResult::Done(i, o) => {
  //                   // do not allow parsers that do not consume input (causes infinite loops)
  //                   if i.input_len() == input.input_len() {
  //                     break;
  //                   }
  //                   res.push(o);
  //                   input = i;
  //                 }
  //                 $crate::IResult::Error(_)                    => {
  //                   break;
  //                 },
  //                 $crate::IResult::Incomplete($crate::Needed::Unknown) => {
  //                   incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
  //                   break;
  //                 },
  //                 $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
  //                   incomplete = ::std::option::Option::Some($crate::Needed::Size(i + ($i).input_len() - input.input_len()));
  //                   break;
  //                 },
  //               }
  //               if input.input_len() == 0 {
  //                 break;
  //               }
  //             }

  //             match incomplete {
  //               ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
  //               ::std::option::Option::None    => $crate::IResult::Done(input, res)
  //             }
  //           }
  //         }
  //       }
  //     }
  //   }
  // );
  ($i:expr, $obj:ident.$method:ident) => (
    many0!($i, call_m!($obj.$method));
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
macro_rules! many1_m (
  // ($i:expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     use $crate::InputLength;
  //     match $submac!($i, $($args)*) {
  //       $crate::IResult::Error(_)      => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Many1,$i)),
  //       $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
  //       $crate::IResult::Done(i1,o1)   => {
  //         if i1.len() == 0 {
  //           $crate::IResult::Done(i1,vec![o1])
  //         } else {

  //           let mut res    = ::std::vec::Vec::with_capacity(4);
  //           res.push(o1);
  //           let mut input  = i1;
  //           let mut incomplete: ::std::option::Option<$crate::Needed> = ::std::option::Option::None;
  //           loop {
  //             if input.input_len() == 0 {
  //               break;
  //             }
  //             match $submac!(input, $($args)*) {
  //               $crate::IResult::Error(_)                    => {
  //                 break;
  //               },
  //               $crate::IResult::Incomplete($crate::Needed::Unknown) => {
  //                 incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
  //                 break;
  //               },
  //               $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
  //                 incomplete = ::std::option::Option::Some($crate::Needed::Size(i + ($i).input_len() - input.input_len()));
  //                 break;
  //               },
  //               $crate::IResult::Done(i, o) => {
  //                 if i.input_len() == input.input_len() {
  //                   break;
  //                 }
  //                 res.push(o);
  //                 input = i;
  //               }
  //             }
  //           }

  //           match incomplete {
  //             ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
  //             ::std::option::Option::None    => $crate::IResult::Done(input, res)
  //           }
  //         }
  //       }
  //     }
  //   }
  // );
  ($i:expr, $obj:ident.$method:ident) => (
    many1!($i, call_m!($obj.$method));
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
macro_rules! many_m_n_m(
  // ($i:expr, $m:expr, $n: expr, $submac:ident!( $($args:tt)* )) => (
  //   {
  //     use $crate::InputLength;
  //     let mut res          = ::std::vec::Vec::with_capacity($m);
  //     let mut input        = $i;
  //     let mut count: usize = 0;
  //     let mut err          = false;
  //     let mut incomplete: ::std::option::Option<$crate::Needed> = ::std::option::Option::None;
  //     loop {
  //       if count == $n { break }
  //       match $submac!(input, $($args)*) {
  //         $crate::IResult::Done(i, o) => {
  //           // do not allow parsers that do not consume input (causes infinite loops)
  //           if i.input_len() == input.input_len() {
  //             break;
  //           }
  //           res.push(o);
  //           input  = i;
  //           count += 1;
  //         }
  //         $crate::IResult::Error(_)                    => {
  //           err = true;
  //           break;
  //         },
  //         $crate::IResult::Incomplete($crate::Needed::Unknown) => {
  //           incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
  //           break;
  //         },
  //         $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
  //           incomplete = ::std::option::Option::Some($crate::Needed::Size(i + ($i).input_len() - input.input_len()));
  //           break;
  //         },
  //       }
  //       if input.input_len() == 0 {
  //         break;
  //       }
  //     }

  //     if count < $m {
  //       if err {
  //         $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::ManyMN,$i))
  //       } else {
  //         match incomplete {
  //           ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
  //           ::std::option::Option::None    => $crate::IResult::Incomplete($crate::Needed::Unknown)
  //         }
  //       }
  //     } else {
  //       match incomplete {
  //         ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
  //         ::std::option::Option::None    => $crate::IResult::Done(input, res)
  //       }
  //     }
  //   }
  // );
  ($i:expr, $m:expr, $n: expr, $obj:ident.$method:ident) => (
    many_m_n!($i, $m, $n, call_m!($obj.$method));
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
macro_rules! count_m (
  // ($i:expr, $submac:ident!( $($args:tt)* ), $count: expr) => (
  //   {
  //     let mut input      = $i;
  //     let mut res        = ::std::vec::Vec::with_capacity($count);
  //     let mut cnt: usize = 0;
  //     let mut err        = false;
  //     loop {
  //       if cnt == $count {
  //         break
  //       }
  //       match $submac!(input, $($args)*) {
  //         $crate::IResult::Done(i,o) => {
  //           res.push(o);
  //           input = i;
  //           cnt = cnt + 1;
  //         },
  //         $crate::IResult::Error(_)  => {
  //           err = true;
  //           break;
  //         },
  //         $crate::IResult::Incomplete(_) => {
  //           break;
  //         }
  //       }
  //     }
  //     if err {
  //       $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Count,$i))
  //     } else if cnt == $count {
  //       $crate::IResult::Done(input, res)
  //     } else {
  //       $crate::IResult::Incomplete($crate::Needed::Unknown)
  //     }
  //   }
  // );
  ($i:expr, $obj:ident.$method:ident, $count: expr) => (
    count!($i, call_m!($obj.$method), $count);
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
macro_rules! count_fixed_m (
  // ($i:expr, $typ:ty, $submac:ident!( $($args:tt)* ), $count: expr) => (
  //   {
  //     let mut input = $i;
  //     // `$typ` must be Copy, and thus having no destructor, this is panic safe
  //     let mut res: [$typ; $count] = unsafe{[::std::mem::uninitialized(); $count as usize]};
  //     let mut cnt: usize = 0;
  //     let mut err = false;
  //     loop {
  //       if cnt == $count {
  //         break
  //       }
  //       match $submac!(input, $($args)*) {
  //         $crate::IResult::Done(i,o) => {
  //           res[cnt] = o;
  //           input = i;
  //           cnt = cnt + 1;
  //         },
  //         $crate::IResult::Error(_)  => {
  //           err = true;
  //           break;
  //         },
  //         $crate::IResult::Incomplete(_) => {
  //           break;
  //         }
  //       }
  //     }
  //     if err {
  //       $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Count,$i))
  //     } else if cnt == $count {
  //       $crate::IResult::Done(input, res)
  //     } else {
  //       $crate::IResult::Incomplete($crate::Needed::Unknown)
  //     }
  //   }
  // );
  ($i:expr, $typ: ty, $obj:ident.$method:ident, $count: expr) => (
    count_fixed!($i, $typ, call_m!($obj.$method), $count);
  );
);

/// `length_value!(I -> IResult<I, nb>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// gets a number from the first parser, then applies the second parser that many times
#[macro_export]
macro_rules! length_value_m (
  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident) => (
    {
      match $obj1.$method1($i) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,nb)   => {
          let length_token     = $i.len() - i1.len();
          let mut input        = i1;
          let mut res          = ::std::vec::Vec::new();
          let mut err          = false;
          let mut inc          = $crate::Needed::Unknown;

          loop {
            if res.len() == nb as usize {
              break;
            }
            match $obj2.method2(input) {
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
            $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::LengthValue,$i))
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
  ($i:expr, $obj1:ident.$method1:ident, $obj2:ident.$method2:ident, $length:expr) => (
    {
      match $obj1.$method1($i) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,nb)   => {
          let length_token     = $i.len() - i1.len();
          let mut input        = i1;
          let mut res          = ::std::vec::Vec::new();
          let mut err          = false;
          let mut inc          = $crate::Needed::Unknown;

          loop {
            if res.len() == nb as usize {
              break;
            }
            match $obj2.$method2(input) {
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
            $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::LengthValue,$i))
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
        let bytes = as_bytes(&expected);

        let res : $crate::IResult<&[u8],&[u8]> = if bytes.len() > $i.len() {
          $crate::IResult::Incomplete($crate::Needed::Size(bytes.len()))
        } else if &$i[0..bytes.len()] == bytes {
          $crate::IResult::Done(&$i[bytes.len()..], &$i[0..bytes.len()])
        } else {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::Tag, $i))
        };
        res
      }
    );
  );

  macro_rules! take (
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
    struct TestStruct;
    impl TestStruct {
      method!(pub tst<&TestStruct>, tag!("abcd"));

      pub fn sum2(a:u8, b:u8)       -> u8 { a + b }
      pub fn sum3(a:u8, b:u8, c:u8) -> u8 { a + b + c }
    }
  }

  #[test]
  fn pub_named_test() {
    let a = &b"abcd"[..];
    let t = pub_named_mod::TestStruct{};
    let res = t.tst(a);
    assert_eq!(res, Done(&b""[..], a));
  }

  #[test]
  fn apply_test() {
    let t = pub_named_mod::TestStruct{};
    let a = apply!(1, t.sum2, 2);
    let b = apply!(1, t.sum3, 2, 3);

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
    struct TestStruct;
    impl TestStruct {
      fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) }
      fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) }
      method!(f<&TestStruct,&[u8],B>,
        chain_m!(
          tag!("abcd")        ~
          tag!("abcd")?       ~
          aa: self.ret_int1   ~
          tag!("efgh")        ~
          bb: self.ret_int2   ~
          tag!("efgh")        ,
          ||{B{a: aa, b: bb}}
        )
      );
    };

    let t = TestStruct{};
    let r = t.f(&b"abcdabcdefghefghX"[..]);
    assert_eq!(r, Done(&b"X"[..], B{a: 1, b: 2}));

    let r2 = t.f(&b"abcdefghefghX"[..]);
    assert_eq!(r2, Done(&b"X"[..], B{a: 1, b: 2}));
  }

  #[test]
  fn nested_chain() {
    struct TestStruct;
    impl TestStruct {
      fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) }
      fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) }
      method!(f<&TestStruct,&[u8],B>,
        chain_m!(
          chain!(
            tag!("abcd")      ~
            tag!("abcd")?     ,
            || {}
          )                   ~
          aa: self.ret_int1   ~
          tag!("efgh")        ~
          bb: self.ret_int2   ~
          tag!("efgh")        ,
          ||{B{a: aa, b: bb}}
        )
      );
    };

    let t = TestStruct{};
    let r = t.f(&b"abcdabcdefghefghX"[..]);
    assert_eq!(r, Done(&b"X"[..], B{a: 1, b: 2}));

    let r2 = t.f(&b"abcdefghefghX"[..]);
    assert_eq!(r2, Done(&b"X"[..], B{a: 1, b: 2}));
  }

  #[derive(PartialEq,Eq,Debug)]
  struct C {
    a: u8,
    b: Option<u8>
  }

  #[test]
  fn chain_mut() {
    struct TestStruct;
    impl TestStruct {
      fn ret_b1_2(i:&[u8]) -> IResult<&[u8], B> { Done(i,B{a:1,b:2}) }
      method!(f<&TestStruct,&[u8],B>,
        chain_mut!(
          tag!("abcd")     ~
          tag!("abcd")?    ~
          tag!("efgh")     ~
          mut bb: self.ret_b1_2 ~
          tag!("efgh")   ,
          ||{
            bb.b = 3;
            bb
          }
        )
      );
    };

    let t = TestStruct{};
    let r = t.f(&b"abcdabcdefghefghX"[..]);
    assert_eq!(r, Done(&b"X"[..], B{a: 1, b: 3}));
  }

  #[test]
  fn chain_opt() {
    struct TestStruct;
    impl TestStruct {
      method!(y<&TestStruct>, tag!("efgh"));
      fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) }
      method!(ret_y<&TestStruct,&[u8], u8>, map_m!(self.y, |_| 2));

      method!(f<&TestStruct,&[u8],C>,
        chain_m!(
          tag!("abcd") ~
          aa: self.ret_int1 ~
          bb: self.ret_y?   ,
          ||{C{a: aa, b: bb}}
        )
      );
    };

    let t = TestStruct{};
    let r = t.f(&b"abcdefghX"[..]);
    assert_eq!(r, Done(&b"X"[..], C{a: 1, b: Some(2)}));

    let r2 = t.f(&b"abcdWXYZ"[..]);
    assert_eq!(r2, Done(&b"WXYZ"[..], C{a: 1, b: None}));

    let r3 = t.f(&b"abcdX"[..]);
    assert_eq!(r3, Incomplete(Needed::Size(8)));
  }

  use util::{error_to_list, add_error_pattern, print_error};
  use std::collections;

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

  #[test]
  fn err() {
    struct TestStruct;
    impl TestStruct {
      method!(err_test<&TestStruct>, alt!(
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
    };
    let a = &b"efghblah"[..];
    let b = &b"efghijklblah"[..];
    let c = &b"efghijklmnop"[..];

    let blah = &b"blah"[..];
    let t = TestStruct{};
    let res_a = t.err_test(a);
    let res_b = t.err_test(b);
    let res_c = t.err_test(c);
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
    struct TestStruct;
    impl TestStruct {
      method!(err_test<&TestStruct>,
        preceded!(tag!("efgh"), add_error!(ErrorKind::Custom(42),
            chain!(
                   tag!("ijkl")              ~
              res: add_error!(ErrorKind::Custom(128), tag!("mnop")) ,
              || { res }
            )
          )
      ));
    };
    let a = &b"efghblah"[..];
    let b = &b"efghijklblah"[..];
    let c = &b"efghijklmnop"[..];

    let blah = &b"blah"[..];

    let t = TestStruct{};
    let res_a = t.err_test(a);
    let res_b = t.err_test(b);
    let res_c = t.err_test(c);
    assert_eq!(res_a, Error(NodePosition(ErrorKind::Custom(42), blah, Box::new(Position(ErrorKind::Tag, blah)))));
    assert_eq!(res_b, Error(NodePosition(ErrorKind::Custom(42), &b"ijklblah"[..], Box::new(NodePosition(ErrorKind::Custom(128), blah, Box::new(Position(ErrorKind::Tag, blah)))))));
    assert_eq!(res_c, Done(&b""[..], &b"mnop"[..]));
  }

  #[test]
  fn complete() {
    struct TestStruct;
    impl TestStruct {
      method!(err_test<&TestStruct>,
        chain!(
               tag!("ijkl")              ~
          res: complete!(tag!("mnop")) ,
          || { res }
        )
      );
    };
    let a = &b"ijklmn"[..];

    let t = TestStruct{};
    let res_a = t.err_test(a);
    assert_eq!(res_a, Error(Position(ErrorKind::Complete, &b"mn"[..])));
  }

  #[test]
  fn alt() {
    struct TestStruct;
    impl TestStruct {
      fn work(&self, input: &[u8]) -> IResult<&[u8],&[u8], &'static str> {
        Done(&b""[..], input)
      }

      #[allow(unused_variables)]
      fn dont_work(&self, input: &[u8]) -> IResult<&[u8],&[u8],&'static str> {
        Error(Code(ErrorKind::Custom("abcd")))
      }

      fn work2(&self, input: &[u8]) -> IResult<&[u8],&[u8], &'static str> {
        Done(input, &b""[..])
      }

      fn alt1(&self, i:&[u8]) ->  IResult<&[u8],&[u8], &'static str> {
        alt_m!(i, self.dont_work | self.dont_work)
      }
      fn alt2(&self, i:&[u8]) ->  IResult<&[u8],&[u8], &'static str> {
        alt_m!(i, self.dont_work | self.work)
      }
      fn alt3(&self, i:&[u8]) ->  IResult<&[u8],&[u8], &'static str> {
        alt_m!(i, self.dont_work | self.dont_work | self.work2 | self.dont_work)
      }

      method!(alt4<&TestStruct>, alt!(tag!("abcd") | tag!("efgh")));
      method!(alt5<&TestStruct,bool>, alt!(tag!("abcd") => { |_| false } | tag!("efgh") => { |_| true }));
    };
    //named!(alt1, alt!(dont_work | dont_work));
    //named!(alt2, alt!(dont_work | work));
    //named!(alt3, alt!(dont_work | dont_work | work2 | dont_work));

    let t = TestStruct{};
    let a = &b"abcd"[..];
    assert_eq!(t.alt1(a), Error(Position(ErrorKind::Alt, a)));
    assert_eq!(t.alt2(a), Done(&b""[..], a));
    assert_eq!(t.alt3(a), Done(a, &b""[..]));

    let b = &b"efgh"[..];
    assert_eq!(t.alt4(a), Done(&b""[..], a));
    assert_eq!(t.alt4(b), Done(&b""[..], b));

    // test the alternative syntax
    assert_eq!(t.alt5(a), Done(&b""[..], false));
    assert_eq!(t.alt5(b), Done(&b""[..], true));

  }

  #[test]
  fn alt_incomplete() {
    struct TestStruct;
    impl TestStruct {
      method!(alt1<&TestStruct>, alt!(tag!("a") | tag!("bc") | tag!("def")));
    };

    let t = TestStruct{};
    let a = &b""[..];
    assert_eq!(t.alt1(a), Incomplete(Needed::Size(1)));
    let a = &b"b"[..];
    assert_eq!(t.alt1(a), Incomplete(Needed::Size(2)));
    let a = &b"bcd"[..];
    assert_eq!(t.alt1(a), Done(&b"d"[..], &b"bc"[..]));
    let a = &b"cde"[..];
    assert_eq!(t.alt1(a), Error(Position(ErrorKind::Alt, a)));
    let a = &b"de"[..];
    assert_eq!(t.alt1(a), Incomplete(Needed::Size(3)));
    let a = &b"defg"[..];
    assert_eq!(t.alt1(a), Done(&b"g"[..], &b"def"[..]));
  }

  #[test]
  fn switch() {
    struct TestStruct;
    impl TestStruct {
      method!(sw<&TestStruct>,
        switch!(take!(4),
          b"abcd" => take!(2) |
          b"efgh" => take!(4)
        )
      );
    };

    let t = TestStruct{};
    let a = &b"abcdefgh"[..];
    assert_eq!(t.sw(a), Done(&b"gh"[..], &b"ef"[..]));

    let b = &b"efghijkl"[..];
    assert_eq!(t.sw(b), Done(&b""[..], &b"ijkl"[..]));
    let c = &b"afghijkl"[..];
    assert_eq!(t.sw(c), Error(Position(ErrorKind::Switch, &b"afghijkl"[..])));
  }

  #[test]
  fn opt() {
    struct TestStruct;
    impl TestStruct {
      method!(o<&TestStruct,&[u8],Option<&[u8]> >, opt!(tag!("abcd")));
    };

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    assert_eq!(t.o(a), Done(&b"ef"[..], Some(&b"abcd"[..])));
    assert_eq!(t.o(b), Done(&b"bcdefg"[..], None));
  }

  #[test]
  fn opt_res() {
    struct TestStruct;
    impl TestStruct {
      named!(o<&TestStruct,&[u8], Result<&[u8], Err<&[u8]>> >, opt_res!(tag!("abcd")));
    };

    let t = TestStruct{};
    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    assert_eq!(t.o(a), Done(&b"ef"[..], Ok(&b"abcd"[..])));
    assert_eq!(t.o(b), Done(&b"bcdefg"[..], Err(Position(ErrorKind::Tag, b))));
  }

  // #[test]
  // fn cond() {
  //   let b = true;
  //   let f: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> = Box::new(closure!(&'static [u8], cond!( b, tag!("abcd") ) ));

  //   let a = b"abcdef";
  //   assert_eq!(f(&a[..]), Done(&b"ef"[..], Some(&b"abcd"[..])));

  //   let b2 = false;
  //   let f2: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> = Box::new(closure!(&'static [u8], cond!( b2, tag!("abcd") ) ));
  //   //let f2 = closure!(&'static [u8], cond!( b2, tag!("abcd") ) );

  //   assert_eq!(f2(&a[..]), Done(&b"abcdef"[..], None));
  // }

  #[test]
  fn cond_wrapping() {
    struct TestStruct;
    impl TestStruct {

    // Test that cond!() will wrap a given identifier in the call!() macro.

      method!(silly<&TestStruct>, tag!("foo"));
    };

    let t = TestStruct{};
    let b = true;
    //let f = closure!(&'static [u8], cond!( b, silly ) );
    let f: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> = Box::new(closure!(&'static [u8], cond_m!( b, t.silly ) ));
    assert_eq!(f(b"foobar"), Done(&b"bar"[..], Some(&b"foo"[..])));
  }

  #[test]
  fn peek() {
    struct TestStruct;
    impl TestStruct {
      method!(ptag<&TestStruct,&[u8],&[u8]>, peek!(tag!("abcd")));
    };

    let t = TestStruct{};
    let r1 = t.ptag(&b"abcdefgh"[..]);
    assert_eq!(r1, Done(&b"abcdefgh"[..], &b"abcd"[..]));

    let r1 = t.ptag(&b"efgh"[..]);
    assert_eq!(r1, Error(Position(ErrorKind::Tag,&b"efgh"[..])));
  }

  #[test]
  fn pair() {
    struct TestStruct;
    impl TestStruct {
      method!(p<&TestStruct,&[u8],(&[u8], &[u8])>, pair!(tag!("abcd"), tag!("efgh")));
    };

    let t = TestStruct{};

    let r1 = p(&b"abcdefghijkl"[..]);
    assert_eq!(r1, Done(&b"ijkl"[..], (&b"abcd"[..], &b"efgh"[..])));
  }

  #[test]
  fn separated_pair() {
    struct TestStruct;
    impl TestStruct {
      method!(p<&TestStruct,&[u8],(&[u8], &[u8])>, separated_pair!(tag!("abcd"), tag!(","), tag!("efgh")));
    };

    let t = TestStruct{};

    let r1 = t.p(&b"abcd,efghijkl"[..]);
    assert_eq!(r1, Done(&b"ijkl"[..], (&b"abcd"[..], &b"efgh"[..])));
  }

  #[test]
  fn preceded() {
    struct TestStruct;
    impl TestStruct {
      method!(p<&TestStruct,&[u8], &[u8]>, preceded!(tag!("abcd"), tag!("efgh")));
    };

    let t = TestStruct{};

    let r1 = t.p(&b"abcdefghijkl"[..]);
    assert_eq!(r1, Done(&b"ijkl"[..], &b"efgh"[..]));
  }

  #[test]
  fn terminated() {
    struct TestStruct;
    impl TestStruct {
      method!(p<&TestStruct,&[u8], &[u8]>, terminated!(tag!("abcd"), tag!("efgh")));
    };

    let t = TestStruct{};

    let r1 = t.p(&b"abcdefghijkl"[..]);
    assert_eq!(r1, Done(&b"ijkl"[..], &b"abcd"[..]));
  }

  #[test]
  fn delimited() {
    struct TestStruct;
    impl TestStruct {
      method!(p<&TestStruct,&[u8], &[u8]>, delimited!(tag!("abcd"), tag!("efgh"), tag!("ij")));
    };

    let t = TestStruct{};

    let r1 = t.p(&b"abcdefghijkl"[..]);
    assert_eq!(r1, Done(&b"kl"[..], &b"efgh"[..]));
  }

    #[test]
  fn separated_list() {
    struct TestStruct;
    impl TestStruct {
      method!(multi<&TestStruct,&[u8],Vec<&[u8]> >, separated_list!(tag!(","), tag!("abcd")));
    };

    let t = TestStruct{};

    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"azerty"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(t.multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(t.multi(b), Done(&b"ef"[..], res2));
    assert_eq!(t.multi(c), Done(&b"azerty"[..], Vec::new()));
  }

  #[test]
  fn separated_nonempty_list() {
    struct TestStruct;
    impl TestStruct {
      method!(multi<&TestStruct,&[u8],Vec<&[u8]> >, separated_nonempty_list!(tag!(","), tag!("abcd")));
    };

    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"azerty"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(t.multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(t.multi(b), Done(&b"ef"[..], res2));
    assert_eq!(t.multi(c), Error(Position(ErrorKind::Tag,c)));
  }

  #[test]
  fn many0() {
    struct TestStruct;
    impl TestStruct {
      method!(multi<&[u8],Vec<&[u8]> >, many0!(tag!("abcd")));
    };

    let a = &b"abcdef"[..];
    let b = &b"abcdabcdefgh"[..];
    let c = &b"azerty"[..];
    let d = &b"abcdab"[..];

    //let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Incomplete(Needed::Size(8)));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res2));
    assert_eq!(multi(c), Done(&b"azerty"[..], Vec::new()));
    assert_eq!(multi(d), Incomplete(Needed::Size(8)));
  }

  #[cfg(feature = "nightly")]
  use test::Bencher;

  #[cfg(feature = "nightly")]
  #[bench]
  fn many0_bench(b: &mut Bencher) {
    struct TestStruct;
    impl TestStruct {
      method!(multi<&TestStruct,&[u8],Vec<&[u8]> >, many0!(tag!("abcd")));
    };
    let t = TestStruct{};
    b.iter(|| {
      t.multi(&b"abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"[..])
    });
  }

  #[test]
  fn many1() {
    struct TestStruct;
    impl TestStruct {
      method!(multi<&TestStruct,&[u8],Vec<&[u8]> >, many1!(tag!("abcd")));
    };

    let a = &b"abcdef"[..];
    let b = &b"abcdabcdefgh"[..];
    let c = &b"azerty"[..];
    let d = &b"abcdab"[..];

    let t = TestStruct{};
    //let res1 = vec![&b"abcd"[..]];
    assert_eq!(t.multi(a), Incomplete(Needed::Size(8)));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(t.multi(b), Done(&b"efgh"[..], res2));
    assert_eq!(t.multi(c), Error(Position(ErrorKind::Many1,c)));
    assert_eq!(t.multi(d), Incomplete(Needed::Size(8)));
  }

  #[test]
  fn infinite_many() {
    struct TestStruct;
    impl TestStruct {
      fn tst(input: &[u8]) -> IResult<&[u8], &[u8]> {
        println!("input: {:?}", input);
        Error(Position(ErrorKind::Custom(0),input))
      }

      // should not go into an infinite loop
      method!(multi0<&TestStruct,&[u8],Vec<&[u8]> >, many0!(tst));
      method!(multi1<&TestStruct,&[u8],Vec<&[u8]> >, many1!(tst));
    };
    let t = TestStruct{};
    let a = &b"abcdef"[..];
    assert_eq!(t.multi0(a), Done(a, Vec::new()));

    let a = &b"abcdef"[..];
    assert_eq!(t.multi1(a), Error(Position(ErrorKind::Many1,a)));
  }

  #[test]
  fn many_m_n() {
    struct TestStruct;
    impl TestStruct {
      method!(multi<&TestStruct,&[u8],Vec<&[u8]> >, many_m_n!(2, 4, tag!("Abcd")));
    };

    let a = &b"Abcdef"[..];
    let b = &b"AbcdAbcdefgh"[..];
    let c = &b"AbcdAbcdAbcdAbcdefgh"[..];
    let d = &b"AbcdAbcdAbcdAbcdAbcdefgh"[..];
    let e = &b"AbcdAb"[..];

    let t = TestStruct{};
    //let res1 = vec![&b"abcd"[..]];
    assert_eq!(t.multi(a), Incomplete(Needed::Size(8)));
    let res2 = vec![&b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(t.multi(b), Done(&b"efgh"[..], res2));
    let res3 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(t.multi(c), Done(&b"efgh"[..], res3));
    let res4 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(t.multi(d), Done(&b"Abcdefgh"[..], res4));
    assert_eq!(t.multi(e), Incomplete(Needed::Size(8)));
  }

  #[test]
  fn count() {
    struct TestStruct;
    impl TestStruct {
      fn counter(input: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
        let size: usize = 2;
        count!(input, tag!( "abcd" ), size )
      }
    };

    let t = TestStruct{};
    let a = b"abcdabcdabcdef";
    let b = b"abcdefgh";
    let res = vec![&b"abcd"[..], &b"abcd"[..]];

    assert_eq!(t.counter(&a[..]), Done(&b"abcdef"[..], res));
    assert_eq!(t.counter(&b[..]), Error(Position(ErrorKind::Count, &b[..])));
  }

  #[test]
  fn count_zero() {
    struct TestStruct;
    impl TestStruct {
      fn counter(input: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
        let size: usize = 0;
        count!(input, tag!( "abcd" ), size )
      }
    };

    let t = TestStruct{};
    let a = b"abcdabcdabcdef";
    let res: Vec<&[u8]> = Vec::new();

    assert_eq!(t.counter(&a[..]), Done(&b"abcdabcdabcdef"[..], res));
  }

  #[test]
  fn count_fixed() {
    struct TestStruct;
    impl TestStruct {
      //named!(counter< [&[u8]; 2], u32 >, count_fixed!( &[u8], tag!( "abcd" ), 2 ) );
      fn counter(input:&[u8]) -> IResult<&[u8], [&[u8]; 2], () > {
        count_fixed!(input, &[u8], tag!( "abcd" ), 2 )
      }
    };

    let t = TestStruct{};
    let a = b"abcdabcdabcdef";
    let b = b"abcdefgh";
    let res = [&b"abcd"[..], &b"abcd"[..]];

    assert_eq!(t.counter(&a[..]), Done(&b"abcdef"[..], res));
    assert_eq!(t.counter(&b[..]), Error(Position(ErrorKind::Count, &b[..])));
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
    struct TestStruct;
    impl TestStruct {
      //named!(counter< [&[u8]; 2], u32 >, count_fixed!( &[u8], tag!( "abcd" ), 2 ) );
      fn counter(input:&[u8]) -> IResult<&[u8], [&[u8]; 2], () > {
        count_fixed!(input, &[u8], tag!( "abcd" ), 2 )
      }
    };

    let t = TestStruct{};
    let a = b"abcdabcdabcdef";
    let b = b"abcdefgh";
    let res = [&b"abcd"[..], &b"abcd"[..]];

    assert_eq!(t.counter(&a[..]), Done(&b"abcdef"[..], res));
    assert_eq!(t.counter(&b[..]), Error(Position(ErrorKind::Count, &b[..])));
  }

  use nom::{be_u8,be_u16};
  #[test]
  fn length_value_test() {
    struct TestStruct;
    impl TestStruct {
      method!(tst1<&TestStruct,&[u8], Vec<u16> >, length_value!(be_u8, be_u16));
      method!(tst2<&TestStruct,&[u8], Vec<u16> >, length_value!(be_u8, be_u16, 2));
    };

    let t = TestStruct{};
    let i1 = vec![0, 5, 6];
    let i2 = vec![1, 5, 6, 3];
    let i3 = vec![2, 5, 6, 3];
    let i4 = vec![2, 5, 6, 3, 4, 5, 7];
    let i5 = vec![3, 5, 6, 3, 4, 5];

    let r1: Vec<u16> = Vec::new();
    let r2: Vec<u16> = vec![1286];
    let r4: Vec<u16> = vec![1286, 772];
    assert_eq!(t.tst1(&i1), IResult::Done(&i1[1..], r1));
    assert_eq!(t.tst1(&i2), IResult::Done(&i2[3..], r2));
    assert_eq!(t.tst1(&i3), IResult::Incomplete(Needed::Size(5)));
    assert_eq!(t.tst1(&i4), IResult::Done(&i4[5..], r4));
    assert_eq!(t.tst1(&i5), IResult::Incomplete(Needed::Size(7)));

    let r6: Vec<u16> = Vec::new();
    let r7: Vec<u16> = vec![1286];
    let r9: Vec<u16> = vec![1286, 772];
    assert_eq!(t.tst2(&i1), IResult::Done(&i1[1..], r6));
    assert_eq!(t.tst2(&i2), IResult::Done(&i2[3..], r7));
    assert_eq!(t.st2(&i3), IResult::Incomplete(Needed::Size(5)));
    assert_eq!(t.tst2(&i4), IResult::Done(&i4[5..], r9));
    assert_eq!(t.tst1(&i5), IResult::Incomplete(Needed::Size(7)));
  }

  #[test]
  fn chain_incomplete() {
    struct TestStruct;
    impl TestStruct {
      fn res() -> IResult<&[u8], &[u8]> {
        chain!(&b"abcdefgh"[..],
          a: take!(4) ~
          b: take!(8),
          ||{(a,b )}
        )
      }
    };

    let t = TestStruct{};
    assert_eq!(t.res(), IResult::Incomplete(Needed::Size(12)));
  }
}
