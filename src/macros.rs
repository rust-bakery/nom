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
//! ```
#[allow(unused_variables)]

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
    (#$($args:tt)*) => (
        named_attr!(#$($args)*);
    );
    ($name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        fn $name( i: $i ) -> $crate::IResult<$i,$o,u32> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$i:ty,$o:ty,$e:ty>, $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        fn $name( i: $i ) -> $crate::IResult<$i, $o, $e> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        fn $name( i: $i ) -> $crate::IResult<$i, $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        fn $name<'a>( i: &'a[u8] ) -> $crate::IResult<&'a [u8], $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    ($name:ident, $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        fn $name( i: &[u8] ) -> $crate::IResult<&[u8], &[u8], u32> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        pub fn $name( i: $i ) -> $crate::IResult<$i,$o, u32> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$i:ty,$o:ty,$e:ty>, $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        pub fn $name( i: $i ) -> $crate::IResult<$i, $o, $e> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        pub fn $name( i: $i ) -> $crate::IResult<$i, $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        pub fn $name( i: &[u8] ) -> $crate::IResult<&[u8], $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    (pub $name:ident, $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        pub fn $name<'a>( i: &'a [u8] ) -> $crate::IResult<&[u8], &[u8], u32> {
            $submac!(i, $($args)*)
        }
    );
);

/// Makes a function from a parser combination with arguments.
#[macro_export]
macro_rules! named_args {
    (pub $func_name:ident ( $( $arg:ident : $typ:ty ),* ) < $return_type:ty > , $submac:ident!( $($args:tt)* ) ) => {
        pub fn $func_name(input: &[u8], $( $arg : $typ ),*) -> $crate::IResult<&[u8], $return_type> {
            $submac!(input, $($args)*)
        }
    };
    (pub $func_name:ident < 'a > ( $( $arg:ident : $typ:ty ),* ) < $return_type:ty > , $submac:ident!( $($args:tt)* ) ) => {
        pub fn $func_name<'this_is_probably_unique_i_hope_please, 'a>(input: &'this_is_probably_unique_i_hope_please [u8], $( $arg : $typ ),*) -> $crate::IResult<&'this_is_probably_unique_i_hope_please [u8], $return_type> {
            $submac!(input, $($args)*)
        }
    };
    ($func_name:ident ( $( $arg:ident : $typ:ty ),* ) < $return_type:ty > , $submac:ident!( $($args:tt)* ) ) => {
        fn $func_name(input: &[u8], $( $arg : $typ ),*) -> $crate::IResult<&[u8], $return_type> {
            $submac!(input, $($args)*)
        }
    };
    ($func_name:ident < 'a > ( $( $arg:ident : $typ:ty ),* ) < $return_type:ty > , $submac:ident!( $($args:tt)* ) ) => {
        fn $func_name<'this_is_probably_unique_i_hope_please, 'a>(input: &'this_is_probably_unique_i_hope_please [u8], $( $arg : $typ ),*) -> $crate::IResult<&'this_is_probably_unique_i_hope_please [u8], $return_type> {
            $submac!(input, $($args)*)
        }
    };
}

/// Makes a function from a parser combination, with attributes
///
/// The usage of this macro is almost identical to `named!`, except that
/// you also pass attributes to be attached to the generated function.
/// This is ideal for adding documentation to your parser.
///
/// ```ignore
/// // Create my_function as if you wrote it with the doc comment /// My Func
/// named_attr!(#[doc = "My Func"], my_function( &[u8] ) -> &[u8], tag!("abcd"));
/// // Also works for pub functions, and multiple lines
/// named!(#[doc = "My Func\nRecognise abcd"], pub my_function, tag!("abcd"));
/// // Multiple attributes can be passed if required
/// named!(#[doc = "My Func"] #[inline(always)], pub my_function, tag!("abcd"));
/// ```
#[macro_export]
macro_rules! named_attr (
    ($(#[$attr:meta])*, $name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        $(#[$attr])*
        fn $name( i: $i ) -> $crate::IResult<$i,$o,u32> {
            $submac!(i, $($args)*)
        }
    );
    ($(#[$attr:meta])*, $name:ident<$i:ty,$o:ty,$e:ty>, $submac:ident!( $($args:tt)* )) => (
        $(#[$attr])*
        fn $name( i: $i ) -> $crate::IResult<$i, $o, $e> {
            $submac!(i, $($args)*)
        }
    );
    ($(#[$attr:meta])*, $name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        $(#[$attr])*
        fn $name( i: $i ) -> $crate::IResult<$i, $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    ($(#[$attr:meta])*, $name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
        $(#[$attr])*
        fn $name<'a>( i: &'a[u8] ) -> $crate::IResult<&'a [u8], $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    ($(#[$attr:meta])*, $name:ident, $submac:ident!( $($args:tt)* )) => (
        $(#[$attr])*
        fn $name( i: &[u8] ) -> $crate::IResult<&[u8], &[u8], u32> {
            $submac!(i, $($args)*)
        }
    );
    ($(#[$attr:meta])*, pub $name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        $(#[$attr])*
        pub fn $name( i: $i ) -> $crate::IResult<$i,$o, u32> {
            $submac!(i, $($args)*)
        }
    );
    ($(#[$attr:meta])*, pub $name:ident<$i:ty,$o:ty,$e:ty>, $submac:ident!( $($args:tt)* )) => (
        $(#[$attr])*
        pub fn $name( i: $i ) -> $crate::IResult<$i, $o, $e> {
            $submac!(i, $($args)*)
        }
    );
    ($(#[$attr:meta])*, pub $name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        $(#[$attr])*
        pub fn $name( i: $i ) -> $crate::IResult<$i, $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    ($(#[$attr:meta])*, pub $name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
        $(#[$attr])*
        pub fn $name( i: &[u8] ) -> $crate::IResult<&[u8], $o, u32> {
            $submac!(i, $($args)*)
        }
    );
    ($(#[$attr:meta])*, pub $name:ident, $submac:ident!( $($args:tt)* )) => (
        $(#[$attr])*
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
///   named!(parser, call!(take_wrapper, 2));
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
/// If another `return_error!` combinator is present in the parent
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
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::{Position,NodePosition};
/// # use nom::ErrorKind;
/// # fn main() {
///     named!(err_test, alt!(
///       tag!("abcd") |
///       preceded!(tag!("efgh"), return_error!(ErrorKind::Custom(42),
///           do_parse!(
///                  tag!("ijkl")                                        >>
///             res: return_error!(ErrorKind::Custom(128), tag!("mnop")) >>
///             (res)
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
///     assert_eq!(res_a, Error(error_node_position!(ErrorKind::Custom(42), blah, error_position!(ErrorKind::Tag, blah))));
///     assert_eq!(res_b, Error(error_node_position!(ErrorKind::Custom(42), &b"ijklblah"[..],
///       error_node_position!(ErrorKind::Custom(128), blah, error_position!(ErrorKind::Tag, blah))))
///     );
/// # }
/// ```
///
#[macro_export]
macro_rules! return_error (
  ($i:expr, $code:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let i_ = $i.clone();
      let cl = || {
        $submac!(i_, $($args)*)
      };

      match cl() {
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
        $crate::IResult::Error(e)      => {
          return $crate::IResult::Error(error_node_position!($code, $i, e))
        }
      }
    }
  );
  ($i:expr, $code:expr, $f:expr) => (
    return_error!($i, $code, call!($f));
  );
);

/// Add an error if the child parser fails
///
/// While error! does an early return and avoids backtracking,
/// add_return_error! backtracks normally. It just provides more context
/// for an error
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use std::collections;
/// # use nom::IResult::Error;
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::{Position,NodePosition};
/// # use nom::ErrorKind;
/// # fn main() {
///     named!(err_test, add_return_error!(ErrorKind::Custom(42), tag!("abcd")));
///
///     let a = &b"efghblah"[..];
///     let res_a = err_test(a);
///     assert_eq!(res_a, Error(error_node_position!(ErrorKind::Custom(42), a, error_position!(ErrorKind::Tag, a))));
/// # }
/// ```
///
#[macro_export]
macro_rules! add_return_error (
  ($i:expr, $code:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
        $crate::IResult::Error(e)      => {
          $crate::IResult::Error(error_node_position!($code, $i, e))
        }
      }
    }
  );
  ($i:expr, $code:expr, $f:expr) => (
    add_return_error!($i, $code, call!($f));
  );
);

/// replaces a `Incomplete` returned by the child parser
/// with an `Error`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use std::collections;
/// # use nom::IResult::Error;
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::{Position,NodePosition};
/// # use nom::ErrorKind;
/// # fn main() {
///     named!(take_5, complete!(take!(5)));
///
///     let a = &b"abcd"[..];
///     let res_a = take_5(a);
///     assert_eq!(res_a,  Error(error_position!(ErrorKind::Complete, a)));
/// # }
/// ```
///
#[macro_export]
macro_rules! complete (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        $crate::IResult::Done(i, o)    => $crate::IResult::Done(i, o),
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete(_) =>  {
          $crate::IResult::Error(error_position!($crate::ErrorKind::Complete, $i))
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
/// this can provide more flexibility than `do_parse!` if needed
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Error};
/// # #[cfg(feature = "verbose-errors")]
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
/// assert_eq!(r1, Error(error_position!(ErrorKind::ExprOpt,&[2,3,4,5][..])));
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

/// `map!(I -> IResult<I,O>, O -> P) => I -> IResult<I, P>`
/// maps a function on the result of a parser
#[macro_export]
macro_rules! map(
  // Internal parser, do not use directly
  (__impl $i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    {
      pub fn _unify<T, R, F: FnOnce(T) -> R>(f: F, t: T) -> R {
       f(t)
      }
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done(i, o)                          => $crate::IResult::Done(i, _unify($g, o))
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    map!(__impl $i, $submac!($($args)*), $g);
  );
  ($i:expr, $f:expr, $g:expr) => (
    map!(__impl $i, call!($f), $g);
  );
);

/// `map_res!(I -> IResult<I,O>, O -> Result<P>) => I -> IResult<I, P>`
/// maps a function returning a Result on the output of a parser
#[macro_export]
macro_rules! map_res (
  // Internal parser, do not use directly
  (__impl $i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done(i, o)                          => match $submac2!(o, $($args2)*) {
          Ok(output) => $crate::IResult::Done(i, output),
          Err(_)     => $crate::IResult::Error(error_position!($crate::ErrorKind::MapRes, $i))
        }
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    map_res!(__impl $i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    map_res!(__impl $i, $submac!($($args)*), $submac2!($($args2)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    map_res!(__impl $i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    map_res!(__impl $i, call!($f), $submac!($($args)*));
  );
);

/// `map_opt!(I -> IResult<I,O>, O -> Option<P>) => I -> IResult<I, P>`
/// maps a function returning an Option on the output of a parser
#[macro_export]
macro_rules! map_opt (
  // Internal parser, do not use directly
  (__impl $i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done(i, o)                          => match $submac2!(o, $($args2)*) {
          ::std::option::Option::Some(output) => $crate::IResult::Done(i, output),
          ::std::option::Option::None         => $crate::IResult::Error(error_position!($crate::ErrorKind::MapOpt, $i))
        }
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    map_opt!(__impl $i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    map_opt!(__impl $i, $submac!($($args)*), $submac2!($($args2)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    map_opt!(__impl $i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    map_opt!(__impl $i, call!($f), $submac!($($args)*));
  );
);

/// `parse_to!(O) => I -> IResult<I, O>`
/// uses the `parse` method from `std::str::FromStr` to convert the current
/// input to the specified type
///
/// this will completely consume the input
#[macro_export]
macro_rules! parse_to (
  ($i:expr, $t:ty ) => (
    {
      use $crate::ParseTo;
      use $crate::Slice;
      use $crate::InputLength;
      match ($i).parse_to() {
        ::std::option::Option::Some(output) => $crate::IResult::Done($i.slice(..$i.input_len()), output),
        ::std::option::Option::None         => $crate::IResult::Error(error_position!($crate::ErrorKind::MapOpt, $i))
      }
    }
  );
);

/// `verify!(I -> IResult<I,O>, O -> bool) => I -> IResult<I, O>`
/// returns the result of the child parser if it satisfies a verification function
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # use nom::be_u32;
/// # fn main() {
///  named!(check<u32>, verify!(be_u32, |val:u32| val >= 0 && val < 3));
/// # }
/// ```
#[macro_export]
macro_rules! verify (
  // Internal parser, do not use directly
  (__impl $i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done(i, o)                          => if $submac2!(o, $($args2)*) {
          $crate::IResult::Done(i, o)
        } else {
          $crate::IResult::Error(error_position!($crate::ErrorKind::Verify, $i))
        }
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    verify!(__impl $i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    verify!(__impl $i, $submac!($($args)*), $submac2!($($args2)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    verify!(__impl $i, call!($f), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    verify!(__impl $i, call!($f), $submac!($($args)*));
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
          let res: $crate::IResult<_,_> = $crate::IResult::Done(i, $res);
          res
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
    {
      let res: $crate::IResult<_,_> = $crate::IResult::Done($i, $res);
      res
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
        Err(_)     => $crate::IResult::Error(error_position!($crate::ErrorKind::ExprRes, $i))
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
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::{be_u8,ErrorKind};
///
///  fn take_add(input:&[u8], size: u8) -> IResult<&[u8],&[u8]> {
///    do_parse!(input,
///      sz:     be_u8                             >>
///      length: expr_opt!(size.checked_add(sz))   >> // checking for integer overflow (returns an Option)
///      data:   take!(length)                     >>
///      (data)
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
/// assert_eq!(r1, Error(error_position!(ErrorKind::ExprOpt,&[2,3,4,5][..])));
/// # }
/// ```
#[macro_export]
macro_rules! expr_opt (
  ($i:expr, $e:expr) => (
    {
      match $e {
        ::std::option::Option::Some(output) => $crate::IResult::Done($i, output),
        ::std::option::Option::None         => $crate::IResult::Error(error_position!($crate::ErrorKind::ExprOpt, $i))
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
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, ::std::option::Option::Some(o)),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        _                              => {
          let res: $crate::IResult<_,_> = $crate::IResult::Done($i, ::std::option::Option::None);
          res
        },
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
/// ```ignore
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!( o<&[u8], Result<&[u8], nom::Err<&[u8]> > >, opt_res!( tag!( "abcd" ) ) );
///
///  let a = b"abcdef";
///  let b = b"bcdefg";
///  assert_eq!(o(&a[..]), Done(&b"ef"[..], Ok(&b"abcd"[..])));
///  assert_eq!(o(&b[..]), Done(&b"bcdefg"[..], Err(error_position!(ErrorKind::Tag, &b[..]))));
///  # }
/// ```
#[macro_export]
macro_rules! opt_res (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,  ::std::result::Result::Ok(o)),
        $crate::IResult::Error(e)      => $crate::IResult::Done($i, ::std::result::Result::Err(e)),
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
/// on the value returned by a preceding parser in
/// a `do_parse!`.
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
        let res: $crate::IResult<_,_> = $crate::IResult::Done($i, ::std::option::Option::None);
        res
      }
    }
  );
  ($i:expr, $cond:expr, $f:expr) => (
    cond_with_error!($i, $cond, call!($f));
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
/// on the value returned by a preceding parser in
/// a `do_parse!`.
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
        let i_ = $i.clone();
        match $submac!(i_, $($args)*) {
          $crate::IResult::Done(i,o)     => $crate::IResult::Done(i, ::std::option::Option::Some(o)),
          $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
          $crate::IResult::Error(_)      => {
            let res: $crate::IResult<_,_> = $crate::IResult::Done($i, ::std::option::Option::None);
            res
          },
        }
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Done($i, ::std::option::Option::None);
        res
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
/// on the value returned by a preceding parser in
/// a `do_parse!`.
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
///  assert_eq!(f2(&a[..]), Error(error_position!(ErrorKind::CondReduce, &a[..])));
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
        $crate::IResult::Error(error_position!($crate::ErrorKind::CondReduce, $i))
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
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
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

/// `not!(I -> IResult<I,O>) => I -> IResult<I, O>`
/// returns a result only if the embedded parser returns Error or Incomplete
/// does not consume the input
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
/// named!(not_e, do_parse!(
///     res: tag!("abc")      >>
///          not!(char!('e')) >>
///     (res)
/// ));
///
/// let r = not_e(&b"abcd"[..]);
/// assert_eq!(r, Done(&b"d"[..], &b"abc"[..]));
///
/// let r2 = not_e(&b"abce"[..]);
/// assert_eq!(r2, Error(error_position!(ErrorKind::Not, &b"e"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! not(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::Slice;
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        $crate::IResult::Done(_, _)    => $crate::IResult::Error(error_position!($crate::ErrorKind::Not, $i)),
        $crate::IResult::Error(_)      => $crate::IResult::Done($i, ($i).slice(..0)),
        $crate::IResult::Incomplete(_) => $crate::IResult::Done($i, ($i).slice(..0))
      }
    }
  );
  ($i:expr, $f:expr) => (
    not!($i, call!($f));
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

/// `eof!()` returns its input if it is at the end of input data
///
/// please note that for now, eof only means there's no more
/// data available, it does not work yet with smarter input
/// types
#[macro_export]
macro_rules! eof (
  ($i:expr,) => (
    {
      use $crate::InputLength;
      if ($i).input_len() == 0 {
        $crate::IResult::Done($i, $i)
      } else {
        $crate::IResult::Error(error_position!($crate::ErrorKind::Eof, $i))
      }
    }
  );
);

/// `recognize!(I -> IResult<I, O> ) => I -> IResult<I, I>`
/// if the child parser was successful, return the consumed input as produced value
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(x, recognize!(delimited!(tag!("<!--"), take!(5), tag!("-->"))));
///  let r = x(&b"<!-- abc --> aaa"[..]);
///  assert_eq!(r, Done(&b" aaa"[..], &b"<!-- abc -->"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! recognize (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::Offset;
      use $crate::Slice;
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        $crate::IResult::Done(i,_)     => {
          let index = (&$i).offset(&i);
          $crate::IResult::Done(i, ($i).slice(..index))
        },
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i)
      }
    }
  );
  ($i:expr, $f:expr) => (
    recognize!($i, call!($f))
  );
);


#[cfg(test)]
mod tests {
  use internal::{Needed,IResult};
  #[cfg(feature = "verbose-errors")]
  use verbose_errors::Err;

  #[cfg(not(feature = "verbose-errors"))]
  use simple_errors::Err;

  use internal::IResult::*;
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
          $crate::IResult::Error(error_position!($crate::ErrorKind::Tag, $i))
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

  #[cfg(feature = "verbose-errors")]
  #[test]
  fn opt_res() {
    named!(opt_res_abcd<&[u8], Result<&[u8], Err<&[u8]> > >, opt_res!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    let c = &b"ab"[..];
    assert_eq!(opt_res_abcd(a), Done(&b"ef"[..], Ok(&b"abcd"[..])));
    assert_eq!(opt_res_abcd(b), Done(&b"bcdefg"[..], Err(error_position!(ErrorKind::Tag, b))));
    assert_eq!(opt_res_abcd(c), Incomplete(Needed::Size(4)));
  }

  #[cfg(not(feature = "verbose-errors"))]
  #[test]
  fn opt_res() {
    named!(opt_res_abcd<&[u8], Result<&[u8], Err<u32>> >, opt_res!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    let c = &b"ab"[..];
    assert_eq!(opt_res_abcd(a), Done(&b"ef"[..], Ok(&b"abcd"[..])));
    assert_eq!(opt_res_abcd(b), Done(&b"bcdefg"[..], Err(error_position!(ErrorKind::Tag, b))));
    assert_eq!(opt_res_abcd(c), Incomplete(Needed::Size(4)));
  }

  #[test]
  #[cfg(feature = "std")]
  fn cond() {
    let f_true: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>>  =
      Box::new(closure!(&'static [u8], fix_error!(&str, cond!( true, tag!("abcd") ) )));
    let f_false: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> =
      Box::new(closure!(&'static [u8], fix_error!(&str, cond!( false, tag!("abcd") ) )));
    //let f_false = closure!(&'static [u8], cond!( false, tag!("abcd") ) );

    assert_eq!(f_true(&b"abcdef"[..]), Done(&b"ef"[..], Some(&b"abcd"[..])));
    assert_eq!(f_true(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(f_true(&b"xxx"[..]), Done(&b"xxx"[..], None));

    assert_eq!(f_false(&b"abcdef"[..]), Done(&b"abcdef"[..], None));
    assert_eq!(f_false(&b"ab"[..]), Done(&b"ab"[..], None));
    assert_eq!(f_false(&b"xxx"[..]), Done(&b"xxx"[..], None));
  }

  #[test]
  #[cfg(feature = "std")]
  fn cond_wrapping() {
    // Test that cond!() will wrap a given identifier in the call!() macro.
    named!( tag_abcd, tag!("abcd") );
    let f_true: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>>  =
      Box::new(closure!(&'static [u8], fix_error!(&str, cond!( true, tag_abcd ) )));
    let f_false: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, &str>> =
      Box::new(closure!(&'static [u8], fix_error!(&str, cond!( false, tag_abcd ) )));
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
    assert_eq!(peek_tag(&b"xxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn not() {
    named!(not_aaa, not!(tag!("aaa")));
    assert_eq!(not_aaa(&b"aaa"[..]), Error(error_position!(ErrorKind::Not, &b"aaa"[..])));
    assert_eq!(not_aaa(&b"aa"[..]), Done(&b"aa"[..], &b""[..]));
    assert_eq!(not_aaa(&b"abcd"[..]), Done(&b"abcd"[..], &b""[..]));
  }

  #[test]
  fn verify() {
    named!(test, verify!(take!(5), |slice: &[u8]| slice[0] == 'a' as u8));
    assert_eq!(test(&b"bcd"[..]), Incomplete(Needed::Size(5)));
    assert_eq!(test(&b"bcdefg"[..]), Error(error_position!(ErrorKind::Verify, &b"bcdefg"[..])));
    assert_eq!(test(&b"abcdefg"[..]), Done(&b"fg"[..], &b"abcde"[..]));
  }
}
