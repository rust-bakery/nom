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
//!     fn $name<'a>( i: &'a [u8] ) -> IResult<'a,&[u8], &[u8]> {
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
      use ::std::result::Result::*;
      use $crate::{Err,Needed,IResult};

      let i_ = $i.clone();
      let cl = || {
        $submac!(i_, $($args)*)
      };

      match cl() {
        Err(Err::Incomplete(x)) => Err(Err::Incomplete(x)),
        Ok((i, o))              => Ok((i, o)),
        Err(Err::Error(e))      => {
          return Err(Err::Error(error_node_position!($code, $i, e)))
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
      use ::std::result::Result::*;
      use $crate::Err;

      match $submac!($i, $($args)*) {
        Err(Err::Incomplete(x)) => Err(Err::Incomplete(x)),
        Ok((i, o))    => Ok((i, o)),
        Err(Err::Error(e))      => {
          Err(Err::Error(error_node_position!($code, $i, e)))
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
      use ::std::result::Result::*;
      use $crate::Err;

      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        Ok((i, o))    => Ok((i, o)),
        Err(Err::Error(e))      => Err(Err::Error(e)),
        Err(Err::Incomplete(_)) =>  {
          Err(Err::Error(error_position!(ErrorKind::Complete, $i)))
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
/// # use nom::IResult::{self, Ok(, Error};
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::{be_u8,ErrorKind};
///
///  fn take_add(input:&[u8], size: u8) -> IResult<&[u8],&[u8]> {
///    let (i1, sz)     = try_parse!(input, be_u8);
///    let (i2, length) = try_parse!(i1, expr_opt!(size.checked_add(sz)));
///    let (i3, data)   = try_parse!(i2, take!(length));
///    return Ok((i3, data);
///  }
/// # fn main() {
/// let arr1 = [1, 2, 3, 4, 5];
/// let r1 = take_add(&arr1[..], 1);
/// assert_eq!(r1, Ok((&[4,5][..], &[2,3][..]));
///
/// let arr2 = [0xFE, 2, 3, 4, 5];
/// // size is overflowing
/// let r1 = take_add(&arr2[..], 42);
/// assert_eq!(r1, Error(error_position!(ErrorKind::ExprOpt,&[2,3,4,5][..])));
/// # }
/// ```
#[macro_export]
macro_rules! try_parse (
  ($i:expr, $submac:ident!( $($args:tt)* )) => ({
    use ::std::result::Result::*;
    use $crate::{Convert,Context,Err,Needed,IResult};

    match $submac!($i, $($args)*) {
      Ok((i,o))     => (i,o),
      Err(Err::Error(e))      => return Err(Err::Error(Context::convert(e))),
      Err(Err::Incomplete(i)) => return Err(Err::Incomplete(i))
    }
    });
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

      ($submac!($i, $($args)*)).map(|(i,o)| {
        (i, _unify($g, o))
      })
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
      use ::std::result::Result::*;
      use $crate::Err;

      let i_ = $i.clone();
      ($submac!(i_, $($args)*)).and_then(|(i,o)| {
        match $submac2!(o, $($args2)*) {
          Ok(output) => Ok((i, output)),
          Err(_)     => Err(Err::Error(error_position!(ErrorKind::MapRes, $i)))
        }
      })
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
      use ::std::result::Result::*;
      use $crate::Err;

      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        Err(Err::Error(e))      => Err(Err::Error(e)),
        Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
        Ok((i, o))              => match $submac2!(o, $($args2)*) {
          ::std::option::Option::Some(output)   => Ok((i, output)),
          ::std::option::Option::None           => Err(Err::Error(error_position!(ErrorKind::MapOpt, $i)))
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
      use ::std::result::Result::*;
      use $crate::Err;

      use $crate::ParseTo;
      use $crate::Slice;
      use $crate::InputLength;

      let res: ::std::option::Option<$t> = ($i).parse_to();
      match res {
        ::std::option::Option::Some(output) => Ok(($i.slice(..$i.input_len()), output)),
        ::std::option::Option::None         => Err(Err::Error(error_position!(ErrorKind::MapOpt, $i)))
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
      use ::std::result::Result::*;
      use $crate::{Convert,Err,Needed,IResult};

      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        Err(e)     => Err(Err::convert(e)),
        Ok((i, o)) => if $submac2!(o, $($args2)*) {
          Ok((i, o))
        } else {
          Err(Err::Error(error_position!(ErrorKind::Verify, $i)))
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
///  assert_eq!(r, Ok((&b" aaa"[..], 42));
///
///  let r2 = y(&b"<!----> aaa"[..]);
///  assert_eq!(r2, Ok((&b" aaa"[..], 42));
/// # }
/// ```
#[macro_export]
macro_rules! value (
  ($i:expr, $res:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use $crate::{Convert,Err,Needed,IResult};

      match $submac!($i, $($args)*) {
        Ok((i,_)) => {
          let res: IResult<_,_> = Ok((i, $res));
          res
        },
        Err(e) => Err(Err::convert(e)),
      }
    }
  );
  ($i:expr, $res:expr, $f:expr) => (
    value!($i, $res, call!($f))
  );
  ($i:expr, $res:expr) => (
    {
      let res: $crate::IResult<_,_,u32> = Ok(($i, $res));
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
      use ::std::result::Result::*;
      use $crate::{Err,Needed,IResult};

      match $e {
        Ok(output) => Ok(($i, output)),
        Err(_)     => Err(Err::Error(error_position!(ErrorKind::ExprRes, $i)))
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
/// # use nom::IResult::{self, Ok(, Error};
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
/// assert_eq!(r1, Ok((&[4,5][..], &[2,3][..]));
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
      use ::std::result::Result::*;
      use $crate::{Err,Needed,IResult};

      match $e {
        ::std::option::Option::Some(output) => Ok(($i, output)),
        ::std::option::Option::None         => Err(Err::Error(error_position!(ErrorKind::ExprOpt, $i)))
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
///  assert_eq!(o(&a[..]), Ok((&b"ef"[..], Some(&b"abcd"[..])));
///  assert_eq!(o(&b[..]), Ok((&b"bcdefg"[..], None));
///  # }
/// ```
#[macro_export]
macro_rules! opt(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use $crate::{Err,IResult};

      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        Ok((i,o))     => Ok((i, ::std::option::Option::Some(o))),
        Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
        _                              => {
          let res: IResult<_,_> = Ok(($i, ::std::option::Option::None));
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
///  assert_eq!(o(&a[..]), Ok((&b"ef"[..], Ok(&b"abcd"[..])));
///  assert_eq!(o(&b[..]), Ok((&b"bcdefg"[..], Err(error_position!(ErrorKind::Tag, &b[..]))));
///  # }
/// ```
#[macro_export]
macro_rules! opt_res (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use $crate::Err;

      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        Ok((i,o))     => Ok((i,  Ok(o))),
        Err(Err::Error(e))      => Ok(($i, Err(Err::Error(e)))),
        Err(Err::Incomplete(i)) => Err(Err::Incomplete(i))
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
///  assert_eq!(f(&a[..]), Ok((&b"ef"[..], Some(&b"abcd"[..])));
///
///  let b2 = false;
///  let f2:Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>>> = Box::new(closure!(&'static[u8],
///    cond!( b2, tag!("abcd") ))
///  );
///  assert_eq!(f2(&a[..]), Ok((&b"abcdef"[..], None));
///  # }
/// ```
///
#[macro_export]
macro_rules! cond_with_error(
  ($i:expr, $cond:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use $crate::{Convert,Err,Needed,IResult};

      if $cond {
        match $submac!($i, $($args)*) {
          Ok((i,o)) => Ok((i, ::std::option::Option::Some(o))),
          Err(e)    => Err(Err::convert(e)),
        }
      } else {
        let res: ::std::result::Result<_,_> = Ok(($i, ::std::option::Option::None));
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
///  assert_eq!(f(&a[..]), Ok((&b"ef"[..], Some(&b"abcd"[..])));
///
///  let b2 = false;
///  let f2:Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>>> = Box::new(closure!(&'static[u8],
///    cond!( b2, tag!("abcd") ))
///  );
///  assert_eq!(f2(&a[..]), Ok((&b"abcdef"[..], None));
///  # }
/// ```
///
#[macro_export]
macro_rules! cond(
  ($i:expr, $cond:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use $crate::{Err,IResult};

      if $cond {
        let i_ = $i.clone();
        match $submac!(i_, $($args)*) {
          Ok((i,o))               => Ok((i, ::std::option::Option::Some(o))),
          Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
          Err(Err::Error(_))      => {
            let res: IResult<_,_,u32> = Ok(($i, ::std::option::Option::None));
            res
          },
        }
      } else {
        let res: ::std::result::Result<_,_> = Ok(($i, ::std::option::Option::None));
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
///  assert_eq!(f(&a[..]), Ok((&b"ef"[..], &b"abcd"[..]));
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
      use ::std::result::Result::*;
      use $crate::{Convert,Err,Needed,IResult};

      if $cond {
        match $submac!($i, $($args)*) {
          Ok((i,o)) => Ok((i, o)),
          Err(e)    => Err(Err::convert(e)),
        }
      } else {
        Err(Err::Error(error_position!(ErrorKind::CondReduce, $i)))
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
/// the embedded parser may return Err(Err::Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(ptag, peek!( tag!( "abcd" ) ) );
///
///  let r = ptag(&b"abcdefgh"[..]);
///  assert_eq!(r, Ok((&b"abcdefgh"[..], &b"abcd"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! peek(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use $crate::{Convert,Err};

      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        Ok((_,o)) => Ok(($i, o)),
        Err(e)    => Err(Err::convert(e)),
      }
    }
  );
  ($i:expr, $f:expr) => (
    peek!($i, call!($f));
  );
);

/// `not!(I -> IResult<I,O>) => I -> IResult<I, O>`
/// returns a result only if the embedded parser returns Error or Err(Err::Incomplete
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
/// assert_eq!(r, Ok((&b"d"[..], &b"abc"[..]));
///
/// let r2 = not_e(&b"abce"[..]);
/// assert_eq!(r2, Error(error_position!(ErrorKind::Not, &b"e"[..])));
/// # }
/// ```
#[macro_export]
macro_rules! not(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use $crate::Err;

      use $crate::Slice;
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        Ok(_)  => Err(Err::Error(error_position!(ErrorKind::Not, $i))),
        Err(_) => Ok(($i, ($i).slice(..0))),
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
///  assert_eq!(r, Ok((&b"efgh"[..], &b"abcd"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! tap (
  ($i:expr, $name:ident : $submac:ident!( $($args:tt)* ) => $e:expr) => (
    {
      use ::std::result::Result::*;
      use $crate::{Convert,Err,Needed,IResult};

      match $submac!($i, $($args)*) {
        Ok((i,o)) => {
          let $name = o;
          $e;
          Ok((i, $name))
        },
        Err(e)    => Err(Err::convert(e)),
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
      use ::std::result::Result::*;
      use $crate::Err;

      use $crate::InputLength;
      if ($i).input_len() == 0 {
        Ok(($i, $i))
      } else {
        Err(Err::Error(error_position!(ErrorKind::Eof, $i)))
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
///  assert_eq!(r, Ok((&b" aaa"[..], &b"<!-- abc -->"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! recognize (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use ::std::result::Result::*;
      use $crate::{Convert,Err};

      use $crate::Offset;
      use $crate::Slice;
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        Ok((i,_)) => {
          let index = (&$i).offset(&i);
          Ok((i, ($i).slice(..index)))
        },
        Err(e)    => Err(Err::convert(e))
      }
    }
  );
  ($i:expr, $f:expr) => (
    recognize!($i, call!($f))
  );
);


#[cfg(test)]
mod tests {
  use internal::{Err,Needed,IResult};

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

        let res: $crate::IResult<_,_,u32> = if reduced != b {
          Err($crate::Err::Error(error_position!($crate::ErrorKind::Tag, $i)))
        } else if m < blen {
          Err($crate::Err::Incomplete($crate::Needed::Size(blen)))
        } else {
          Ok((&$i[blen..], reduced))
        };
        res
      }
    );
  );

  macro_rules! take(
    ($i:expr, $count:expr) => (
      {
        let cnt = $count as usize;
        let res:IResult<&[u8],&[u8]> = if $i.len() < cnt {
          Err(Err::Incomplete(Needed::Size(cnt)))
        } else {
          Ok((&$i[cnt..],&$i[0..cnt]))
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
    assert_eq!(res, Ok((&b""[..], a)));
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
    assert_eq!(opt_abcd(a), Ok((&b"ef"[..], Some(&b"abcd"[..]))));
    assert_eq!(opt_abcd(b), Ok((&b"bcdefg"[..], None)));
    assert_eq!(opt_abcd(c), Err(Err::Incomplete(Needed::Size(4))));
  }

  #[cfg(feature = "verbose-errors")]
  #[test]
  fn opt_res() {
    named!(opt_res_abcd<&[u8], Result<&[u8], Err<&[u8]> > >, opt_res!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    let c = &b"ab"[..];
    assert_eq!(opt_res_abcd(a), Ok((&b"ef"[..], Ok(&b"abcd"[..]))));
    assert_eq!(opt_res_abcd(b), Ok((&b"bcdefg"[..], Err(Err::Error(error_position!(ErrorKind::Tag, b))))));
    assert_eq!(opt_res_abcd(c), Err(Err::Incomplete(Needed::Size(4))));
  }

  #[cfg(not(feature = "verbose-errors"))]
  #[test]
  fn opt_res() {
    named!(opt_res_abcd<&[u8], Result<&[u8], Err<&[u8], u32>> >, opt_res!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"bcdefg"[..];
    let c = &b"ab"[..];
    assert_eq!(opt_res_abcd(a), Ok((&b"ef"[..], Ok(&b"abcd"[..]))));
    assert_eq!(opt_res_abcd(b), Ok((&b"bcdefg"[..], Err(Err::Error(error_position!(ErrorKind::Tag, b))))));
    assert_eq!(opt_res_abcd(c), Err(Err::Incomplete(Needed::Size(4))));
  }

  use std::convert::From;
  #[derive(Debug,PartialEq)]
  pub struct CustomError(&'static str);
  impl From<u32> for CustomError {
    fn from(_: u32) -> Self {
      CustomError("test")
    }
  }

  #[test]
  #[cfg(feature = "std")]
  fn cond() {
    let f_true: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, CustomError>>  =
      Box::new(closure!(&'static [u8], fix_error!(CustomError, cond!( true, tag!("abcd") ) )));
    let f_false: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, CustomError>> =
      Box::new(closure!(&'static [u8], fix_error!(CustomError, cond!( false, tag!("abcd") ) )));
    //let f_false = closure!(&'static [u8], cond!( false, tag!("abcd") ) );

    assert_eq!(f_true(&b"abcdef"[..]), Ok((&b"ef"[..], Some(&b"abcd"[..]))));
    assert_eq!(f_true(&b"ab"[..]), Err(Err::Incomplete(Needed::Size(4))));
    assert_eq!(f_true(&b"xxx"[..]), Ok((&b"xxx"[..], None)));

    assert_eq!(f_false(&b"abcdef"[..]), Ok((&b"abcdef"[..], None)));
    assert_eq!(f_false(&b"ab"[..]), Ok((&b"ab"[..], None)));
    assert_eq!(f_false(&b"xxx"[..]), Ok((&b"xxx"[..], None)));
  }

  #[test]
  #[cfg(feature = "std")]
  fn cond_wrapping() {
    // Test that cond!() will wrap a given identifier in the call!() macro.
    named!( tag_abcd, tag!("abcd") );
    let f_true: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, CustomError>>  =
      Box::new(closure!(&'static [u8], fix_error!(CustomError, cond!( true, tag_abcd ) )));
    let f_false: Box<Fn(&'static [u8]) -> IResult<&[u8],Option<&[u8]>, CustomError>> =
      Box::new(closure!(&'static [u8], fix_error!(CustomError, cond!( false, tag_abcd ) )));
    //let f_false = closure!(&'static [u8], cond!( b2, tag!("abcd") ) );

    assert_eq!(f_true(&b"abcdef"[..]), Ok((&b"ef"[..], Some(&b"abcd"[..]))));
    assert_eq!(f_true(&b"ab"[..]), Err(Err::Incomplete(Needed::Size(4))));
    assert_eq!(f_true(&b"xxx"[..]), Ok((&b"xxx"[..], None)));

    assert_eq!(f_false(&b"abcdef"[..]), Ok((&b"abcdef"[..], None)));
    assert_eq!(f_false(&b"ab"[..]), Ok((&b"ab"[..], None)));
    assert_eq!(f_false(&b"xxx"[..]), Ok((&b"xxx"[..], None)));
  }

  #[test]
  fn peek() {
    named!(peek_tag<&[u8],&[u8]>, peek!(tag!("abcd")));

    assert_eq!(peek_tag(&b"abcdef"[..]), Ok((&b"abcdef"[..], &b"abcd"[..])));
    assert_eq!(peek_tag(&b"ab"[..]), Err(Err::Incomplete(Needed::Size(4))));
    assert_eq!(peek_tag(&b"xxx"[..]), Err(Err::Error(error_position!(ErrorKind::Tag, &b"xxx"[..]))));
  }

  #[test]
  fn not() {
    named!(not_aaa, not!(tag!("aaa")));
    assert_eq!(not_aaa(&b"aaa"[..]), Err(Err::Error(error_position!(ErrorKind::Not, &b"aaa"[..]))));
    assert_eq!(not_aaa(&b"aa"[..]), Ok((&b"aa"[..], &b""[..])));
    assert_eq!(not_aaa(&b"abcd"[..]), Ok((&b"abcd"[..], &b""[..])));
  }

  #[test]
  fn verify() {
    named!(test, verify!(take!(5), |slice: &[u8]| slice[0] == 'a' as u8));
    assert_eq!(test(&b"bcd"[..]), Err(Err::Incomplete(Needed::Size(5))));
    assert_eq!(test(&b"bcdefg"[..]), Err(Err::Error(error_position!(ErrorKind::Verify, &b"bcdefg"[..]))));
    assert_eq!(test(&b"abcdefg"[..]), Ok((&b"fg"[..], &b"abcde"[..])));
  }
}
