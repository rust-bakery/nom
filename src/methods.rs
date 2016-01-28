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
//! But when used as methods in other combinators, are used
//! like this:
//!
//! ```ignore
//! method!(my_function<&Parser>,self, [(self, self_ref_cell)] tag!("abcd"));
//! ```
//!
//! Internally, other combinators will rewrite
//! that call to pass the input as first argument:
//!
//! ```ignore
//! macro_rules! method (
//!   ($name:ident<$a:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
//!     fn $name( $self_: $a, i: &[u8] ) -> $crate::IResult<&[u8], &[u8]> {
//!       use std::cell::RefCell;
//!       $(let $cell = RefCell::new($stt)),*;
//!       $submac!(i, $($args)*)
//!     }
//!   );
//! );
//! ```
//! 
//! The `method!` macro is similar to the `named!` macro in the macros module.
//! While `named!` will create a parser function, `method!` will create a parser
//! method on the struct it is defined in.
//!
//! Compared to the `named!` macro there are a few differences in how they are
//! invodked. A `method!` invocation always has to have the type of `self`
//! declared:
//! ```ignore
//! //                  -`self`'s type-
//! method!(method_name<  &Parser<'a> >, ...);
//! ```
//! `self`'s type always comes first except in the `method!` macro that takes
//! a lifetime parameter.
//! ```ignore
//! //                  lifetime | `self`'s type |   in/out types
//! method!(method_name<lifetime , &Parser<'a>   , &'a str, &'a str>, ...);
//!```
//! The next difference is you have to input the self struct. Due to Rust's
//! macro hygiene the macro can't declare it on it's own.
//! ```ignore
//! //                                                 -self-
//! method!(method_name<&Parser<'a>, &'a str, &'a str>, self, ...);
//! ```
//! When making a parsing struct with parsing methods, due to the static borrow
//! checker,calling any parsing methods on self (or any other parsing struct)
//! will cause self to be borrowed for the entire method, even in lines before
//! the borrow happened. To get around this restriction all parsing structs
//! that will have methods called on them will be wrapped in `RefCell`s and
//! and methods will be called on a borrowed (mutable) reference of the
//! `RefCell`. This allows for more intuitive and usable borrow lifetimes
//! (though it does come with a slight performance penalty as Rust's runtime
//! borrow-checker is used instead of the compile-time borrow checker).
//!
//! The `method!` creator needs specify the structs they want wrapped in
//! `RefCell`s for later calling as well as the name of the wrapping `RefCell`.
//! ```ignore
//! 
//! method!(method_name<&Parser<'a>, &'a str, &'a str>, self,
//! // -struct, wrapped struct's name-    -struct,     wrapped struct's name-
//!   [(self,     ref_cell_self     ), (other_parser,      ref_cell_other  )], ...);
//! ```
//! Again, due to macro hygiene the `method!` macro can't auto-generate the
//! the wrapper's names, so you need to supply them yourself, but this is okay
//! because you'll need to use them later.
//! 
//! To call a wrapped struct you need to use the `call_rf!` (to get a non-mutable
//! borrow) or `call_mut!` (to get a mutable borrow) macro. For example:
//! ```ignore
//! struct<'a> Parser<'a> {
//!   parsed: &'a str,
//! }
//! impl<'a> Parser<'a> {
//!   // Constructor omitted for brevity
//!   method!(take4<&Parser<'a>, &'a str, &'a str>, self, [], take!(4));
//!   method!(caller<&Parser<'a>, &'a str, &'a str>, self, [(self, rcs)]), call_rf!(rcs.take4));
//! }
//! ```
//! Notice in the definition of `take4` no structs and wrapped names are specified
//! because they aren't needed since it won't be calling any methods. The `caller`
//! method however does call a method on the `self` struct so it specifies `self`
//! as a struct to be wrapped and `rcs` as the wrapped name. Later, we make use of
//! the `call_rf!` macro (to get a non-mutable borrow) or `call_mut!` macro (to
//! get a mutable borrow) to call the `take4` method on the wrapped `self` struct, 
//! `rcs`.
//! 
//! More complicated combinations still mostly look the same as their `named!`
//! counterparts:
//! ```ignore
//!    method!(pub simple_chain<&mut Parser<'a>, &'a str, &'a str>, self, [(self, rcs)],
//!      chain!(
//!             call_rf!(rcs.tag_abc)      ~
//!             call_rf!(rcs.tag_def)      ~
//!             call_rf!(rcs.tag_ghi)      ~
//!       last: call_rf!(rcs.simple_peek)  ,
//!        ||{rcs.borrow_mut().parsed = last; last}
//!      )
//!    );
//! ```
//! Since `simple_chain` modifies self any callers will have to wrap it in the `call_mut!`
//! macro.
//!
//! The four additions to method definitions remeber are:
//! 1. Specify `self`'s type
//! 2. Pass `self` to the macro
//! 3. Specify structs that need to be wrapped and the name of their wrapper
//! 4. Call parser methods using the `call_rf!` or `call_mut` macros.

/// Makes a method from a parser combination
///
/// The type can be set up if the compiler needs
/// more information
///
/// ```ignore
/// method!(my_function<&Parser<'a> >( &[u8] ) -> &[u8], tag!("abcd"));
/// // first type parameter is `self`'s type, second is input, third is output
/// method!(my_function<&Parser<'a>, &[u8], &[u8]>,     tag!("abcd"));
/// // will have &Parser<'a> as the `self` type, &[u8] as input type, &[u8] as output type
/// method!(my_function<&Parser<'a>,                   tag!("abcd"));
/// // will use &[u8] as input type (use this if the compiler
/// // complains about lifetime issues
/// method!(my_function<&Parser<'a>, &[u8]>,            tag!("abcd"));
/// //prefix them with 'pub' to make the methods public
/// method!(pub my_function<&Parser<'a>,               tag!("abcd"));
/// ```
#[macro_export]
macro_rules! method (
  ($name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
    fn $name( $self_: $a, i: $i ) -> $crate::IResult<$i,$o> {
      use std::cell::RefCell;
      $(let $cell = RefCell::new($stt)),*;
      $submac!(i, $($args)*)
    }
  );
  ($name:ident<$a:ty,$i:ty,$o:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
    fn $name( $self_: $a, i: $i ) -> $crate::IResult<$i, $o> {
      use std::cell::RefCell;
      $(let $cell = RefCell::new($stt)),*;
      $submac!(i, $($args)*)
    }
  );
  ($name:ident<$a:ty, $o:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
    fn $name<'a>( $self_: $a, i: &'a[u8] ) -> $crate::IResult<&'a [u8], $o> {
      use std::cell::RefCell;
      $(let $cell = RefCell::new($stt)),*;
      $submac!(i, $($args)*)
    }
    );
  ($name:ident<$life:item,$a:ty,$i:ty,$o:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
    fn $name<$life>( $self_: $a, i: $i ) -> $crate::IResult<$life, $i, $o> {
      use std::cell::RefCell;
      $(let $cell = RefCell::new($stt)),*;
      $submac!(i, $($args)*)
    }
  );
  ($name:ident<$a:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
    fn $name( $self_: $a, i: &[u8] ) -> $crate::IResult<&[u8], &[u8]> {
      use std::cell::RefCell;
      $(let $cell = RefCell::new($stt)),*;
      $submac!(i, $($args)*)
    }
  );
  (pub $name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
    pub fn $name( $self_: $a, i: $i ) -> $crate::IResult<$i,$o> {
      use std::cell::RefCell;
      $(let $cell = RefCell::new($stt)),*;
      $submac!(i, $($args)*)
    }
  );
  (pub $name:ident<$a:ty,$i:ty,$o:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
    pub fn $name( $self_: $a, i: $i ) -> $crate::IResult<$i, $o> {
      use std::cell::RefCell;
      $(let $cell = RefCell::new($stt)),*;
      $submac!(i, $($args)*)
    }
  );
  (pub $name:ident<$a:ty,$o:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
    pub fn $name( $self_: $a, i: &[u8] ) -> $crate::IResult<&[u8], $o> {
      use std::cell::RefCell;
      $(let $cell = RefCell::new($stt)),*;
      $submac!(i, $($args)*)
    }
  );
  (pub $name:ident<$a:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) => (
    pub fn $name<'a>( $self_: $a, i: &'a [u8] ) -> $crate::IResult<&[u8], &[u8]> {
      use std::cell::RefCell;
      $(let $cell = RefCell::new($stt)),*;
      $submac!(i, $($args)*)
    }
  );
);

/// Used to call methods directly on an struct, not on the wrapping `RefCell`. Use with caution.
#[macro_export]
macro_rules! call_m (
  ($i:expr, $stt:ident.$method:ident) => ( $stt.$method( $i ) );
  ($i:expr, $stt:ident.$method:ident, $($args:expr),* ) => ( $stt.$method( $i, $($args),* ) );
);

/// Used to called methods on non-mutable structs wrapped in `RefCell`s
#[macro_export]
macro_rules! call_rf (
  ($i:expr, $cell:ident.$method:ident) => ( { let res = $cell.borrow().$method( $i ); res } );
  ($i:expr, $cell:ident.$method:ident, $($args:expr),* ) => ( { let res = $cell.borrow().$method( $i, $($args),* ); res } );
);

/// Used to called methods on mutable structs wrapped in `RefCell`s
#[macro_export]
macro_rules! call_rf (
  ($i:expr, $cell:ident.$method:ident) => ( { let res = $cell.borrow_mut().$method( $i ); res } );
  ($i:expr, $cell:ident.$method:ident, $($args:expr),* ) => ( { let res = $cell.borrow_mut().$method( $i, $($args),* ); res } );
);

/// emulate function currying for method calls on bare structs, not on the wrapping `RefCell.
/// Use with caution: 
/// `apply!(self.my_function, arg1, arg2, ...)` becomes `self.my_function(input, arg1, arg2, ...)`
///
/// Supports up to 6 arguments
#[macro_export]
macro_rules! apply_m (
  ($i:expr, $stt:ident.$method:ident, $($args:expr),* ) => ( $stt.$method( $i, $($args),* ) );
);

/// emulate function currying for method calls on non-mutable structs wrapped in `RefCell`s: 
/// `apply!(cell.my_function, arg1, arg2, ...)` becomes `cell.borrow_mut().my_function(input, arg1, arg2, ...)`
///
/// Supports up to 6 arguments
#[macro_export]
macro_rules! apply_rf (
  ($i:expr, $cell:ident.$method:ident, $($args:expr),* ) => ( $cell.borrow().$method( $i, $($args),* ) );
);

/// emulate function currying for method calls on mutable structs wrapped in `RefCell`s: 
/// `apply!(cell.my_function, arg1, arg2, ...)` becomes `cell.borrow_mut().my_function(input, arg1, arg2, ...)`
///
/// Supports up to 6 arguments
#[macro_export]
macro_rules! apply_mut (
  ($i:expr, $cell:ident.$method:ident, $($args:expr),* ) => ( $cell.borrow_mut().$method( $i, $($args),* ) );
);

#[cfg(test)]
mod tests {
  use internal::{Needed,IResult,Err};
  use internal::IResult::*;
  use internal::Err::*;
  use util::ErrorKind;

  // reproduce the tag_s and take_s macros, because of module import order
  macro_rules! tag_s (
    ($i:expr, $tag: expr) => (
      {
        let res: $crate::IResult<_,_> = if $tag.len() > $i.len() {
          $crate::IResult::Incomplete($crate::Needed::Size($tag.len()))
        //} else if &$i[0..$tag.len()] == $tag {
        } else if ($i).starts_with($tag) {
          $crate::IResult::Done(&$i[$tag.len()..], &$i[0..$tag.len()])
        } else {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::TagStr, $i))
        };
        res
      }
    );
  );

  macro_rules! take_s (
    ($i:expr, $count:expr) => (
      {
        let cnt = $count as usize;
        let res: $crate::IResult<_,_> = if $i.chars().count() < cnt {
          $crate::IResult::Incomplete($crate::Needed::Size(cnt))
        } else {
          let mut offset = $i.len();
          let mut count = 0;
          for (o, c) in $i.char_indices() {
            println!("index: {}: {}", count, c);
            if count == cnt {
              offset = o;
              break;
            }
            count += 1;
          }
          $crate::IResult::Done(&$i[offset..], &$i[..offset])
        };
        res
      }
    );
  );

  pub struct Parser<'a> {
    last_str: &'a str,
    truth: bool,
  }

  impl<'a> Parser<'a> {
    pub fn new(s: &'a str) -> Parser<'a> {
      Parser{last_str: s, truth: false}
    }
  // ($name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) =>
  // ($name:ident<$a:ty,$i:ty,$o:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) =>
  // ($name:ident<$a:ty, $o:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) =>
  // ($name:ident<$life:item,$a:ty,$i:ty,$o:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) =>
  // ($name:ident<$a:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) =>
  // (pub $name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) =>
  // (pub $name:ident<$a:ty,$i:ty,$o:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) =>
  // (pub $name:ident<$a:ty,$o:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) =>
  // (pub $name:ident<$a:ty>, $self_:ident, [ $( ($stt:ident, $cell:ident) ),* ], $submac:ident!( $($args:tt)* )) =>
    method!(tag_abc<&mut Parser<'a>, &'a str, &'a str>, self, [], tag_s!("áβç"));
    method!(tag_def<&mut Parser<'a>, &'a str, &'a str>, self, [], tag_s!("δèƒ"));
    method!(tag_ghi<&mut Parser<'a>, &'a str, &'a str>, self, [], tag_s!("ϱλï"));
    method!(take3<&mut Parser<'a>, &'a str, &'a str>, self, [], take_s!(3));
    method!(pub simple_call<&mut Parser<'a>, &'a str, &'a str>, self, [(self, ref_cell_self)],
      call_rf!(ref_cell_self.tag_abc)
    );
    method!(pub simple_peek<&mut Parser<'a>, &'a str, &'a str>, self, [(self, rcs)],
      peek!(call_rf!(rcs.take3))
    );
    method!(pub simple_chain<&mut Parser<'a>, &'a str, &'a str>, self, [(self, rcs)],
      chain!(
             call_rf!(rcs.tag_abc)      ~
             call_rf!(rcs.tag_def)      ~
             call_rf!(rcs.tag_ghi)      ~
       last: call_rf!(rcs.simple_peek)  ,
        ||{rcs.borrow_mut().last_str = last; last}
      )
    );
  }

  #[test]
  fn test_method_call_rf() {
    let mut p = Parser::new("");
    let INPUT = "áβçδèƒϱλïJƙ";
    let CONSUMED = "áβç";
    let LEFTOVER = "δèƒϱλïJƙ";
    match p.simple_call(INPUT) {
      Done(extra, output) => { assert!(extra == LEFTOVER, "`Parser.simple_call` consumed leftover input. Leftover: {}", extra);
                               assert!(output == CONSUMED, "`Parser.simple_call` doens't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", CONSUMED, output);
                             },
      other => panic!("`Parser.simple_call` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_peek() {
    let mut p = Parser::new("");
    let INPUT = "ж¥ƺáβçδèƒϱλïJƙ";
    let CONSUMED = "ж¥ƺ";
    match p.simple_peek(INPUT) {
      Done(extra, output) => { assert!(extra == INPUT, "`Parser.simple_peek` consumed leftover input. Leftover: {}", extra);
                               assert!(output == CONSUMED, "`Parser.simple_peek` doens't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", CONSUMED, output);
                             },
      other => panic!("`Parser.simple_peek` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_chain() {
    let mut p = Parser::new("");
    let INPUT = "áβçδèƒϱλïJƙℓ";
    let LEFTOVER = "Jƙℓ";
    match p.simple_chain(INPUT) {
      Done(extra, output) => { assert!(extra == LEFTOVER, "`Parser.simple_chain` consumed leftover input. Leftover: {}", extra);
                               assert!(output == LEFTOVER, "`Parser.simple_chain` doens't return the string it was supposed to \
                                on success. Expected `{}`, got `{}`.", LEFTOVER, output);
                             },
      other => panic!("`Parser.simple_chain` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }
}
