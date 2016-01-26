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

/// Used to call methods directly on an struct
#[macro_export]
macro_rules! call_m (
  ($i:expr, $stt:ident.$method:ident) => ( $stt.$method( $i ) );
  ($i:expr, $stt:ident.$method:ident, $($args:expr),* ) => ( $stt.$method( $i, $($args),* ) );
);

/// Used to called methods on structs wrapped in `RefCell`s
// #[macro_export]
// macro_rules! call_rf (
//   ($i:expr, $cell:ident.$method:ident) => ( $cell.borrow_mut().$method( $i ) );
//   ($i:expr, $cell:ident.$method:ident, $($args:expr),* ) => ( $cell.borrow_mut().$method( $i, $($args),* ) );
// );

/// Used to called methods on structs wrapped in `RefCell`s
#[macro_export]
macro_rules! call_rf (
  ($i:expr, $cell:ident.$method:ident) => ( { let res = $cell.borrow_mut().$method( $i ); res } );
  ($i:expr, $cell:ident.$method:ident, $($args:expr),* ) => ( { let res = $cell.borrow_mut().$method( $i, $($args),* ); res } );
);

/// emulate function currying for method calls on bare structs: 
/// `apply!(my_function, arg1, arg2, ...)` becomes `my_function(input, arg1, arg2, ...)`
///
/// Supports up to 6 arguments
#[macro_export]
macro_rules! apply_m (
  ($i:expr, $stt:ident.$method:ident, $($args:expr),* ) => ( $stt.$method( $i, $($args),* ) );
);

/// emulate function currying for method calls on structs wrapped in `RefCell`s: 
/// `apply!(my_function, arg1, arg2, ...)` becomes `my_function(input, arg1, arg2, ...)`
///
/// Supports up to 6 arguments
#[macro_export]
macro_rules! apply_rf (
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
