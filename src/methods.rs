//! Method macro combinators
//!
//! These macros make parsers as methods of structs
//! and that can take methods of structs to call
//! as parsers.
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
//! method!(my_function<Parser<'a> >, self, tag!("abcd"));
//! ```
//!
//! Internally, other combinators will rewrite
//! that call to pass the input as second argument:
//!
//! ```ignore
//! macro_rules! method (
//!   ($name:ident<$a:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
//!     fn $name( $self_: $a, i: &[u8] ) -> $crate::IResult<&[u8], &[u8]> {
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
//! invoked. A `method!` invocation always has to have the type of `self`
//! declared and it can't be a reference due to Rust's borrow lifetime
//! restrictions:
//! ```ignore
//! //                  -`self`'s type-
//! method!(method_name<  Parser<'a> >, ...);
//! ```
//! `self`'s type always comes first.
//! The next difference is you have to input the self struct. Due to Rust's
//! macro hygiene the macro can't declare it on it's own.
//! ```ignore
//! //                                                 -self-
//! method!(method_name<Parser<'a>, &'a str, &'a str>, self, ...);
//! ```
//! When making a parsing struct with parsing methods, due to the static borrow
//! checker,calling any parsing methods on self (or any other parsing struct)
//! will cause self to be moved for the rest of the method.To get around this
//! restriction all self is moved into the called method and then the called
//! method will return self to the caller.
//! 
//! To call a method on self you need to use the `call_m!` macro. For example:
//! ```ignore
//! struct<'a> Parser<'a> {
//!   parsed: &'a str,
//! }
//! impl<'a> Parser<'a> {
//!   // Constructor omitted for brevity
//!   method!(take4<Parser<'a>, &'a str, &'a str>, self, take!(4));
//!   method!(caller<Parser<'a>, &'a str, &'a str>, self, call_m!(self.take4));
//! }
//! ```
//! More complicated combinations still mostly look the same as their `named!`
//! counterparts:
//! ```ignore
//!    method!(pub simple_chain<&mut Parser<'a>, &'a str, &'a str>, self,
//!      do_parse!(
//!             call_m!(self.tag_abc)                                        >>
//!             call_m!(self.tag_def)                                        >>
//!             call_m!(self.tag_ghi)                                        >>
//!       last: map!(call_m!(self.simple_peek), |parsed| sb.parsed = parsed) >>
//!       (last)
//!      )
//!    );
//! ```
//! The three additions to method definitions to remember are:
//! 1. Specify `self`'s type
//! 2. Pass `self` to the macro
//! 4. Call parser methods using the `call_m!` macro.

/// Makes a method from a parser combination
///
/// The must be set up because the compiler needs
/// the information
///
/// ```ignore
/// method!(my_function<Parser<'a> >( &[u8] ) -> &[u8], tag!("abcd"));
/// // first type parameter is `self`'s type, second is input, third is output
/// method!(my_function<Parser<'a>, &[u8], &[u8]>,     tag!("abcd"));
/// //prefix them with 'pub' to make the methods public
/// method!(pub my_function<Parser<'a>,&[u8], &[u8]>, tag!("abcd"));
/// ```
#[macro_export]
macro_rules! method (
  // Non-public immutable self
  ($name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      fn $name( $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  ($name:ident<$a:ty,$i:ty,$o:ty,$e:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    #[allow(unused_variables)]
    fn $name( $self_: $a, i: $i ) -> ($a, $crate::IResult<$i, $o, $e>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  ($name:ident<$a:ty,$i:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    #[allow(unused_variables)]
    fn $name( $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>)  {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  ($name:ident<$a:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      fn $name( $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], $o, u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  ($name:ident<$a:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      fn $name( $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], &[u8], u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  // Public immutable self
  (pub $name:ident<$a:ty>( $i:ty ) -> $o:ty, $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      pub fn $name( $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  (pub $name:ident<$a:ty,$i:ty,$o:ty,$e:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      fn $name( $self_: $a, i: $i ) -> ($a, $crate::IResult<$i, $o, $e>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  (pub $name:ident<$a:ty,$i:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    #[allow(unused_variables)]
    pub fn $name( $self_: $a,i: $i ) -> ($a, $crate::IResult<$i,$o,u32>)  {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  (pub $name:ident<$a:ty,$o:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    #[allow(unused_variables)]
    pub fn $name( $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], $o, u32>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  (pub $name:ident<$a:ty>, $self_:ident, $submac:ident!( $($args:tt)* )) => (
    #[allow(unused_variables)]
    pub fn $name( $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], &[u8], u32>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  // Non-public mutable self
  ($name:ident<$a:ty>( $i:ty ) -> $o:ty, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      fn $name( mut $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  ($name:ident<$a:ty,$i:ty,$o:ty,$e:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      fn $name( mut $self_: $a, i: $i ) -> ($a, $crate::IResult<$i, $o, $e>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
      }
  );
  ($name:ident<$a:ty,$i:ty,$o:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
    #[allow(unused_variables)]
    fn $name( mut $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>)  {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  ($name:ident<$a:ty,$o:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      fn $name( mut $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], $o, u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  ($name:ident<$a:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      fn $name( mut $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], &[u8], u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  // Public mutable self
  (pub $name:ident<$a:ty>( $i:ty ) -> $o:ty, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      pub fn $name( mut $self_: $a, i: $i ) -> ($a, $crate::IResult<$i,$o,u32>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  (pub $name:ident<$a:ty,$i:ty,$o:ty,$e:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
      #[allow(unused_variables)]
      fn $name( mut $self_: $a, i: $i ) -> ($a, $crate::IResult<$i, $o, $e>) {
        let result = $submac!(i, $($args)*);
        ($self_, result)
      }
  );
  (pub $name:ident<$a:ty,$i:ty,$o:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
    #[allow(unused_variables)]
    pub fn $name( mut $self_: $a,i: $i ) -> ($a, $crate::IResult<$i,$o,u32>)  {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  (pub $name:ident<$a:ty,$o:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
    #[allow(unused_variables)]
    pub fn $name( mut $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], $o, u32>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
  (pub $name:ident<$a:ty>, mut $self_:ident, $submac:ident!( $($args:tt)* )) => (
    #[allow(unused_variables)]
    pub fn $name( mut $self_: $a, i: &[u8] ) -> ($a, $crate::IResult<&[u8], &[u8], u32>) {
      let result = $submac!(i, $($args)*);
      ($self_, result)
    }
  );
);

/// Used to called methods then move self back into self
#[macro_export]
macro_rules! call_m (
  ($i:expr, $self_:ident.$method:ident) => (
    {
      let (tmp, res) = $self_.$method($i);
      $self_ = tmp;
      res
    }
  );
  ($i:expr, $self_:ident.$method:ident, $($args:expr),* ) => (
    {
      let (tmp, res) = $self_.$method($i, $($args),*);
      $self_ = tmp;
      res
    }
  );
);


/// emulate function currying for method calls on structs
/// `apply_m!(self.my_function, arg1, arg2, ...)` becomes `self.my_function(input, arg1, arg2, ...)`
///
/// Supports up to 6 arguments
#[macro_export]
macro_rules! apply_m (
  ($i:expr, $self_:ident.$method:ident, $($args:expr),* ) => ( { let (tmp, res) = $self_.$method( $i, $($args),* ); $self_ = tmp; res } );
);

#[cfg(test)]
mod tests {
  use internal::IResult::*;

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
          $crate::IResult::Error(error_position!($crate::ErrorKind::TagStr, $i))
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
          for (o, _) in $i.char_indices() {
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

  struct Parser<'a> {
    bcd: &'a str,
  }

  impl<'a> Parser<'a> {
    pub fn new() -> Parser<'a> {
      Parser{bcd: ""}
    }

    method!(tag_abc<Parser<'a>, &'a str, &'a str>, self, tag_s!("áβç"));
    method!(tag_bcd<Parser<'a> >(&'a str) -> &'a str, self, tag_s!("βçδ"));
    method!(pub tag_hij<Parser<'a> >(&'a str) -> &'a str, self, tag_s!("λïJ"));
    method!(pub tag_ijk<Parser<'a>, &'a str, &'a str>, self, tag_s!("ïJƙ"));
    method!(take3<Parser<'a>, &'a str, &'a str>, self, take_s!(3));
    method!(pub simple_call<Parser<'a>, &'a str, &'a str>, mut self,
      call_m!(self.tag_abc)
    );
    method!(pub simple_peek<Parser<'a>, &'a str, &'a str>, mut self,
      peek!(call_m!(self.take3))
    );
    method!(pub simple_chain<Parser<'a>, &'a str, &'a str>, mut self,
      do_parse!(
         map!(call_m!(self.tag_bcd), |bcd| self.bcd = bcd) >>
         last: call_m!(self.simple_peek)                   >>
         (last)
      )
    );
    fn tag_stuff(mut self: Parser<'a>, input: &'a str, something: &'a str) -> (Parser<'a>, ::IResult<&'a str, &'a str>) {
      self.bcd = something;
      let(tmp, res) = self.tag_abc(input);
      self = tmp;
      (self, res)
    }
    method!(use_apply<Parser<'a>, &'a str, &'a str>, mut self, apply_m!(self.tag_stuff, "βçδ"));
  }

  #[test]
  fn test_method_call_abc() {
    let p = Parser::new();
    let input: &str = "áβçδèƒϱλïJƙ";
    let consumed: &str = "áβç";
    let leftover: &str = "δèƒϱλïJƙ";
    let(_, res) = p.tag_abc(input);
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.tag_abc` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.tag_abc` doesnt return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.tag_abc` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_bcd() {
    let p = Parser::new();
    let input: &str = "βçδèƒϱλïJƙ";
    let consumed: &str = "βçδ";
    let leftover: &str = "èƒϱλïJƙ";
    let(_, res) = p.tag_bcd(input);
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.tag_bcd` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.tag_bcd` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.tag_bcd` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_hij() {
    let p = Parser::new();
    let input: &str = "λïJƙℓ₥ñôƥ9řƨ";
    let consumed: &str = "λïJ";
    let leftover: &str = "ƙℓ₥ñôƥ9řƨ";
    let(_, res) = p.tag_hij(input);
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.tag_hij` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.tag_hij` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.tag_hij` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_ijk() {
    let p = Parser::new();
    let input: &str = "ïJƙℓ₥ñôƥ9řƨ";
    let consumed: &str = "ïJƙ";
    let leftover: &str = "ℓ₥ñôƥ9řƨ";
    let(_, res) = p.tag_ijk(input);
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.tag_ijk` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.tag_ijk` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.tag_ijk` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }
  #[test]
  fn test_method_simple_call() {
    let p = Parser::new();
    let input: &str = "áβçδèƒϱλïJƙ";
    let consumed: &str = "áβç";
    let leftover: &str = "δèƒϱλïJƙ";
    let(_, res) = p.simple_call(input);
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.simple_call` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.simple_call` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.simple_call` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_apply_m() {
    let mut p = Parser::new();
    let input: &str = "áβçδèƒϱλïJƙ";
    let consumed: &str = "áβç";
    let leftover: &str = "δèƒϱλïJƙ";
    let(tmp, res) = p.use_apply(input);
    p = tmp;
    match res {
      Done(extra, output) => { assert!(extra == leftover, "`Parser.use_apply` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.use_apply` doesn't return the string it was supposed to \
                                on success. Expected `{}`, got `{}`.", leftover, output);
                               assert!(p.bcd == "βçδ", "Parser.use_apply didn't modify the parser field correctly: {}", p.bcd);
                             },
      other => panic!("`Parser.use_apply` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  } 

  #[test]
  fn test_method_call_peek() {
    let p = Parser::new();
    let input: &str = "ж¥ƺáβçδèƒϱλïJƙ";
    let consumed: &str = "ж¥ƺ";
    let(_, res) = p.simple_peek(input);
    match res {
      Done(extra, output) => { assert!(extra == input, "`Parser.simple_peek` consumed leftover input. leftover: {}", extra);
                               assert!(output == consumed, "`Parser.simple_peek` doesn't return the string it consumed \
                                on success. Expected `{}`, got `{}`.", consumed, output);
                             },
      other => panic!("`Parser.simple_peek` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }

  #[test]
  fn test_method_call_chain() {
    let mut p = Parser::new();
    let input : &str = "βçδδèƒϱλïJƙℓ";
    let leftover : &str = "δèƒϱλïJƙℓ";
    let output : &str = "δèƒ";
    let(tmp, res) = p.simple_chain(input);
    p = tmp;
    match res {
      Done(extra, out) => { assert!(extra == leftover, "`Parser.simple_chain` consumed leftover input. leftover: {}", extra);
                               assert!(out == output, "`Parser.simple_chain` doesn't return the string it was supposed to \
                                on success. Expected `{}`, got `{}`.", output, out);
                               assert!(p.bcd == "βçδ", "Parser.simple_chain didn't modify the parser field correctly: {}", p.bcd);
                             },
      other => panic!("`Parser.simple_chain` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    }
  }
}
