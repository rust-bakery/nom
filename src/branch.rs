/// Try a list of parsers and return the result of the first successful one
///
/// ```rust,ignore
/// alt!(I -> IResult<I,O> | I -> IResult<I,O> | ... | I -> IResult<I,O> ) => I -> IResult<I, O>
/// ```
/// All the parsers must have the same return type.
///
/// If one of the parsers returns `Incomplete`, `alt!` will return `Incomplete`, to retry
/// once you get more input. Note that it is better for performance to know the
/// minimum size of data you need before you get into `alt!`.
///
/// The `alt!` combinator is used in the following way:
///
/// ```rust,ignore
/// alt!(parser_1 | parser_2 | ... | parser_n)
/// ```
///
/// # Basic example
///
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  // Create a parser that will match either "dragon" or "beast"
///  named!( dragon_or_beast, alt!( tag!( "dragon" ) | tag!( "beast" ) ) );
///
///  // Given the input "dragon slayer", the parser will match "dragon"
///  // and the rest will be " slayer"
///  let (rest, result) = dragon_or_beast(b"dragon slayer").unwrap();
///  assert_eq!(result, b"dragon");
///  assert_eq!(rest, b" slayer");
///
///  // Given the input "beast of Gevaudan", the parser will match "beast"
///  // and the rest will be " of Gevaudan"
///  let (rest, result) = dragon_or_beast(&b"beast of Gevaudan"[..]).unwrap();
///  assert_eq!(result, b"beast");
///  assert_eq!(rest, b" of Gevaudan");
///  # }
/// ```
///
/// # Manipulate results
///
/// There exists another syntax for `alt!` that gives you the ability to
/// manipulate the result from each parser:
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
/// #
/// // We create an enum to represent our creatures
/// #[derive(Debug,PartialEq,Eq)]
/// enum Creature {
///     Dragon,
///     Beast,
///     Unknown(usize)
/// }
///
/// // Let's make a helper function that returns true when not a space
/// // we are required to do this because the `take_while!` macro is limited
/// // to idents, so we can't negate `ìs_space` at the call site
/// fn is_not_space(c: u8) -> bool { ! nom::is_space(c) }
///
/// // Our parser will return the `Dragon` variant when matching "dragon",
/// // the `Beast` variant when matching "beast" and otherwise it will consume
/// // the input until a space is found and return an `Unknown` creature with
/// // the size of it's name.
/// named!(creature<Creature>, alt!(
///     tag!("dragon")            => { |_| Creature::Dragon } |
///     tag!("beast")             => { |_| Creature::Beast }  |
///     take_while!(is_not_space) => { |r: &[u8]| Creature::Unknown(r.len()) }
///     // the closure takes the result as argument if the parser is successful
/// ));
///
/// // Given the input "dragon slayer" the parser will return `Creature::Dragon`
/// // and the rest will be " slayer"
/// let (rest, result) = creature(b"dragon slayer").unwrap();
/// assert_eq!(result, Creature::Dragon);
/// assert_eq!(rest, b" slayer");
///
/// // Given the input "beast of Gevaudan" the parser will return `Creature::Beast`
/// // and the rest will be " of Gevaudan"
/// let (rest, result) = creature(b"beast of Gevaudan").unwrap();
/// assert_eq!(result, Creature::Beast);
/// assert_eq!(rest, b" of Gevaudan");
///
/// // Given the input "demon hunter" the parser will return `Creature::Unkown(5)`
/// // and the rest will be " hunter"
/// let (rest, result) = creature(b"demon hunter").unwrap();
/// assert_eq!(result, Creature::Unknown(5));
/// assert_eq!(rest, b" hunter");
/// # }
/// ```
///
/// # Behaviour of `alt!`
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
///          eof!()
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
  (__impl $i:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)* ) => (
    compiler_error!("alt uses '|' as separator, not ',':

      alt!(
        tag!(\"abcd\") |
        tag!(\"efgh\") |
        tag!(\"ijkl\")
      )
    ");
  );
  (__impl $i:expr, $e:ident, $($rest:tt)* ) => (
    alt!(__impl $i, call!($e) , $($rest)*);
  );
  (__impl $i:expr, $e:ident | $($rest:tt)*) => (
    alt!(__impl $i, call!($e) | $($rest)*);
  );

  (__impl $i:expr, $subrule:ident!( $($args:tt)*) | $($rest:tt)*) => (
    {
      let i_ = $i.clone();
      let res = $subrule!(i_, $($args)*);
      match res {
        $crate::IResult::Done(_,_)     => res,
        $crate::IResult::Incomplete(_) => res,
        $crate::IResult::Error(e)      => {
          let out = alt!(__impl $i, $($rest)*);

          // Compile-time hack to ensure that res's E type is not under-specified.
          // This all has no effect at runtime.
          fn unify_types<T>(_: &T, _: &T) {}
          if let $crate::IResult::Error(ref e2) = out {
            unify_types(&e, e2);
          }

          out
        }
      }
    }
  );

  (__impl $i:expr, $subrule:ident!( $($args:tt)* ) => { $gen:expr } | $($rest:tt)*) => (
    {
      let i_ = $i.clone();
      match $subrule!(i_, $($args)* ) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,$gen(o)),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(e)      => {
          let out = alt!(__impl $i, $($rest)*);

          // Compile-time hack to ensure that res's E type is not under-specified.
          // This all has no effect at runtime.
          fn unify_types<T>(_: &T, _: &T) {}
          if let $crate::IResult::Error(ref e2) = out {
            unify_types(&e, e2);
          }

          out
        }
      }
    }
  );

  (__impl $i:expr, $e:ident => { $gen:expr } | $($rest:tt)*) => (
    alt!(__impl $i, call!($e) => { $gen } | $($rest)*);
  );

  (__impl $i:expr, __end) => (
    $crate::IResult::Error(error_position!($crate::ErrorKind::Alt,$i))
  );

  ($i:expr, $($rest:tt)*) => (
    {
      alt!(__impl $i, $($rest)* | __end)
    }
  );
);

/// Is equivalent to the `alt!` combinator, except that it will not return `Incomplete`
/// when one of the constituting parsers returns `Incomplete`. Instead, it will try the
/// next alternative in the chain.
///
/// You should use this combinator only if you know you
/// will not receive partial input for the rules you're trying to match (this
/// is almost always the case for parsing programming languages).
///
/// ```rust,ignore
/// alt_complete!(I -> IResult<I,O> | I -> IResult<I,O> | ... | I -> IResult<I,O> ) => I -> IResult<I, O>
/// ```
/// All the parsers must have the same return type.
///
/// If one of the parsers return `Incomplete`, `alt_complete!` will try the next alternative.
/// If there is no other parser left to try, an `Error` will be returned.
///
/// ```rust,ignore
/// alt_complete!(parser_1 | parser_2 | ... | parser_n)
/// ```
/// **For more in depth examples, refer to the documentation of `alt!`**
#[macro_export]
macro_rules! alt_complete (
  // Recursive rules (must include `complete!` around the head)

  ($i:expr, $e:ident | $($rest:tt)*) => (
    alt_complete!($i, complete!(call!($e)) | $($rest)*);
  );

  ($i:expr, $subrule:ident!( $($args:tt)*) | $($rest:tt)*) => (
    {
      let i_ = $i.clone();
      let res = complete!(i_, $subrule!($($args)*));
      match res {
        $crate::IResult::Done(_,_) => res,
        e => {
          let out = alt_complete!($i, $($rest)*);

          if let (&$crate::IResult::Error(ref e1), &$crate::IResult::Error(ref e2)) = (&e, &out) {
            // Compile-time hack to ensure that res's E type is not under-specified.
            // This all has no effect at runtime.
            fn unify_types<T>(_: &T, _: &T) {}
            unify_types(e1, e2);
          }

          out
        },
      }
    }
  );

  ($i:expr, $subrule:ident!( $($args:tt)* ) => { $gen:expr } | $($rest:tt)+) => (
    {
      let i_ = $i.clone();
      match complete!(i_, $subrule!($($args)*)) {
        $crate::IResult::Done(i,o) => $crate::IResult::Done(i,$gen(o)),
        e => {
          let out = alt_complete!($i, $($rest)*);

          if let (&$crate::IResult::Error(ref e1), &$crate::IResult::Error(ref e2)) = (&e, &out) {
            // Compile-time hack to ensure that res's E type is not under-specified.
            // This all has no effect at runtime.
            fn unify_types<T>(_: &T, _: &T) {}
            unify_types(e1, e2);
          }

          out
        },
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
    alt!(__impl $i, complete!($subrule!($($args)*)) => { $gen } | __end)
  );

  ($i:expr, $e:ident) => (
    alt_complete!($i, call!($e));
  );

  ($i:expr, $subrule:ident!( $($args:tt)*)) => (
    alt!(__impl $i, complete!($subrule!($($args)*)) | __end)
  );
);

/// `switch!(I -> IResult<I,P>, P => I -> IResult<I,O> | ... | P => I -> IResult<I,O> ) => I -> IResult<I, O>`
/// choose the next parser depending on the result of the first one, if successful,
/// and returns the result of the second parser
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done,Error};
/// # #[cfg(feature = "verbose-errors")]
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
///  assert_eq!(sw(&b[..]), Error(error_node_position!(ErrorKind::Switch, &b"abcdef"[..],
///    error_position!(ErrorKind::Tag, &b"ef"[..]))));
///  assert_eq!(sw(&c[..]), Done(&b""[..], &b"123"[..]));
///  assert_eq!(sw(&d[..]), Error(error_position!(ErrorKind::Switch, &b"blah"[..])));
///  # }
/// ```
///
/// You can specify a default case like with a normal match, using `_`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(sw,
///    switch!(take!(4),
///      b"abcd" => tag!("XYZ") |
///      _       => value!(&b"default"[..])
///    )
///  );
///
///  let a = b"abcdXYZ123";
///  let b = b"blah";
///
///  assert_eq!(sw(&a[..]), Done(&b"123"[..], &b"XYZ"[..]));
///  assert_eq!(sw(&b[..]), Done(&b""[..], &b"default"[..]));
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
  (__impl $i:expr, $submac:ident!( $($args:tt)* ), $($p:pat => $subrule:ident!( $($args2:tt)* ))|* ) => (
    {
      let i_ = $i.clone();
      match map!(i_, $submac!($($args)*), |o| Some(o)) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(error_node_position!(
            $crate::ErrorKind::Switch, $i, e
        )),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i, o)    => {
          match o {
            $(Some($p) => match $subrule!(i, $($args2)*) {
              $crate::IResult::Error(e) => $crate::IResult::Error(error_node_position!(
                  $crate::ErrorKind::Switch, $i, e
              )),
              a => a,
            }),*,
            _    => $crate::IResult::Error(error_position!($crate::ErrorKind::Switch,$i))
          }
        }
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)*), $($rest:tt)*) => (
    {
      switch!(__impl $i, $submac!($($args)*), $($rest)*)
    }
  );
  ($i:expr, $e:ident, $($rest:tt)*) => (
    {
      switch!(__impl $i, call!($e), $($rest)*)
    }
  );
);

///
///
/// `permutation!(I -> IResult<I,A>, I -> IResult<I,B>, ... I -> IResult<I,X> ) => I -> IResult<I, (A,B,...X)>`
/// applies its sub parsers in a sequence, but independent from their order
/// this parser will only succeed if all of its sub parsers succeed
///
/// the tuple of results is in the same order as the parsers are declared
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done,Error,Incomplete};
/// # use nom::{ErrorKind,Needed};
/// # fn main() {
/// named!(perm<(&[u8], &[u8], &[u8])>,
///   permutation!(tag!("abcd"), tag!("efg"), tag!("hi"))
/// );
///
/// // whatever the order, if the parser succeeds, each
/// // tag should have matched correctly
/// let expected = (&b"abcd"[..], &b"efg"[..], &b"hi"[..]);
///
/// let a = &b"abcdefghijk"[..];
/// assert_eq!(perm(a), Done(&b"jk"[..], expected));
/// let b = &b"efgabcdhijkl"[..];
/// assert_eq!(perm(b), Done(&b"jkl"[..], expected));
/// let c = &b"hiefgabcdjklm"[..];
/// assert_eq!(perm(c), Done(&b"jklm"[..], expected));
///
/// let d = &b"efgxyzabcdefghi"[..];
/// assert_eq!(perm(d), Error(error_position!(ErrorKind::Permutation, &b"xyzabcdefghi"[..])));
///
/// let e = &b"efgabc"[..];
/// assert_eq!(perm(e), Incomplete(Needed::Size(7)));
/// # }
/// ```
#[macro_export]
macro_rules! permutation (
  ($i:expr, $($rest:tt)*) => (
    {
      let mut res    = permutation_init!((), $($rest)*);
      let mut input  = $i;
      let mut error  = ::std::option::Option::None;
      let mut needed = ::std::option::Option::None;

      loop {
        let mut all_done = true;
        permutation_iterator!(0, input, all_done, needed, res, $($rest)*);

        //if we reach that part, it means none of the parsers were able to read anything
        if !all_done {
          //FIXME: should wrap the error returned by the child parser
          error = ::std::option::Option::Some(error_position!($crate::ErrorKind::Permutation, input));
        }
        break;
      }

      if let ::std::option::Option::Some(need) = needed {
        if let $crate::Needed::Size(sz) = need {
          $crate::IResult::Incomplete(
            $crate::Needed::Size(
              $crate::InputLength::input_len(&($i))  -
              $crate::InputLength::input_len(&input) +
              sz
            )
          )
        } else {
          $crate::IResult::Incomplete($crate::Needed::Unknown)
        }
      } else if let ::std::option::Option::Some(e) = error {
        $crate::IResult::Error(e)
      } else {
        let unwrapped_res = permutation_unwrap!(0, (), res, $($rest)*);
        $crate::IResult::Done(input, unwrapped_res)
      }
    }
  );
);


#[doc(hidden)]
#[macro_export]
macro_rules! permutation_init (
  ((), $e:ident, $($rest:tt)*) => (
    permutation_init!((::std::option::Option::None), $($rest)*)
  );
  ((), $submac:ident!( $($args:tt)* ), $($rest:tt)*) => (
    permutation_init!((::std::option::Option::None), $($rest)*)
  );
  (($($parsed:expr),*), $e:ident, $($rest:tt)*) => (
    permutation_init!(($($parsed),* , ::std::option::Option::None), $($rest)*);
  );
  (($($parsed:expr),*), $submac:ident!( $($args:tt)* ), $($rest:tt)*) => (
    permutation_init!(($($parsed),* , ::std::option::Option::None), $($rest)*);
  );
  (($($parsed:expr),*), $e:ident) => (
    ($($parsed),* , ::std::option::Option::None)
  );
  (($($parsed:expr),*), $submac:ident!( $($args:tt)* )) => (
    ($($parsed),* , ::std::option::Option::None)
  );
  (($($parsed:expr),*),) => (
    ($($parsed),*)
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! succ (
  (0, $submac:ident ! ($($rest:tt)*)) => ($submac!(1, $($rest)*));
  (1, $submac:ident ! ($($rest:tt)*)) => ($submac!(2, $($rest)*));
  (2, $submac:ident ! ($($rest:tt)*)) => ($submac!(3, $($rest)*));
  (3, $submac:ident ! ($($rest:tt)*)) => ($submac!(4, $($rest)*));
  (4, $submac:ident ! ($($rest:tt)*)) => ($submac!(5, $($rest)*));
  (5, $submac:ident ! ($($rest:tt)*)) => ($submac!(6, $($rest)*));
  (6, $submac:ident ! ($($rest:tt)*)) => ($submac!(7, $($rest)*));
  (7, $submac:ident ! ($($rest:tt)*)) => ($submac!(8, $($rest)*));
  (8, $submac:ident ! ($($rest:tt)*)) => ($submac!(9, $($rest)*));
  (9, $submac:ident ! ($($rest:tt)*)) => ($submac!(10, $($rest)*));
  (10, $submac:ident ! ($($rest:tt)*)) => ($submac!(11, $($rest)*));
  (11, $submac:ident ! ($($rest:tt)*)) => ($submac!(12, $($rest)*));
  (12, $submac:ident ! ($($rest:tt)*)) => ($submac!(13, $($rest)*));
  (13, $submac:ident ! ($($rest:tt)*)) => ($submac!(14, $($rest)*));
  (14, $submac:ident ! ($($rest:tt)*)) => ($submac!(15, $($rest)*));
  (15, $submac:ident ! ($($rest:tt)*)) => ($submac!(16, $($rest)*));
  (16, $submac:ident ! ($($rest:tt)*)) => ($submac!(17, $($rest)*));
  (17, $submac:ident ! ($($rest:tt)*)) => ($submac!(18, $($rest)*));
  (18, $submac:ident ! ($($rest:tt)*)) => ($submac!(19, $($rest)*));
  (19, $submac:ident ! ($($rest:tt)*)) => ($submac!(20, $($rest)*));
);

// HACK: for some reason, Rust 1.11 does not accept $res.$it in
// permutation_unwrap. This is a bit ugly, but it will have no
// impact on the generated code
#[doc(hidden)]
#[macro_export]
macro_rules! acc (
  (0, $tup:expr) => ($tup.0);
  (1, $tup:expr) => ($tup.1);
  (2, $tup:expr) => ($tup.2);
  (3, $tup:expr) => ($tup.3);
  (4, $tup:expr) => ($tup.4);
  (5, $tup:expr) => ($tup.5);
  (6, $tup:expr) => ($tup.6);
  (7, $tup:expr) => ($tup.7);
  (8, $tup:expr) => ($tup.8);
  (9, $tup:expr) => ($tup.9);
  (10, $tup:expr) => ($tup.10);
  (11, $tup:expr) => ($tup.11);
  (12, $tup:expr) => ($tup.12);
  (13, $tup:expr) => ($tup.13);
  (14, $tup:expr) => ($tup.14);
  (15, $tup:expr) => ($tup.15);
  (16, $tup:expr) => ($tup.16);
  (17, $tup:expr) => ($tup.17);
  (18, $tup:expr) => ($tup.18);
  (19, $tup:expr) => ($tup.19);
  (20, $tup:expr) => ($tup.20);
);

#[doc(hidden)]
#[macro_export]
macro_rules! permutation_unwrap (
  ($it:tt,  (), $res:ident, $submac:ident!( $($args:tt)* ), $($rest:tt)*) => (
    succ!($it, permutation_unwrap!((acc!($it, $res).unwrap()), $res, $($rest)*));
  );
  ($it:tt, ($($parsed:expr),*), $res:ident, $e:ident, $($rest:tt)*) => (
    succ!($it, permutation_unwrap!(($($parsed),* , acc!($it, $res).unwrap()), $res, $($rest)*));
  );
  ($it:tt, ($($parsed:expr),*), $res:ident, $submac:ident!( $($args:tt)* ), $($rest:tt)*) => (
    succ!($it, permutation_unwrap!(($($parsed),* , acc!($it, $res).unwrap()), $res, $($rest)*));
  );
  ($it:tt, ($($parsed:expr),*), $res:ident, $e:ident) => (
    ($($parsed),* , { acc!($it, $res).unwrap() })
  );
  ($it:tt, ($($parsed:expr),*), $res:ident, $submac:ident!( $($args:tt)* )) => (
    ($($parsed),* , acc!($it, $res).unwrap() )
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! permutation_iterator (
  ($it:tt,$i:expr, $all_done:expr, $needed:expr, $res:expr, $e:ident, $($rest:tt)*) => (
    permutation_iterator!($it, $i, $all_done, $needed, $res, call!($e), $($rest)*);
  );
  ($it:tt, $i:expr, $all_done:expr, $needed:expr, $res:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)*) => {
    if acc!($it, $res) == ::std::option::Option::None {
      match $submac!($i, $($args)*) {
        $crate::IResult::Done(i,o)     => {
          $i = i;
          acc!($it, $res) = ::std::option::Option::Some(o);
          continue;
        },
        $crate::IResult::Error(_) => {
          $all_done = false;
        },
        $crate::IResult::Incomplete(i) => {
          $needed = ::std::option::Option::Some(i);
          break;
        }
      };
    }
    succ!($it, permutation_iterator!($i, $all_done, $needed, $res, $($rest)*));
  };
  ($it:tt,$i:expr, $all_done:expr, $needed:expr, $res:expr, $e:ident) => (
    permutation_iterator!($it, $i, $all_done, $res, call!($e));
  );
  ($it:tt, $i:expr, $all_done:expr, $needed:expr, $res:expr, $submac:ident!( $($args:tt)* )) => {
    if acc!($it, $res) == ::std::option::Option::None {
      match $submac!($i, $($args)*) {
        $crate::IResult::Done(i,o)     => {
          $i = i;
          acc!($it, $res) = ::std::option::Option::Some(o);
          continue;
        },
        $crate::IResult::Error(_) => {
          $all_done = false;
        },
        $crate::IResult::Incomplete(i) => {
          $needed = ::std::option::Option::Some(i);
          break;
        }
      };
    }
  };
);

#[cfg(test)]
mod tests {
  use internal::{Needed,IResult};
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

#[test]
  fn alt() {
    fn work(input: &[u8]) -> IResult<&[u8],&[u8], &'static str> {
      Done(&b""[..], input)
    }

    #[allow(unused_variables)]
    fn dont_work(input: &[u8]) -> IResult<&[u8],&[u8],&'static str> {
      Error(error_code!(ErrorKind::Custom("abcd")))
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
    assert_eq!(alt1(a), Error(error_position!(ErrorKind::Alt, a)));
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

    // compile-time test guarding against an underspecified E generic type (#474)
    named!(alt_eof1, alt!(eof!() | eof!()));
    named!(alt_eof2, alt!(eof!() => {|x| x} | eof!() => {|x| x}));
    let _ = (alt_eof1, alt_eof2);

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
    assert_eq!(alt1(a), Error(error_position!(ErrorKind::Alt, a)));
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
    assert_eq!(ac(a), Error(error_position!(ErrorKind::Alt, a)));
    let a = &b"ef"[..];
    assert_eq!(ac(a), Done(&b""[..], &b"ef"[..]));
    let a = &b"cde"[..];
    assert_eq!(ac(a), Error(error_position!(ErrorKind::Alt, a)));
  }

  #[allow(unused_variables)]
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
    assert_eq!(sw(c), Error(error_position!(ErrorKind::Switch, &b"afghijkl"[..])));
  }

  #[test]
  fn permutation() {
    //trace_macros!(true);
    named!(perm<(&[u8], &[u8], &[u8])>,
      permutation!(tag!("abcd"), tag!("efg"), tag!("hi"))
    );
    //trace_macros!(false);

    let expected = (&b"abcd"[..], &b"efg"[..], &b"hi"[..]);

    let a = &b"abcdefghijk"[..];
    assert_eq!(perm(a), Done(&b"jk"[..], expected));
    let b = &b"efgabcdhijk"[..];
    assert_eq!(perm(b), Done(&b"jk"[..], expected));
    let c = &b"hiefgabcdjk"[..];
    assert_eq!(perm(c), Done(&b"jk"[..], expected));

    let d = &b"efgxyzabcdefghi"[..];
    assert_eq!(perm(d), Error(error_position!(ErrorKind::Permutation, &b"xyzabcdefghi"[..])));

    let e = &b"efgabc"[..];
    assert_eq!(perm(e), Incomplete(Needed::Size(7)));
  }

  /*
  named!(does_not_compile,
    alt!(tag!("abcd"), tag!("efgh"))
  );
  */
}
