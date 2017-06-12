//! Support for whitespace delimited formats
//!
//! a lot of textual formats allows spaces and other
//! types of separators between tokens. Handling it
//! manually with nom means wrapping all parsers
//! like this:
//!
//! ```ignore
//! named!(token, delimited!(space, tk, space));
//! ```
//!
//! To ease the development of such parsers, you
//! can use the whitespace parsing facility, which works
//! as follows:
//!
//! ```
//! # #[macro_use] extern crate nom;
//! # use nom::IResult::Done;
//! # fn main() {
//! named!(tuple<&[u8], (&[u8], &[u8]) >,
//!   ws!(tuple!( take!(3), tag!("de") ))
//! );
//!
//! assert_eq!(
//!   tuple(&b" \t abc de fg"[..]),
//!   Done(&b"fg"[..], (&b"abc"[..], &b"de"[..]))
//! );
//! # }
//! ```
//!
//! The `ws!` combinator will modify the parser to
//! intersperse space parsers everywhere. By default,
//! it will consume the following characters: " \t\r\n".
//!
//! If you want to modify that behaviour, you can make
//! your own whitespace wrapper. As an example, if
//! you don't want to consume ends of lines, only
//! spaces and tabs, you can do it like this:
//!
//! ```
//! # #[macro_use] extern crate nom;
//! # use nom::IResult::Done;
//! named!(pub space, eat_separator!(&b" \t"[..]));
//!
//! #[macro_export]
//! macro_rules! sp (
//!   ($i:expr, $($args:tt)*) => (
//!     {
//!       sep!($i, space, $($args)*)
//!     }
//!   )
//! );
//!
//! # fn main() {
//! named!(tuple<&[u8], (&[u8], &[u8]) >,
//!   sp!(tuple!( take!(3), tag!("de") ))
//! );
//!
//! assert_eq!(
//!   tuple(&b" \t abc de fg"[..]),
//!   Done(&b"fg"[..], (&b"abc"[..], &b"de"[..]))
//! );
//! # }
//! ```
//!
//! This combinator works by replacing each combinator with
//! a version that supports wrapping with separator parsers.
//! It will not support the combinators you wrote in your
//! own code. You can still manually wrap them with the separator
//! you want, or you can copy the macros defined in src/whitespace.rs
//! and modify them to support a new combinator:
//! * copy the combinator's code here, add the _sep suffix
//! * add the `$separator:expr` as second argument
//! * wrap any sub parsers with sep!($separator, $submac!($($args)*))
//! * reference it in the definition of `sep!` as follows:
//!
//! ```ignore
//!  ($i:expr,  $separator:ident, my_combinator ! ($($rest:tt)*) ) => {
//!    wrap_sep!($i,
//!      $separator,
//!      my_combinator_sep!($separator, $($rest)*)
//!    )
//!  };
//! ```
//!

#[macro_export]
macro_rules! wrap_sep (
  ($i:expr, $separator:expr, $submac:ident!( $($args:tt)* )) => (
    match ($separator)($i) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(i1,_)    => {
        match $submac!(i1, $($args)*) {
          $crate::IResult::Error(e)      => $crate::IResult::Error(e),
          $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i + ($crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i1)))),
          $crate::IResult::Done(i2,o)    => {
            match ($separator)(i2) {
              $crate::IResult::Error(e)      => $crate::IResult::Error(e),
              $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
              $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i + ($crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i2)))),
              $crate::IResult::Done(i3,_)    => $crate::IResult::Done(i3, o)
            }
          }
        }
      }
    }
  );
  ($i:expr, $separator:expr, $f:expr) => (
    wrap_sep!($i, $separator, call!($f))
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! pair_sep (
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    tuple!(
      $i,
      sep!($separator, $submac!($($args)*)),
      sep!($separator, $submac2!($($args2)*))
    )
  );
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)* ), $g:expr) => (
    pair_sep!($i, $separator, $submac!($($args)*), call!($g));
  );
  ($i:expr, $separator:ident, $f:expr, $submac:ident!( $($args:tt)* )) => (
    pair_sep!($i, $separator, call!($f), $submac!($($args)*));
  );
  ($i:expr, $separator:ident, $f:expr, $g:expr) => (
    pair_sep!($i, $separator, call!($f), call!($g));
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! delimited_sep (
  ($i:expr, $separator:ident, $submac1:ident!( $($args1:tt)* ), $($rest:tt)+) => (
    match tuple_sep!($i, $separator, 0usize, (), $submac1!($($args1)*), $($rest)*) {
      $crate::IResult::Error(a)                   => $crate::IResult::Error(a),
      $crate::IResult::Incomplete(i)              => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(remaining, (_,o,_)) => {
        $crate::IResult::Done(remaining, o)
      }
    }
  );
  ($i:expr, $separator:ident, $f:expr, $($rest:tt)+) => (
    delimited_sep!($i, $separator, call!($f), $($rest)*);
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! separated_pair_sep (
  ($i:expr, $separator:ident, $submac1:ident!( $($args1:tt)* ), $($rest:tt)+) => (
    match tuple_sep!($i, $separator, 0usize, (), $submac1!($($args1)*), $($rest)*) {
      $crate::IResult::Error(a)                   => $crate::IResult::Error(a),
      $crate::IResult::Incomplete(i)              => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(remaining, (o1,_,o2)) => {
        $crate::IResult::Done(remaining, (o1,o2))
      }
    }
  );
  ($i:expr, $separator:ident, $f:expr, $($rest:tt)+) => (
    separated_pair_sep!($i, $separator, call!($f), $($rest)*);
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! preceded_sep (
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    match pair_sep!($i, $separator, $submac!($($args)*), $submac2!($($args2)*)) {
      $crate::IResult::Error(a)               => $crate::IResult::Error(a),
      $crate::IResult::Incomplete(i)          => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(remaining, (_,o)) => {
        $crate::IResult::Done(remaining, o)
      }
    }
  );
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)* ), $g:expr) => (
    preceded_sep!($i, $separator, $submac!($($args)*), call!($g));
  );
  ($i:expr, $separator:ident, $f:expr, $submac:ident!( $($args:tt)* )) => (
    preceded_sep!($i, $separator, call!($f), $submac!($($args)*));
  );
  ($i:expr, $separator:ident, $f:expr, $g:expr) => (
    preceded_sep!($i, $separator, call!($f), call!($g));
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! terminated_sep (
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    match pair_sep!($i, $separator, $submac!($($args)*), $submac2!($($args2)*)) {
      $crate::IResult::Error(a)               => $crate::IResult::Error(a),
      $crate::IResult::Incomplete(i)          => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(remaining, (o,_)) => {
        $crate::IResult::Done(remaining, o)
      }
    }
  );
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)* ), $g:expr) => (
    terminated_sep!($i, $separator, $submac!($($args)*), call!($g));
  );
  ($i:expr, $separator:ident, $f:expr, $submac:ident!( $($args:tt)* )) => (
    terminated_sep!($i, $separator, call!($f), $submac!($($args)*));
  );
  ($i:expr, $separator:ident, $f:expr, $g:expr) => (
    terminated_sep!($i, $separator, call!($f), call!($g));
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! tuple_sep (
  ($i:expr, $separator:ident, $consumed:expr, ($($parsed:tt),*), $e:ident, $($rest:tt)*) => (
    tuple_sep!($i, $separator, $consumed, ($($parsed),*), call!($e), $($rest)*);
  );
  ($i:expr, $separator:ident, $consumed:expr, (), $submac:ident!( $($args:tt)* ), $($rest:tt)*) => (
    {
      match sep!($i, $separator, $submac!($($args)*)) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          tuple_sep!(i, $separator, $consumed + ($crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i)), (o), $($rest)*)
        }
      }
    }
  );
  ($i:expr, $separator:ident, $consumed:expr, ($($parsed:tt)*), $submac:ident!( $($args:tt)* ), $($rest:tt)*) => (
    {
      match sep!($i, $separator, $submac!($($args)*)) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          tuple_sep!(i, $separator, $consumed + ($crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i)), ($($parsed)* , o), $($rest)*)
        }
      }
    }
  );
  ($i:expr, $separator:ident, $consumed:expr, ($($parsed:tt),*), $e:ident) => (
    tuple_sep!($i, $separator,  $consumed, ($($parsed),*), call!($e));
  );
  ($i:expr, $separator:ident, $consumed:expr, (), $submac:ident!( $($args:tt)* )) => (
    {
      match sep!($i, $separator, $submac!($($args)*)) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          $crate::IResult::Done(i, (o))
        }
      }
    }
  );
  ($i:expr, $separator:ident, $consumed:expr, ($($parsed:expr),*), $submac:ident!( $($args:tt)* )) => (
    {
      match sep!($i, $separator, $submac!($($args)*)) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          $crate::IResult::Done(i, ($($parsed),* , o))
        }
      }
    }
  );
  ($i:expr, $separator:ident, $consumed:expr, ($($parsed:expr),*)) => (
    {
      $crate::IResult::Done($i, ($($parsed),*))
    }
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! do_parse_sep (
  (__impl $i:expr, $separator:ident, $consumed:expr, ( $($rest:expr),* )) => (
    $crate::IResult::Done($i, ( $($rest),* ))
  );

  (__impl $i:expr, $separator:ident, $consumed:expr, $e:ident >> $($rest:tt)*) => (
    do_parse_sep!(__impl $i, $separator, $consumed, call!($e) >> $($rest)*);
  );
  (__impl $i:expr, $separator:ident, $consumed:expr, $submac:ident!( $($args:tt)* ) >> $($rest:tt)*) => (
    {
      match sep!($i, $separator, $submac!($($args)*)) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) =>
          $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,_)     => {
          do_parse_sep!(__impl i, $separator,
            $consumed + ($crate::InputLength::input_len(&($i)) -
                         $crate::InputLength::input_len(&i)), $($rest)*)
        },
      }
    }
  );

  (__impl $i:expr, $separator:ident, $consumed:expr, $field:ident : $e:ident >> $($rest:tt)*) => (
    do_parse_sep!(__impl $i, $separator, $consumed, $field: call!($e) >> $($rest)*);
  );

  (__impl $i:expr, $separator:ident, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ) >> $($rest:tt)*) => (
    {
      match sep!($i, $separator, $submac!($($args)*)) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) =>
          $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
        $crate::IResult::Done(i,o)     => {
          let $field = o;
          do_parse_sep!(__impl i, $separator,
            $consumed + ($crate::InputLength::input_len(&($i)) -
                         $crate::InputLength::input_len(&i)), $($rest)*)
        },
      }
    }
  );

  // ending the chain
  (__impl $i:expr, $separator:ident, $consumed:expr, $e:ident >> ( $($rest:tt)* )) => (
    do_parse_sep!(__impl $i, $separator, $consumed, call!($e) >> ( $($rest)* ));
  );

  (__impl $i:expr, $separator:ident, $consumed:expr, $submac:ident!( $($args:tt)* ) >> ( $($rest:tt)* )) => (
    match sep!($i, $separator, $submac!($($args)*)) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete($crate::Needed::Unknown) =>
        $crate::IResult::Incomplete($crate::Needed::Unknown),
      $crate::IResult::Incomplete($crate::Needed::Size(i)) =>
        $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
      $crate::IResult::Done(i,_)     => {
        $crate::IResult::Done(i, ( $($rest)* ))
      },
    }
  );

  (__impl $i:expr, $separator:ident, $consumed:expr, $field:ident : $e:ident >> ( $($rest:tt)* )) => (
    do_parse_sep!(__impl $i, $separator, $consumed, $field: call!($e) >> ( $($rest)* ) );
  );

  (__impl $i:expr, $separator:ident, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ) >> ( $($rest:tt)* )) => (
    match sep!($i, $separator, $submac!($($args)*)) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete($crate::Needed::Unknown) =>
        $crate::IResult::Incomplete($crate::Needed::Unknown),
      $crate::IResult::Incomplete($crate::Needed::Size(i)) =>
        $crate::IResult::Incomplete($crate::Needed::Size($consumed + i)),
      $crate::IResult::Done(i,o)     => {
        let $field = o;
        $crate::IResult::Done(i, ( $($rest)* ))
      },
    }
  );

  ($i:expr, $separator:ident, $($rest:tt)*) => (
    {
      do_parse_sep!(__impl $i, $separator, 0usize, $($rest)*)
    }
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! permutation_sep (
  ($i:expr, $separator:ident, $($rest:tt)*) => (
    {
      let mut res    = permutation_init!((), $($rest)*);
      let mut input  = $i;
      let mut error  = ::std::option::Option::None;
      let mut needed = ::std::option::Option::None;

      loop {
        let mut all_done = true;
        permutation_iterator_sep!(0, input, $separator, all_done, needed, res, $($rest)*);

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
macro_rules! permutation_iterator_sep (
  ($it:tt,$i:expr, $separator:ident, $all_done:expr, $needed:expr, $res:expr, $e:ident, $($rest:tt)*) => (
    permutation_iterator_sep!($it, $i, $separator, $all_done, $needed, $res, call!($e), $($rest)*);
  );
  ($it:tt, $i:expr, $separator:ident, $all_done:expr, $needed:expr, $res:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)*) => {
    if acc!($it, $res) == ::std::option::Option::None {
      match sep!($i, $separator, $submac!($($args)*)) {
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
    succ!($it, permutation_iterator_sep!($i, $separator, $all_done, $needed, $res, $($rest)*));
  };
  ($it:tt,$i:expr, $separator:ident, $all_done:expr, $needed:expr, $res:expr, $e:ident) => (
    permutation_iterator_sep!($it, $i, $separator, $all_done, $res, call!($e));
  );
  ($it:tt, $i:expr, $separator:ident, $all_done:expr, $needed:expr, $res:expr, $submac:ident!( $($args:tt)* )) => {
    if acc!($it, $res) == ::std::option::Option::None {
      match sep!($i, $separator, $submac!($($args)*)) {
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

#[doc(hidden)]
#[macro_export]
macro_rules! alt_sep (
  (__impl $i:expr, $separator:ident, $e:ident | $($rest:tt)*) => (
    alt_sep!(__impl $i, $separator, call!($e) | $($rest)*);
  );

  (__impl $i:expr, $separator:ident, $subrule:ident!( $($args:tt)*) | $($rest:tt)*) => (
    {
      let res = sep!($i, $separator, $subrule!($($args)*));
      match res {
        $crate::IResult::Done(_,_)     => res,
        $crate::IResult::Incomplete(_) => res,
        _                              => alt_sep!(__impl $i, $separator, $($rest)*)
      }
    }
  );

  (__impl $i:expr, $separator:ident, $subrule:ident!( $($args:tt)* ) => { $gen:expr } | $($rest:tt)+) => (
    {
      match sep!($i, $separator, $subrule!( $($args)* )) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,$gen(o)),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(_)      => {
          alt_sep!(__impl $i, $separator, $($rest)*)
        }
      }
    }
  );

  (__impl $i:expr, $separator:ident, $e:ident => { $gen:expr } | $($rest:tt)*) => (
    alt_sep!(__impl $i, $separator, call!($e) => { $gen } | $($rest)*);
  );

  (__impl $i:expr, $separator:ident, $e:ident => { $gen:expr }) => (
    alt_sep!(__impl $i, $separator, call!($e) => { $gen });
  );

  (__impl $i:expr, $separator:ident, $subrule:ident!( $($args:tt)* ) => { $gen:expr }) => (
    {
      match sep!($i, $separator, $subrule!( $($args)* )) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,$gen(o)),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(_)      => {
          $crate::IResult::Error(error_position!($crate::ErrorKind::Alt,$i))
        }
      }
    }
  );

  (__impl $i:expr, $separator:ident, $e:ident) => (
    alt_sep!(__impl $i, $separator, call!($e));
  );

  (__impl $i:expr, $separator:ident, $subrule:ident!( $($args:tt)*)) => (
    {
      match sep!($i, $separator, $subrule!( $($args)* )) {
        $crate::IResult::Done(i,o)     => $crate::IResult::Done(i,o),
        $crate::IResult::Incomplete(x) => $crate::IResult::Incomplete(x),
        $crate::IResult::Error(_)      => {
          $crate::IResult::Error(error_position!($crate::ErrorKind::Alt,$i))
        }
      }
    }
  );

  (__impl $i:expr) => (
    $crate::IResult::Error(error_position!($crate::ErrorKind::Alt,$i))
  );

  (__impl $i:expr, $separator:ident) => (
    $crate::IResult::Error(error_position!($crate::ErrorKind::Alt,$i))
  );

  ($i:expr, $separator:ident, $($rest:tt)*) => (
    {
      alt_sep!(__impl $i, $separator, $($rest)*)
    }
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! alt_complete_sep (
  ($i:expr, $separator:ident, $e:ident | $($rest:tt)*) => (
    alt_complete_sep!($i, $separator, complete!(call!($e)) | $($rest)*);
  );

  ($i:expr, $separator:ident, $subrule:ident!( $($args:tt)*) | $($rest:tt)*) => (
    {
      let res = complete!($i, sep!($separator, $subrule!($($args)*)));
      match res {
        $crate::IResult::Done(_,_) => res,
        _ => alt_complete_sep!($i, $separator, $($rest)*),
      }
    }
  );

  ($i:expr, $separator:ident, $subrule:ident!( $($args:tt)* ) => { $gen:expr } | $($rest:tt)+) => (
    {
      match complete!($i, sep!($separator, $subrule!($($args)*))) {
        $crate::IResult::Done(i,o) => $crate::IResult::Done(i,$gen(o)),
        _ => alt_complete_sep!($i, $separator, $($rest)*),
      }
    }
  );

  ($i:expr, $separator:ident, $e:ident => { $gen:expr } | $($rest:tt)*) => (
    alt_complete_sep!($i, $separator, complete!(call!($e)) => { $gen } | $($rest)*);
  );

  // Tail (non-recursive) rules

  ($i:expr, $separator:ident, $e:ident => { $gen:expr }) => (
    alt_complete_sep!($i, $separator, call!($e) => { $gen });
  );

  ($i:expr, $separator:ident, $subrule:ident!( $($args:tt)* ) => { $gen:expr }) => (
    alt_sep!(__impl $i, $separator, $subrule!($($args)*) => { $gen })
  );

  ($i:expr, $separator:ident, $e:ident) => (
    alt_complete_sep!($i, $separator, call!($e));
  );

  ($i:expr, $separator:ident, $subrule:ident!( $($args:tt)*)) => (
    alt_sep!(__impl $i, $separator, $subrule!($($args)*))
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! switch_sep (
  (__impl $i:expr, $separator:ident, $submac:ident!( $($args:tt)* ), $($p:pat => $subrule:ident!( $($args2:tt)* ))|* ) => (
    {
      match sep!($i, $separator, $submac!($($args)*)) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(error_node_position!(
            $crate::ErrorKind::Switch, $i, e
        )),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i, o)    => {
          match o {
            $($p => match sep!(i, $separator, $subrule!($($args2)*)) {
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
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)*), $($rest:tt)*) => (
    {
      switch_sep!(__impl $i, $separator, $submac!($($args)*), $($rest)*)
    }
  );
  ($i:expr, $separator:ident, $e:ident, $($rest:tt)*) => (
    {
      switch_sep!(__impl $i, $separator, call!($e), $($rest)*)
    }
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! separated_list_sep (
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    separated_list!(
      $i,
      sep!($separator, $submac!($($args)*)),
      sep!($separator, $submac2!($($args2)*))
    )
  );
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)* ), $g:expr) => (
    separated_list_sep!($i, $separator, $submac!($($args)*), call!($g));
  );
  ($i:expr, $separator:ident, $f:expr, $submac:ident!( $($args:tt)* )) => (
    separated_list_sep!($i, $separator, call!($f), $submac!($($args)*));
  );
  ($i:expr, $separator:ident, $f:expr, $g:expr) => (
    separated_list_sep!($i, $separator, call!($f), call!($g));
  );
);

/// helper macros to build a separator parser
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// named!(pub space, eat_separator!(&b" \t"[..]));
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! eat_separator (
  ($i:expr, $arr:expr) => (
    {
      use $crate::{AsChar,InputLength,InputIter,Slice};
      if ($i).input_len() == 0 {
        $crate::IResult::Done(($i).slice(0..), ($i).slice(0..0))
      } else {
        match ($i).iter_indices().position(|(_, item)| {
          let i = item.as_char();
          for (_,c) in ($arr).iter_indices() {
            if c.as_char() == i { return false; }
          }
          true
        }) {
          ::std::option::Option::Some(index) => {
            $crate::IResult::Done(($i).slice(index..), ($i).slice(..index))
          },
          ::std::option::Option::None        => {
            $crate::IResult::Done(($i).slice(($i).input_len()..), ($i))
          }
        }
      }
    }
  );
);

/// sep is the parser rewriting macro for whitespace separated formats
///
/// it takes as argument a space eating function and a parser tree,
/// and will intersperse the space parser everywhere
///
/// ```ignore
/// #[macro_export]
/// macro_rules! ws (
///   ($i:expr, $($args:tt)*) => (
///     {
///       use $crate::sp;
///       sep!($i, sp, $($args)*)
///     }
///   )
/// );
/// ```
#[macro_export]
macro_rules! sep (
  ($i:expr,  $separator:ident, tuple ! ($($rest:tt)*) ) => {
    tuple_sep!($i, $separator, 0usize, (), $($rest)*)
  };
  ($i:expr,  $separator:ident, pair ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      pair_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, delimited ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      delimited_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, separated_pair ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      separated_pair_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, preceded ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      preceded_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, terminated ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      terminated_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, do_parse ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      do_parse_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, permutation ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      permutation_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, alt ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      alt_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, alt_complete ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      alt_complete_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, switch ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      switch_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, separated_list ! ($($rest:tt)*) ) => {
    wrap_sep!($i,
      $separator,
      separated_list_sep!($separator, $($rest)*)
    )
  };
  ($i:expr,  $separator:ident, many0 ! ($($rest:tt)*) ) => {
    many0!($i, wrap_sep!($separator, $($rest)*))
  };
  ($i:expr,  $separator:ident, many1 ! ($($rest:tt)*) ) => {
    many1!($i, wrap_sep!($separator, $($rest)*))
  };
//FIXME: missing separated_nonempty_list,
// many_till, many_m_n, count, count_fixed, fold_many0, fold_many1,
// fold_many_m_n
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)* )) => {
    wrap_sep!($i, $separator, $submac!($($args)*))
  };
  ($i:expr, $separator:ident, $f:expr) => {
    wrap_sep!($i, $separator, call!($f))
  };
);

use std::ops::{Range,RangeFrom,RangeTo};
use internal::IResult;
#[allow(unused_imports)]
pub fn sp<'a,T>(input:T) -> IResult<T, T> where
  T: ::traits::Slice<Range<usize>>+::traits::Slice<RangeFrom<usize>>+::traits::Slice<RangeTo<usize>>,
    T: ::traits::InputIter+::traits::InputLength,
    <T as ::traits::InputIter>::Item: ::traits::AsChar {
    eat_separator!(input, &b" \t\r\n"[..])
}

/// `ws!(I -> IResult<I,O>) => I -> IResult<I, O>`
///
/// transforms a parser to automatically consume
/// whitespace between each token. By default,
/// it takes the following characters: " \t\r\n".
///
/// If you need a whitespace parser consuming a
/// different set of characters, you can make
/// your own by reusing the `sep!` combinator.
///
/// To use `ws!`, pass your parser as argument:
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
/// named!(tuple<&[u8], (&[u8], &[u8]) >,
///   ws!(tuple!( take!(3), tag!("de") ))
/// );
///
/// assert_eq!(
///   tuple(&b" \t abc de fg"[..]),
///   Done(&b"fg"[..], (&b"abc"[..], &b"de"[..]))
/// );
/// # }
/// ```
///
#[macro_export]
macro_rules! ws (
  ($i:expr, $($args:tt)*) => (
    {
      use $crate::sp;
      sep!($i, sp, $($args)*)
    }
  )
);

#[cfg(test)]
#[allow(dead_code)]
mod tests {
  use internal::IResult::*;
  use internal::{IResult,Needed};
  use super::sp;
  use util::ErrorKind;

  #[test]
  fn spaaaaace() {
    assert_eq!(sp(&b" \t abc "[..]),  Done(&b"abc "[..], &b" \t "[..]));
  }

  #[test]
  fn tag() {
    named!(abc, ws!(tag!("abc")));

    assert_eq!(abc(&b" \t abc def"[..]),  Done(&b"def"[..], &b"abc"[..]));
  }

  #[test]
  fn pair() {
    named!(pair_2<&[u8], (&[u8], &[u8]) >,
      ws!(pair!( take!(3), tag!("de") ))
    );

    assert_eq!(pair_2(&b" \t abc de fg"[..]),  Done(&b"fg"[..], (&b"abc"[..], &b"de"[..])));
  }

  #[test]
  fn preceded() {
    named!(prec<&[u8], &[u8] >,
      ws!(preceded!( take!(3), tag!("de") ))
    );

    assert_eq!(prec(&b" \t abc de fg"[..]),  Done(&b"fg"[..], &b"de"[..]));
  }

  #[test]
  fn terminated() {
    named!(term<&[u8], &[u8] >,
      ws!(terminated!( take!(3), tag!("de") ))
    );

    assert_eq!(term(&b" \t abc de fg"[..]),  Done(&b"fg"[..], &b"abc"[..]));
  }

  #[test]
  fn tuple() {
    //trace_macros!(true);
    named!(tuple_2<&[u8], (&[u8], &[u8]) >,
      ws!(tuple!( take!(3), tag!("de") ))
    );
    //trace_macros!(false);

    assert_eq!(tuple_2(&b" \t abc de fg"[..]),  Done(&b"fg"[..], (&b"abc"[..], &b"de"[..])));
  }

  #[test]
  fn levels() {
    //trace_macros!(true);
    named!(level_2<&[u8], (&[u8], (&[u8], &[u8])) >,
      ws!(pair!(take!(3), tuple!( tag!("de"), tag!("fg ") )))
    );
    //trace_macros!(false);

    assert_eq!(level_2(&b" \t abc de fg \t hi "[..]),  Done(&b"hi "[..], (&b"abc"[..], (&b"de"[..], &b"fg "[..]))));
  }

  #[test]
  fn do_parse() {
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };

    //trace_macros!(true);
    named!(do_parser<&[u8], (u8, u8)>,
      ws!(do_parse!(
        tag!("abcd")       >>
        opt!(tag!("abcd")) >>
        aa: ret_int1       >>
        tag!("efgh")       >>
        bb: ret_int2       >>
        tag!("efgh")       >>
        (aa, bb)
      ))
    );

    //trace_macros!(false);

    assert_eq!(do_parser(&b"abcd abcd\tefghefghX"[..]), Done(&b"X"[..], (1, 2)));
    assert_eq!(do_parser(&b"abcd\tefgh      efgh X"[..]), Done(&b"X"[..], (1, 2)));
    assert_eq!(do_parser(&b"abcd  ab"[..]), Incomplete(Needed::Size(10)));
    assert_eq!(do_parser(&b" abcd\tefgh\tef"[..]), Incomplete(Needed::Size(15)));
  }

  #[test]
  fn permutation() {
    //trace_macros!(true);
    named!(perm<(&[u8], &[u8], &[u8])>,
      ws!(permutation!(tag!("abcd"), tag!("efg"), tag!("hi")))
    );
    //trace_macros!(false);

    let expected = (&b"abcd"[..], &b"efg"[..], &b"hi"[..]);

    let a = &b"abcd\tefg \thijk"[..];
    assert_eq!(perm(a), Done(&b"jk"[..], expected));
    let b = &b"  efg  \tabcdhi jk"[..];
    assert_eq!(perm(b), Done(&b"jk"[..], expected));
    let c = &b" hi   efg\tabcdjk"[..];
    assert_eq!(perm(c), Done(&b"jk"[..], expected));

    let d = &b"efg  xyzabcdefghi"[..];
    assert_eq!(perm(d), Error(error_position!(ErrorKind::Permutation, &b"xyzabcdefghi"[..])));

    let e = &b" efg \tabc"[..];
    assert_eq!(perm(e), Incomplete(Needed::Size(10)));
  }

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

    let a = &b"\tabcd"[..];
    assert_eq!(alt1(a), Error(error_position!(ErrorKind::Alt, a)));
    assert_eq!(alt2(a), Done(&b""[..], a));
    assert_eq!(alt3(a), Done(a, &b""[..]));

    named!(alt4, ws!(alt!(tag!("abcd") | tag!("efgh"))));
    let b = &b"  efgh "[..];
    assert_eq!(alt4(a), Done(&b""[..], &b"abcd"[..]));
    assert_eq!(alt4(b), Done(&b""[..], &b"efgh"[..]));

    // test the alternative syntax
    named!(alt5<bool>, ws!(alt!(tag!("abcd") => { |_| false } | tag!("efgh") => { |_| true })));
    assert_eq!(alt5(a), Done(&b""[..], false));
    assert_eq!(alt5(b), Done(&b""[..], true));
  }

  #[test]
  fn alt_complete() {
    named!(ac<&[u8], &[u8]>,
      ws!(alt_complete!(tag!("abcd") | tag!("ef") | tag!("ghi") | tag!("kl")))
    );

    let a = &b""[..];
    assert_eq!(ac(a), Incomplete(Needed::Size(2)));
    let a = &b" \tef "[..];
    assert_eq!(ac(a), Done(&b""[..], &b"ef"[..]));
    let a = &b" cde"[..];
    assert_eq!(ac(a), Error(error_position!(ErrorKind::Alt, &a[1..])));
  }

  #[allow(unused_variables)]
  #[test]
  fn switch() {
    named!(sw,
      ws!(switch!(take!(4),
        b"abcd" => take!(2) |
        b"efgh" => take!(4)
      ))
    );

    let a = &b" abcd ef gh"[..];
    assert_eq!(sw(a), Done(&b"gh"[..], &b"ef"[..]));

    let b = &b"\tefgh ijkl "[..];
    assert_eq!(sw(b), Done(&b""[..], &b"ijkl"[..]));
    let c = &b"afghijkl"[..];
    assert_eq!(sw(c), Error(error_position!(ErrorKind::Switch, &b"afghijkl"[..])));
  }

  named!(str_parse(&str) -> &str, ws!(tag!("test")));
  #[allow(unused_variables)]
  #[test]
  fn str_test() {
    assert_eq!(str_parse(" \n   test\t a\nb"), Done("a\nb", "test"));
  }

  // test whitespace parser generation for alt
  named!(space, tag!(" "));
  named!(pipeline_statement<&[u8], ()>,
    ws!(
      do_parse!(
      tag!("pipeline") >>
      attributes: delimited!(char!('{'),
                             separated_list!(char!(','), alt!(
                               space |
                               space
                             )),
                             char!('}')) >>

      ( () )
    )
  )
  );

}
