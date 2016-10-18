//! Support for whitespace delimited formats
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
    terminated_wrap!($i, $separator, $submac!($($args)*), call!($g));
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


#[macro_export]
macro_rules! eat_separator (
  ($i:expr, $arr:expr) => (
    {
      use $crate::{InputLength,IterIndices,Slice};
      if ($i).input_len() == 0 {
        $crate::IResult::Done($i, ($i).slice(0..0))
      } else {
        match ($i).iter_indices().position(|(_, item)| {
          for (_,c) in ($arr).iter_indices() {
            if c == item { return false; }
          }
          true
        }) {
          Some(index) => {
            $crate::IResult::Done(($i).slice(index..), ($i).slice(..index))
          },
          None        => {
            $crate::IResult::Done(($i).slice(($i).input_len()..), $i)
          }
        }
      }
    }
  );
);

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
  ($i:expr, $separator:ident, $submac:ident!( $($args:tt)* )) => {
    wrap_sep!($i, $separator, $submac!($($args)*))
  };
  ($i:expr, $separator:ident, $f:expr) => {
    wrap_sep!($i, $separator, call!($f))
  };
);

named!(pub sp, eat_separator!(b" \t\r\n"));

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
}
