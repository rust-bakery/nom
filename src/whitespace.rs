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
          $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
          $crate::IResult::Done(i2,o)    => {
            match ($separator)(i2) {
              $crate::IResult::Error(e)      => $crate::IResult::Error(e),
              $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
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
macro_rules! eat_separator (
  ($i:expr, $arr:expr) => (
    {
      use $crate::traits::{InputLength,IterIndices,Slice};
      if ($i).input_len() == 0 {
        $crate::IResult::Done($i, &($i)[0..0])
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
  use super::sp;

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
}
