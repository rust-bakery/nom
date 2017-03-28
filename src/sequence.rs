/// `chain!(I->IResult<I,A> ~ I->IResult<I,B> ~ ... I->IResult<I,X> , || { return O } ) => I -> IResult<I, O>`
/// chains parsers and assemble the results through a closure
///
/// this parser is deprecated and will be removed in nom 3.0. You can
/// now replace it with `do_parse!`. The `?` syntax to make a parser
/// optional can be done with the `opt!` combinator.
///
/// There are also combinators available for specific patterns like
/// `pair!`, `tuple!`, `preceded!`, `terminated!`, `delimited!`, etc.
///
/// In lots of cases, there are better solutions than using `chain!`.
///
/// The input type `I` must implement `nom::InputLength`.
///
/// This combinator will count how much data is consumed by every child parser
/// and take it into account if
/// there is not enough data
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Error};
/// # #[cfg(feature = "verbose-errors")]
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
/// assert_eq!(r1, Error(error_position!(ErrorKind::Tag,&b"efgh"[..])));
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
#[deprecated(since="2.0.0", note="please use [`do_parse!`](macro.do_parse.html) instead")]
macro_rules! chain (
  ($i:expr, $($rest:tt)*) => (
    {
      chaining_parser!($i, 0usize, $($rest)*)
    }
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! chaining_parser (
  ($i:expr, $consumed:expr, $e:ident ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, call!($e) ~ $($rest)*);
  );
  ($i:expr, $consumed:expr, $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
        $crate::IResult::Done(i,_)     => {
          chaining_parser!(i,
            $consumed + ($crate::InputLength::input_len(&($i)) -
                         $crate::InputLength::input_len(&i)), $($rest)*)
        }
      }
    }
);

  ($i:expr, $consumed:expr, $e:ident ? ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, call!($e) ? ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => (
    {
      let res = $submac!($i, $($args)*);
      if let $crate::IResult::Incomplete(inc) = res {
        match inc {
          $crate::Needed::Unknown =>
            $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::Needed::Size(i) => {
            let (needed,overflowed) = $consumed.overflowing_add(i);
            match overflowed {
                true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
            }
          },
        }
      } else {
        let input = if let $crate::IResult::Done(i,_) = res {
          i
        } else {
          $i
        };
        chaining_parser!(input,
          $consumed + ($crate::InputLength::input_len(&($i)) -
                       $crate::InputLength::input_len(&input)), $($rest)*)
      }
    }
  );

  ($i:expr, $consumed:expr, $field:ident : $e:ident ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, $field: call!($e) ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    {
      match  $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
        $crate::IResult::Done(i,o)     => {
          let $field = o;
          chaining_parser!(i,
            $consumed + ($crate::InputLength::input_len(&($i)) -
                         $crate::InputLength::input_len(&i)), $($rest)*)
        }
      }
    }
  );

  ($i:expr, $consumed:expr, mut $field:ident : $e:ident ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, mut $field: call!($e) ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, mut $field:ident : $submac:ident!( $($args:tt)* ) ~ $($rest:tt)*) => (
    {
      match  $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
        $crate::IResult::Done(i,o)     => {
          let mut $field = o;
          chaining_parser!(i,
            $consumed + $crate::InputLength::input_len(&($i)) -
                        $crate::InputLength::input_len(&i), $($rest)*)
        }
      }
    }
  );

  ($i:expr, $consumed:expr, $field:ident : $e:ident ? ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, $field : call!($e) ? ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => (
    {
      let res = $submac!($i, $($args)*);
      if let $crate::IResult::Incomplete(inc) = res {
        match inc {
          $crate::Needed::Unknown =>
            $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::Needed::Size(i) => {
            let (needed,overflowed) = $consumed.overflowing_add(i);
            match overflowed {
                true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
            }
          },
        }
      } else {
        let ($field,input) = if let $crate::IResult::Done(i,o) = res {
          (::std::option::Option::Some(o),i)
        } else {
          (::std::option::Option::None,$i)
        };
        chaining_parser!(input,
          $consumed + $crate::InputLength::input_len(&($i)) -
                      $crate::InputLength::input_len(&input), $($rest)*)
      }
    }
  );

  ($i:expr, $consumed:expr, mut $field:ident : $e:ident ? ~ $($rest:tt)*) => (
    chaining_parser!($i, $consumed, mut $field : call!($e) ? ~ $($rest)*);
  );

  ($i:expr, $consumed:expr, mut $field:ident : $submac:ident!( $($args:tt)* ) ? ~ $($rest:tt)*) => (
    {
      let res = $submac!($i, $($args)*);
      if let $crate::IResult::Incomplete(inc) = res {
        match inc {
          $crate::Needed::Unknown =>
            $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::Needed::Size(i) => {
            let (needed,overflowed) = $consumed.overflowing_add(i);
            match overflowed {
                true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
            }
          },
        }
      } else {
        let (mut $field,input) = if let $crate::IResult::Done(i,o) = res {
          (::std::option::Option::Some(o),i)
        } else {
          (::std::option::Option::None,$i)
        };
        chaining_parser!(input,
          $consumed + $crate::InputLength::input_len(&($i)) -
                      $crate::InputLength::input_len(&input), $($rest)*)
      }
    }
  );

  // ending the chain
  ($i:expr, $consumed:expr, $e:ident, $assemble:expr) => (
    chaining_parser!($i, $consumed, call!($e), $assemble);
  );

  ($i:expr, $consumed:expr, $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete($crate::Needed::Unknown) =>
        $crate::IResult::Incomplete($crate::Needed::Unknown),
      $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
        let (needed,overflowed) = $consumed.overflowing_add(i);
        match overflowed {
            true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
            false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
        }
      },
      $crate::IResult::Done(i,_)     => {
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $consumed:expr, $e:ident ?, $assemble:expr) => (
    chaining_parser!($i, $consumed, call!($e) ?, $assemble);
  );

  ($i:expr, $consumed:expr, $submac:ident!( $($args:tt)* ) ?, $assemble:expr) => ({
    let res = $submac!($i, $($args)*);
    if let $crate::IResult::Incomplete(inc) = res {
      match inc {
        $crate::Needed::Unknown =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::Needed::Size(i) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
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

  ($i:expr, $consumed:expr, $field:ident : $e:ident, $assemble:expr) => (
    chaining_parser!($i, $consumed, $field: call!($e), $assemble);
  );

  ($i:expr, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete($crate::Needed::Unknown) =>
        $crate::IResult::Incomplete($crate::Needed::Unknown),
      $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
        let (needed,overflowed) = $consumed.overflowing_add(i);
        match overflowed {
            true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
            false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
        }
      },
      $crate::IResult::Done(i,o)     => {
        let $field = o;
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $consumed:expr, mut $field:ident : $e:ident, $assemble:expr) => (
    chaining_parser!($i, $consumed, mut $field: call!($e), $assemble);
  );

  ($i:expr, $consumed:expr, mut $field:ident : $submac:ident!( $($args:tt)* ), $assemble:expr) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete($crate::Needed::Unknown) =>
        $crate::IResult::Incomplete($crate::Needed::Unknown),
      $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
        let (needed,overflowed) = $consumed.overflowing_add(i);
        match overflowed {
            true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
            false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
        }
      },
      $crate::IResult::Done(i,o)     => {
        let mut $field = o;
        $crate::IResult::Done(i, $assemble())
      }
    }
  );

  ($i:expr, $consumed:expr, $field:ident : $e:ident ? , $assemble:expr) => (
    chaining_parser!($i, $consumed, $field : call!($e) ? , $assemble);
  );

  ($i:expr, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ) ? , $assemble:expr) => ({
    let res = $submac!($i, $($args)*);
    if let $crate::IResult::Incomplete(inc) = res {
      match inc {
        $crate::Needed::Unknown =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::Needed::Size(i) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
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

  ($i:expr, $consumed:expr, mut $field:ident : $e:ident ? , $assemble:expr) => (
    chaining_parser!($i, $consumed, $field : call!($e) ? , $assemble);
  );

  ($i:expr, $consumed:expr, mut $field:ident : $submac:ident!( $($args:tt)* ) ? , $assemble:expr) => ({
    let res = $submac!($i, $($args)*);
    if let $crate::IResult::Incomplete(inc) = res {
      match inc {
        $crate::Needed::Unknown =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::Needed::Size(i) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
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


/// `tuple!(I->IResult<I,A>, I->IResult<I,B>, ... I->IResult<I,X>) => I -> IResult<I, (A, B, ..., X)>`
/// chains parsers and assemble the sub results in a tuple.
///
/// The input type `I` must implement `nom::InputLength`.
///
/// This combinator will count how much data is consumed by every child parser
/// and take it into account if there is not enough data
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Error};
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # use nom::be_u16;
/// // the return type depends of the children parsers
/// named!(parser<&[u8], (u16, &[u8], &[u8]) >,
///   tuple!(
///     be_u16 ,
///     take!(3),
///     tag!("fg")
///   )
/// );
///
/// # fn main() {
/// assert_eq!(
///   parser(&b"abcdefgh"[..]),
///   Done(
///     &b"h"[..],
///     (0x6162u16, &b"cde"[..], &b"fg"[..])
///   )
/// );
/// # }
/// ```
#[macro_export]
macro_rules! tuple (
  ($i:expr, $($rest:tt)*) => (
    {
      tuple_parser!($i, 0usize, (), $($rest)*)
    }
  );
);

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! tuple_parser (
  ($i:expr, $consumed:expr, ($($parsed:tt),*), $e:ident, $($rest:tt)*) => (
    tuple_parser!($i, $consumed, ($($parsed),*), call!($e), $($rest)*);
  );
  ($i:expr, $consumed:expr, (), $submac:ident!( $($args:tt)* ), $($rest:tt)*) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            =>
          $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
        $crate::IResult::Done(i,o)     => {
          tuple_parser!(i,
            $consumed + ($crate::InputLength::input_len(&($i)) -
                         $crate::InputLength::input_len(&i)), (o), $($rest)*)
        }
      }
    }
  );
  ($i:expr, $consumed:expr, ($($parsed:tt)*), $submac:ident!( $($args:tt)* ), $($rest:tt)*) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            =>
          $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
        $crate::IResult::Done(i,o)     => {
          tuple_parser!(i,
            $consumed + ($crate::InputLength::input_len(&($i)) -
                         $crate::InputLength::input_len(&i)), ($($parsed)* , o), $($rest)*)
        }
      }
    }
  );
  ($i:expr, $consumed:expr, ($($parsed:tt),*), $e:ident) => (
    tuple_parser!($i, $consumed, ($($parsed),*), call!($e));
  );
  ($i:expr, $consumed:expr, (), $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            =>
          $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
        $crate::IResult::Done(i,o)     => {
          $crate::IResult::Done(i, (o))
        }
      }
    }
  );
  ($i:expr, $consumed:expr, ($($parsed:expr),*), $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)                            =>
          $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
        $crate::IResult::Done(i,o)     => {
          $crate::IResult::Done(i, ($($parsed),* , o))
        }
      }
    }
  );
  ($i:expr, $consumed:expr, ($($parsed:expr),*)) => (
    {
      $crate::IResult::Done($i, ($($parsed),*))
    }
  );
);

/// `pair!(I -> IResult<I,O>, I -> IResult<I,P>) => I -> IResult<I, (O,P)>`
/// pair(X,Y), returns (x,y)
///
#[macro_export]
macro_rules! pair(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      tuple!($i, $submac!($($args)*), $submac2!($($args2)*))
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    pair!($i, $submac!($($args)*), call!($g));
  );

  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    pair!($i, call!($f), $submac!($($args)*));
  );

  ($i:expr, $f:expr, $g:expr) => (
    pair!($i, call!($f), call!($g));
  );
);

/// `separated_pair!(I -> IResult<I,O>, I -> IResult<I, T>, I -> IResult<I,P>) => I -> IResult<I, (O,P)>`
/// separated_pair(X,sep,Y) returns (x,y)
#[macro_export]
macro_rules! separated_pair(
  ($i:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)+) => (
    {
      match tuple_parser!($i, 0usize, (), $submac!($($args)*), $($rest)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1, (o1, _, o2))   => {
          $crate::IResult::Done(i1, (o1, o2))
        }
      }
    }
  );

  ($i:expr, $f:expr, $($rest:tt)+) => (
    separated_pair!($i, call!($f), $($rest)*);
  );
);

/// `preceded!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, O>`
/// preceded(opening, X) returns X
#[macro_export]
macro_rules! preceded(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match tuple!($i, $submac!($($args)*), $submac2!($($args2)*)) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(remaining, (_,o))    => {
          $crate::IResult::Done(remaining, o)
        }
      }
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    preceded!($i, $submac!($($args)*), call!($g));
  );

  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    preceded!($i, call!($f), $submac!($($args)*));
  );

  ($i:expr, $f:expr, $g:expr) => (
    preceded!($i, call!($f), call!($g));
  );
);

/// `terminated!(I -> IResult<I,O>, I -> IResult<I,T>) => I -> IResult<I, O>`
/// terminated(X, closing) returns X
#[macro_export]
macro_rules! terminated(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match tuple!($i, $submac!($($args)*), $submac2!($($args2)*)) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(remaining, (o,_))    => {
          $crate::IResult::Done(remaining, o)
        }
      }
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    terminated!($i, $submac!($($args)*), call!($g));
  );

  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    terminated!($i, call!($f), $submac!($($args)*));
  );

  ($i:expr, $f:expr, $g:expr) => (
    terminated!($i, call!($f), call!($g));
  );
);

/// `delimited!(I -> IResult<I,T>, I -> IResult<I,O>, I -> IResult<I,U>) => I -> IResult<I, O>`
/// delimited(opening, X, closing) returns X
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done};
/// named!(bracketed,
///     delimited!(
///         tag!("("),
///         take_until!(")"),
///         tag!(")")
///     )
/// );
///
/// # fn main() {
/// let input = &b"(test)"[..];
/// assert_eq!(bracketed(input), Done(&b""[..], &b"test"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! delimited(
  ($i:expr, $submac:ident!( $($args:tt)* ), $($rest:tt)+) => (
    {
      match tuple_parser!($i, 0usize, (), $submac!($($args)*), $($rest)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1, (_, o, _))   => {
          $crate::IResult::Done(i1, o)
        }
      }
    }
  );

  ($i:expr, $f:expr, $($rest:tt)+) => (
    delimited!($i, call!($f), $($rest)*);
  );
);

/// `do_parse!(I->IResult<I,A> >> I->IResult<I,B> >> ... I->IResult<I,X> , ( O ) ) => I -> IResult<I, O>`
/// do_parse applies sub parsers in a sequence.
/// it can store intermediary results and make them available
/// for later parsers
///
/// The input type `I` must implement `nom::InputLength`.
///
/// This combinator will count how much data is consumed by every child parser
/// and take it into account if there is not enough data
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Incomplete};
/// # use nom::Needed;
/// use nom::be_u8;
///
/// // this parser implements a common pattern in binary formats,
/// // the TAG-LENGTH-VALUE, where you first recognize a specific
/// // byte slice, then the next bytes indicate the length of
/// // the data, then you take that slice and return it
/// //
/// // here, we match the tag 42, take the length in the next byte
/// // and store it in `length`, then use `take!` with `length`
/// // to obtain the subslice that we store in `bytes`, then return
/// // `bytes`
/// named!(tag_length_value,
///   do_parse!(
///     tag!( &[ 42u8 ][..] ) >>
///     length: be_u8         >>
///     bytes:  take!(length) >>
///     (bytes)
///   )
/// );
///
/// # fn main() {
/// let a: Vec<u8>        = vec!(42, 2, 3, 4, 5);
/// let result_a: Vec<u8> = vec!(3, 4);
/// let rest_a: Vec<u8>   = vec!(5);
/// assert_eq!(tag_length_value(&a[..]), Done(&rest_a[..], &result_a[..]));
///
/// // here, the length is 5, but there are only 3 bytes afterwards (3, 4 and 5),
/// // so the parser will tell you that you need 7 bytes: one for the tag,
/// // one for the length, then 5 bytes
/// let b: Vec<u8>     = vec!(42, 5, 3, 4, 5);
/// assert_eq!(tag_length_value(&b[..]), Incomplete(Needed::Size(7)));
/// # }
/// ```
///
/// the result is a tuple, so you can return multiple sub results, like
/// this:
/// `do_parse!(I->IResult<I,A> >> I->IResult<I,B> >> ... I->IResult<I,X> , ( O, P ) ) => I -> IResult<I, (O,P)>`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self, Done, Incomplete};
/// # use nom::Needed;
/// use nom::be_u8;
/// named!(tag_length_value<(u8, &[u8])>,
///   do_parse!(
///     tag!( &[ 42u8 ][..] ) >>
///     length: be_u8         >>
///     bytes:  take!(length) >>
///     (length, bytes)
///   )
/// );
///
/// # fn main() {
/// # }
/// ```
///
#[macro_export]
macro_rules! do_parse (
  (__impl $i:expr, $consumed:expr, ( $($rest:expr),* )) => (
    $crate::IResult::Done($i, ( $($rest),* ))
  );

  (__impl $i:expr, $consumed:expr, $e:ident >> $($rest:tt)*) => (
    do_parse!(__impl $i, $consumed, call!($e) >> $($rest)*);
  );
  (__impl $i:expr, $consumed:expr, $submac:ident!( $($args:tt)* ) >> $($rest:tt)*) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
        $crate::IResult::Done(i,_)     => {
          do_parse!(__impl i,
            $consumed + ($crate::InputLength::input_len(&($i)) -
                         $crate::InputLength::input_len(&i)), $($rest)*)
        },
      }
    }
  );

  (__impl $i:expr, $consumed:expr, $field:ident : $e:ident >> $($rest:tt)*) => (
    do_parse!(__impl $i, $consumed, $field: call!($e) >> $($rest)*);
  );

  (__impl $i:expr, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ) >> $($rest:tt)*) => (
    {
      match  $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) =>
          $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
          let (needed,overflowed) = $consumed.overflowing_add(i);
          match overflowed {
              true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
              false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
          }
        },
        $crate::IResult::Done(i,o)     => {
          let $field = o;
          do_parse!(__impl i,
            $consumed + ($crate::InputLength::input_len(&($i)) -
                         $crate::InputLength::input_len(&i)), $($rest)*)
        },
      }
    }
  );

  // ending the chain
  (__impl $i:expr, $consumed:expr, $e:ident >> ( $($rest:tt)* )) => (
    do_parse!(__impl $i, $consumed, call!($e) >> ( $($rest)* ));
  );

  (__impl $i:expr, $consumed:expr, $submac:ident!( $($args:tt)* ) >> ( $($rest:tt)* )) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete($crate::Needed::Unknown) =>
        $crate::IResult::Incomplete($crate::Needed::Unknown),
      $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
        let (needed,overflowed) = $consumed.overflowing_add(i);
        match overflowed {
            true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
            false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
        }
      },
      $crate::IResult::Done(i,_)     => {
        $crate::IResult::Done(i, ( $($rest)* ))
      },
    }
  );

  (__impl $i:expr, $consumed:expr, $field:ident : $e:ident >> ( $($rest:tt)* )) => (
    do_parse!(__impl $i, $consumed, $field: call!($e) >> ( $($rest)* ) );
  );

  (__impl $i:expr, $consumed:expr, $field:ident : $submac:ident!( $($args:tt)* ) >> ( $($rest:tt)* )) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete($crate::Needed::Unknown) =>
        $crate::IResult::Incomplete($crate::Needed::Unknown),
      $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
        let (needed,overflowed) = $consumed.overflowing_add(i);
        match overflowed {
            true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
            false =>  $crate::IResult::Incomplete($crate::Needed::Size(needed)),
        }
      },
      $crate::IResult::Done(i,o)     => {
        let $field = o;
        $crate::IResult::Done(i, ( $($rest)* ))
      },
    }
  );

  ($i:expr, $($rest:tt)*) => (
    {
      do_parse!(__impl $i, 0usize, $($rest)*)
    }
  );
);

#[cfg(test)]
mod tests {
  use internal::{Needed,IResult};
  use internal::IResult::*;
  use util::ErrorKind;
  use nom::be_u16;

  #[cfg(feature = "verbose-errors")]
  use verbose_errors::Err;

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

  #[derive(PartialEq,Eq,Debug)]
  struct B {
    a: u8,
    b: u8
  }

  #[test]
  fn chain2() {
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };

    named!(chain_parser<&[u8],B>,
      chain!(
        tag!("abcd")   ~
        tag!("abcd")?  ~
        aa: ret_int1   ~
        tag!("efgh")   ~
        bb: ret_int2   ~
        tag!("efgh")   ,
        ||{B{a: aa, b: bb}}
      )
    );

    assert_eq!(chain_parser(&b"abcdabcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(chain_parser(&b"abcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(chain_parser(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(chain_parser(&b"abcdefghef"[..]), Incomplete(Needed::Size(12)));
  }

  #[test]
  fn nested_chain() {
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };

    named!(chain_parser<&[u8],B>,
      chain!(
        chain!(
          tag!("abcd")   ~
          tag!("abcd")?  ,
          || {}
        )              ~
        aa: ret_int1   ~
        tag!("efgh")   ~
        bb: ret_int2   ~
        tag!("efgh")   ,
        ||{B{a: aa, b: bb}}
      )
    );

    assert_eq!(chain_parser(&b"abcdabcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(chain_parser(&b"abcdefghefghX"[..]), Done(&b"X"[..], B{a: 1, b: 2}));
    assert_eq!(chain_parser(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(chain_parser(&b"abcdefghef"[..]), Incomplete(Needed::Size(12)));
  }

  #[derive(PartialEq,Eq,Debug)]
  struct C {
    a: u8,
    b: Option<u8>
  }

  #[test]
  fn chain_mut() {
    fn ret_b1_2(i:&[u8]) -> IResult<&[u8], B> { Done(i,B{a:1,b:2}) };
    named!(f<&[u8],B>,
      chain!(
        tag!("abcd")     ~
        tag!("abcd")?    ~
        tag!("efgh")     ~
        mut bb: ret_b1_2 ~
        tag!("efgh")   ,
        ||{
          bb.b = 3;
          bb
        }
      )
    );

    let r = f(&b"abcdabcdefghefghX"[..]);
    assert_eq!(r, Done(&b"X"[..], B{a: 1, b: 3}));
  }

  #[test]
  fn chain_opt() {
    named!(y, tag!("efgh"));
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    named!(ret_y<&[u8], u8>, map!(y, |_| 2));

    named!(chain_parser<&[u8],C>,
      chain!(
        tag!("abcd") ~
        aa: ret_int1 ~
        bb: ret_y?   ,
        ||{C{a: aa, b: bb}}
      )
    );

    assert_eq!(chain_parser(&b"abcdefghX"[..]), Done(&b"X"[..], C{a: 1, b: Some(2)}));
    assert_eq!(chain_parser(&b"abcdWXYZ"[..]), Done(&b"WXYZ"[..], C{a: 1, b: None}));
    assert_eq!(chain_parser(&b"abcdX"[..]), Done(&b"X"[..], C{ a: 1, b: None }));
    assert_eq!(chain_parser(&b"abcdef"[..]), Incomplete(Needed::Size(8)));
  }

  #[cfg(feature = "verbose-errors")]
  use util::{error_to_list, add_error_pattern, print_error};

  #[cfg(feature = "verbose-errors")]
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

  // do it this way if you can use box patterns
  /*use std::str;
  fn error_to_string(e:Err) -> String
    match e {
      NodePosition(ErrorKind::Custom(42), i1, box Position(ErrorKind::Tag, i2)) => {
        format!("missing `ijkl` tag, found '{}' instead", str::from_utf8(i2).unwrap())
      },
      NodePosition(ErrorKind::Custom(42), i1, box NodePosition(ErrorKind::Custom(128), i2,  box Position(ErrorKind::Tag, i3))) => {
        format!("missing `mnop` tag after `ijkl`, found '{}' instead", str::from_utf8(i3).unwrap())
      },
      _ => "unrecognized error".to_string()
    }
  }*/

  #[cfg(feature = "verbose-errors")]
  use std::collections;

  #[cfg(feature = "verbose-errors")]
  #[test]
  fn err() {
    named!(err_test, alt!(
      tag!("abcd") |
      preceded!(tag!("efgh"), return_error!(ErrorKind::Custom(42),
          do_parse!(
                 tag!("ijkl")                                        >>
            res: return_error!(ErrorKind::Custom(128), tag!("mnop")) >>
            (res)
          )
        )
      )
    ));
    let a = &b"efghblah"[..];
    let b = &b"efghijklblah"[..];
    let c = &b"efghijklmnop"[..];

    let blah = &b"blah"[..];

    let res_a = err_test(a);
    let res_b = err_test(b);
    let res_c = err_test(c);
    assert_eq!(res_a, Error(error_node_position!(ErrorKind::Custom(42), blah, error_position!(ErrorKind::Tag, blah))));
    assert_eq!(res_b, Error(error_node_position!(ErrorKind::Custom(42), &b"ijklblah"[..], error_node_position!(ErrorKind::Custom(128), blah, error_position!(ErrorKind::Tag, blah)))));
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

  #[allow(unused_variables)]
  #[test]
  fn add_err() {
    named!(err_test,
      preceded!(tag!("efgh"), add_return_error!(ErrorKind::Custom(42),
          do_parse!(
                 tag!("ijkl")                                     >>
            res: add_return_error!(ErrorKind::Custom(128), tag!("mnop")) >>
            (res)
          )
        )
    ));
    let a = &b"efghblah"[..];
    let b = &b"efghijklblah"[..];
    let c = &b"efghijklmnop"[..];

    let blah = &b"blah"[..];

    let res_a = err_test(a);
    let res_b = err_test(b);
    let res_c = err_test(c);
    assert_eq!(res_a, Error(error_node_position!(ErrorKind::Custom(42), blah, error_position!(ErrorKind::Tag, blah))));
    assert_eq!(res_b, Error(error_node_position!(ErrorKind::Custom(42), &b"ijklblah"[..], error_node_position!(ErrorKind::Custom(128), blah, error_position!(ErrorKind::Tag, blah)))));
    assert_eq!(res_c, Done(&b""[..], &b"mnop"[..]));
  }

  #[test]
  fn complete() {
    named!(err_test,
      do_parse!(
             tag!("ijkl")            >>
        res: complete!(tag!("mnop")) >>
        (res)
      )
    );
    let a = &b"ijklmn"[..];

    let res_a = err_test(a);
    assert_eq!(res_a, Error(error_position!(ErrorKind::Complete, &b"mn"[..])));
  }

  #[test]
  fn pair() {
    named!( tag_abc, tag!("abc") );
    named!( tag_def, tag!("def") );
    named!( pair_abc_def<&[u8],(&[u8], &[u8])>, pair!(tag_abc, tag_def) );

    assert_eq!(pair_abc_def(&b"abcdefghijkl"[..]), Done(&b"ghijkl"[..], (&b"abc"[..], &b"def"[..])));
    assert_eq!(pair_abc_def(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(pair_abc_def(&b"abcd"[..]), Incomplete(Needed::Size(6)));
    assert_eq!(pair_abc_def(&b"xxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(pair_abc_def(&b"xxxdef"[..]), Error(error_position!(ErrorKind::Tag, &b"xxxdef"[..])));
    assert_eq!(pair_abc_def(&b"abcxxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn separated_pair() {
    named!( tag_abc, tag!("abc") );
    named!( tag_def, tag!("def") );
    named!( tag_separator, tag!(",") );
    named!( sep_pair_abc_def<&[u8],(&[u8], &[u8])>, separated_pair!(tag_abc, tag_separator, tag_def) );

    assert_eq!(sep_pair_abc_def(&b"abc,defghijkl"[..]), Done(&b"ghijkl"[..], (&b"abc"[..], &b"def"[..])));
    assert_eq!(sep_pair_abc_def(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(sep_pair_abc_def(&b"abc,d"[..]), Incomplete(Needed::Size(7)));
    assert_eq!(sep_pair_abc_def(&b"xxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(sep_pair_abc_def(&b"xxx,def"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx,def"[..])));
    assert_eq!(sep_pair_abc_def(&b"abc,xxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn preceded() {
    named!( tag_abcd, tag!("abcd") );
    named!( tag_efgh, tag!("efgh") );
    named!( preceded_abcd_efgh<&[u8], &[u8]>, preceded!(tag_abcd, tag_efgh) );

    assert_eq!(preceded_abcd_efgh(&b"abcdefghijkl"[..]), Done(&b"ijkl"[..], &b"efgh"[..]));
    assert_eq!(preceded_abcd_efgh(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(preceded_abcd_efgh(&b"abcde"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(preceded_abcd_efgh(&b"xxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(preceded_abcd_efgh(&b"xxxxdef"[..]), Error(error_position!(ErrorKind::Tag, &b"xxxxdef"[..])));
    assert_eq!(preceded_abcd_efgh(&b"abcdxxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx"[..])));
  }

  #[test]
  fn terminated() {
    named!( tag_abcd, tag!("abcd") );
    named!( tag_efgh, tag!("efgh") );
    named!( terminated_abcd_efgh<&[u8], &[u8]>, terminated!(tag_abcd, tag_efgh) );

    assert_eq!(terminated_abcd_efgh(&b"abcdefghijkl"[..]), Done(&b"ijkl"[..], &b"abcd"[..]));
    assert_eq!(terminated_abcd_efgh(&b"ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(terminated_abcd_efgh(&b"abcde"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(terminated_abcd_efgh(&b"xxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(terminated_abcd_efgh(&b"xxxxdef"[..]), Error(error_position!(ErrorKind::Tag, &b"xxxxdef"[..])));
    assert_eq!(terminated_abcd_efgh(&b"abcdxxxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxxx"[..])));
  }

  #[test]
  fn delimited() {
    named!( tag_abc, tag!("abc") );
    named!( tag_def, tag!("def") );
    named!( tag_ghi, tag!("ghi") );
    named!( delimited_abc_def_ghi<&[u8], &[u8]>, delimited!(tag_abc, tag_def, tag_ghi) );

    assert_eq!(delimited_abc_def_ghi(&b"abcdefghijkl"[..]), Done(&b"jkl"[..], &b"def"[..]));
    assert_eq!(delimited_abc_def_ghi(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(delimited_abc_def_ghi(&b"abcde"[..]), Incomplete(Needed::Size(6)));
    assert_eq!(delimited_abc_def_ghi(&b"abcdefgh"[..]), Incomplete(Needed::Size(9)));
    assert_eq!(delimited_abc_def_ghi(&b"xxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx"[..])));
    assert_eq!(delimited_abc_def_ghi(&b"xxxdefghi"[..]), Error(error_position!(ErrorKind::Tag, &b"xxxdefghi"[..])));
    assert_eq!(delimited_abc_def_ghi(&b"abcxxxghi"[..]), Error(error_position!(ErrorKind::Tag, &b"xxxghi"[..])));
    assert_eq!(delimited_abc_def_ghi(&b"abcdefxxx"[..]), Error(error_position!(ErrorKind::Tag, &b"xxx"[..])));
  }

    #[test]
  fn chain_incomplete() {
    let res = chain!(&b"abcdefgh"[..],
      a: take!(4) ~
      b: take!(8),
      ||{(a,b )}
    );

    assert_eq!(res, IResult::Incomplete(Needed::Size(12)));
  }

  #[test]
  fn tuple_test() {
    named!(tuple_3<&[u8], (u16, &[u8], &[u8]) >,
    tuple!( be_u16 , take!(3), tag!("fg") ) );

    assert_eq!(tuple_3(&b"abcdefgh"[..]), Done(&b"h"[..], (0x6162u16, &b"cde"[..], &b"fg"[..])));
    assert_eq!(tuple_3(&b"abcd"[..]), Incomplete(Needed::Size(5)));
    assert_eq!(tuple_3(&b"abcde"[..]), Incomplete(Needed::Size(7)));
    assert_eq!(tuple_3(&b"abcdejk"[..]), Error(error_position!(ErrorKind::Tag, &b"jk"[..])));
  }

  #[test]
  fn do_parse() {
    fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
    fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };

    //trace_macros!(true);
    named!(do_parser<&[u8], (u8, u8)>,
      do_parse!(
        tag!("abcd")       >>
        opt!(tag!("abcd")) >>
        aa: ret_int1       >>
        tag!("efgh")       >>
        bb: ret_int2       >>
        tag!("efgh")       >>
        (aa, bb)
      )
    );
    //named!(do_parser<&[u8], (u8, u8)>,
    //  do_parse!(
    //    tag!("abcd") >> aa: ret_int1 >> tag!("efgh") >> bb: ret_int2 >> tag!("efgh") >> (aa, bb)
    //  )
    //);

    //trace_macros!(false);

    assert_eq!(do_parser(&b"abcdabcdefghefghX"[..]), Done(&b"X"[..], (1, 2)));
    assert_eq!(do_parser(&b"abcdefghefghX"[..]), Done(&b"X"[..], (1, 2)));
    assert_eq!(do_parser(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(do_parser(&b"abcdefghef"[..]), Incomplete(Needed::Size(12)));
  }

  #[test]
  fn do_parse_dependency() {
    use nom::be_u8;

    named!(length_value,
      do_parse!(
        length: be_u8         >>
        bytes:  take!(length) >>
        (bytes)
      )
    );

    let a: Vec<u8>     = vec!(2, 3, 4, 5);
    let res_a: Vec<u8> = vec!(3, 4);
    assert_eq!(length_value(&a[..]), Done(&a[3..], &res_a[..]));
    let b: Vec<u8>     = vec!(5, 3, 4, 5);
    assert_eq!(length_value(&b[..]), Incomplete(Needed::Size(6)));
  }
}
