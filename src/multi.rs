//! Parsers for applying parsers multiple times

/// `separated_list!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// separated_list(sep, X) returns Vec<X> will return Incomplete if there may be more elements
#[macro_export]
macro_rules! separated_list(
  ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => (
    {
      use $crate::InputLength;

      //FIXME: use crate vec
      let mut res   = ::std::vec::Vec::new();
      let mut input = $i.clone();

      // get the first element
      let input_ = input.clone();
      match $submac!(input_, $($args2)*) {
        $crate::IResult::Error(_)      => $crate::IResult::Done(input, ::std::vec::Vec::new()),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i,o)     => {
          if i.input_len() == input.input_len() {
            $crate::IResult::Error(error_position!($crate::ErrorKind::SeparatedList,input))
          } else {
            res.push(o);
            input = i;

            let ret;

            loop {
              // get the separator first
              let input_ = input.clone();
              match $sep!(input_, $($args)*) {
                $crate::IResult::Error(_) => {
                  ret = $crate::IResult::Done(input, res);
                  break;
                }
                $crate::IResult::Incomplete($crate::Needed::Unknown) => {
                  ret = $crate::IResult::Incomplete($crate::Needed::Unknown);
                  break;
                },
                $crate::IResult::Incomplete($crate::Needed::Size(needed)) => {
                  let (size,overflowed) = needed.overflowing_add(($i).input_len() - input.input_len());
                  ret = match overflowed {
                    true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                    false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
                  };
                  break;
                },
                $crate::IResult::Done(i2,_)     => {
                  let i2_len = i2.input_len();
                  if i2_len == input.input_len() {
                    ret = $crate::IResult::Done(input, res);
                    break;
                  }

                  // get the element next
                  match $submac!(i2, $($args2)*) {
                    $crate::IResult::Error(_) => {
                      ret = $crate::IResult::Done(input, res);
                      break;
                    },
                    $crate::IResult::Incomplete($crate::Needed::Unknown) => {
                      ret = $crate::IResult::Incomplete($crate::Needed::Unknown);
                      break;
                    },
                    $crate::IResult::Incomplete($crate::Needed::Size(needed)) => {
                      let (size,overflowed) = needed.overflowing_add(($i).input_len() - i2_len);
                      ret = match overflowed {
                        true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                        false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
                      };
                      break;
                    },
                    $crate::IResult::Done(i3,o3)    => {
                      if i3.input_len() == i2_len {
                        ret = $crate::IResult::Done(input, res);
                        break;
                      }
                      res.push(o3);
                      input = i3;
                    }
                  }
                }
              }
            }

            ret
          }
        },
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    separated_list!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    separated_list!($i, call!($f), $submac!($($args)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    separated_list!($i, call!($f), call!($g));
  );
);

/// `separated_nonempty_list!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// separated_nonempty_list(sep, X) returns Vec<X> will return Incomplete if there may be more elements
#[macro_export]
macro_rules! separated_nonempty_list(
  ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => (
    {
      use $crate::InputLength;

      let mut res   = ::std::vec::Vec::new();
      let mut input = $i.clone();

      // get the first element
      let input_ = input.clone();
      match $submac!(input_, $($args2)*) {
        $crate::IResult::Error(a)      => $crate::IResult::Error(a),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i,o)     => {
          if i.input_len() == input.len() {
            $crate::IResult::Error(error_position!($crate::ErrorKind::SeparatedNonEmptyList,input))
          } else {
            res.push(o);
            input = i;

            let ret;

            loop {
              // get the separator first
              let input_ = input.clone();
              match $sep!(input_, $($args)*) {
                $crate::IResult::Error(_) => {
                  ret = $crate::IResult::Done(input, res);
                  break;
                }
                $crate::IResult::Incomplete($crate::Needed::Unknown) => {
                  ret = $crate::IResult::Incomplete($crate::Needed::Unknown);
                  break;
                },
                $crate::IResult::Incomplete($crate::Needed::Size(needed)) => {
                  let (size,overflowed) = needed.overflowing_add(($i).input_len() - input.input_len());
                  ret = match overflowed {
                    true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                    false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
                  };
                  break;
                },
                $crate::IResult::Done(i2,_)     => {
                  let i2_len = i2.input_len();
                  if i2_len == input.input_len() {
                    ret = $crate::IResult::Done(input, res);
                    break;
                  }

                  // get the element next
                  match $submac!(i2, $($args2)*) {
                    $crate::IResult::Error(_) => {
                      ret = $crate::IResult::Done(input, res);
                      break;
                    },
                    $crate::IResult::Incomplete($crate::Needed::Unknown) => {
                      ret = $crate::IResult::Incomplete($crate::Needed::Unknown);
                      break;
                    },
                    $crate::IResult::Incomplete($crate::Needed::Size(needed)) => {
                      let (size,overflowed) = needed.overflowing_add(($i).input_len() - i2_len);
                      ret = match overflowed {
                        true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                        false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
                      };
                      break;
                    },
                    $crate::IResult::Done(i3,o3)    => {
                      if i3.input_len() == i2_len {
                        ret = $crate::IResult::Done(input, res);
                        break;
                      }
                      res.push(o3);
                      input = i3;
                    }
                  }
                }
              }
            }

            ret
          }
        },
      }
    }
  );
  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    separated_nonempty_list!($i, $submac!($($args)*), call!($g));
  );
  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    separated_nonempty_list!($i, call!($f), $submac!($($args)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    separated_nonempty_list!($i, call!($f), call!($g));
  );
);

/// `separated_list_complete!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// This is equivalent to the `separated_list!` combinator, except that it will return `Error`
/// when either the separator or element subparser returns `Incomplete`.
#[macro_export]
macro_rules! separated_list_complete {
    ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => ({
        separated_list!($i, complete!($sep!($($args)*)), complete!($submac!($($args2)*)))
    });

    ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
        separated_list_complete!($i, $submac!($($args)*), call!($g));
    );
    ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
        separated_list_complete!($i, call!($f), $submac!($($args)*));
    );
    ($i:expr, $f:expr, $g:expr) => (
        separated_list_complete!($i, call!($f), call!($g));
    );
}

/// `separated_nonempty_list_complete!(I -> IResult<I,T>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// This is equivalent to the `separated_nonempty_list!` combinator, except that it will return
/// `Error` when either the separator or element subparser returns `Incomplete`.
#[macro_export]
macro_rules! separated_nonempty_list_complete {
    ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => ({
        separated_nonempty_list!($i, complete!($sep!($($args)*)), complete!($submac!($($args2)*)))
    });

    ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
        separated_nonempty_list_complete!($i, $submac!($($args)*), call!($g));
    );
    ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
        separated_nonempty_list_complete!($i, call!($f), $submac!($($args)*));
    );
    ($i:expr, $f:expr, $g:expr) => (
        separated_nonempty_list_complete!($i, call!($f), call!($g));
    );
}

/// `many0!(I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// Applies the parser 0 or more times and returns the list of results in a Vec
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >, many0!( tag!( "abcd" ) ) );
///
///  let a = b"abcdabcdefgh";
///  let b = b"azerty";
///
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&a[..]), Done(&b"efgh"[..], res));
///  assert_eq!(multi(&b[..]), Done(&b"azerty"[..], Vec::new()));
/// # }
/// ```
/// 0 or more
#[macro_export]
macro_rules! many0(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::InputLength;

      let ret;
      let mut res   = ::std::vec::Vec::new();
      let mut input = $i.clone();

      loop {
        if input.input_len() == 0 {
          ret = $crate::IResult::Done(input, res);
          break;
        }

        let input_ = input.clone();
        match $submac!(input_, $($args)*) {
          $crate::IResult::Error(_)                            => {
            ret = $crate::IResult::Done(input, res);
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown) => {
            ret = $crate::IResult::Incomplete($crate::Needed::Unknown);
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
            let (size,overflowed) = i.overflowing_add(($i).input_len() - input.input_len());
            ret = match overflowed {
                true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
            };
            break;
          },
          $crate::IResult::Done(i, o)                          => {
            // loop trip must always consume (otherwise infinite loops)
            if i == input {
              ret = $crate::IResult::Error(error_position!($crate::ErrorKind::Many0,input));
              break;
            }

            res.push(o);
            input = i;
          }
        }
      }

      ret
    }
  );
  ($i:expr, $f:expr) => (
    many0!($i, call!($f));
  );
);

/// `many1!(I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// Applies the parser 1 or more times and returns the list of results in a Vec
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >, many1!( tag!( "abcd" ) ) );
///
///  let a = b"abcdabcdefgh";
///  let b = b"azerty";
///
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&a[..]), Done(&b"efgh"[..], res));
///  assert_eq!(multi(&b[..]), Error(error_position!(ErrorKind::Many1,&b[..])));
/// # }
/// ```
#[macro_export]
macro_rules! many1(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::InputLength;
      let i_ = $i.clone();
      match $submac!(i_, $($args)*) {
        $crate::IResult::Error(_)      => $crate::IResult::Error(
          error_position!($crate::ErrorKind::Many1,$i)
        ),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,o1)   => {
          if i1.input_len() == 0 {
            let mut res = ::std::vec::Vec::new();
            res.push(o1);
            $crate::IResult::Done(i1,res)
          } else {

            let mut res    = ::std::vec::Vec::with_capacity(4);
            res.push(o1);
            let mut input  = i1;
            let mut incomplete: ::std::option::Option<$crate::Needed> =
              ::std::option::Option::None;
            loop {
              if input.input_len() == 0 {
                break;
              }
              let input_ = input.clone();
              match $submac!(input_, $($args)*) {
                $crate::IResult::Error(_)                    => {
                  break;
                },
                $crate::IResult::Incomplete($crate::Needed::Unknown) => {
                  incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
                  break;
                },
                $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
                  let (size,overflowed) = i.overflowing_add(($i).input_len() - input.input_len());
                  incomplete = ::std::option::Option::Some(
                    match overflowed {
                        true  => $crate::Needed::Unknown,
                        false => $crate::Needed::Size(size),
                    }
                  );
                  break;
                },
                $crate::IResult::Done(i, o) => {
                  if i.input_len() == input.input_len() {
                    break;
                  }
                  res.push(o);
                  input = i;
                }
              }
            }

            match incomplete {
              ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
              ::std::option::Option::None    => $crate::IResult::Done(input, res)
            }
          }
        }
      }
    }
  );
  ($i:expr, $f:expr) => (
    many1!($i, call!($f));
  );
);

/// `many_till!(I -> IResult<I,O>, I -> IResult<I,P>) => I -> IResult<I, (Vec<O>, P)>`
/// Applies the first parser until the second applies. Returns a tuple containing the list
/// of results from the first in a Vec and the result of the second.
///
/// The first embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///    named!(multi<&[u8], (Vec<&[u8]>, &[u8]) >, many_till!( tag!( "abcd" ), tag!( "efgh" ) ) );
///
///    let a = b"abcdabcdefghabcd";
///    let b = b"efghabcd";
///    let c = b"azerty";
///
///    let res_a = (vec![&b"abcd"[..], &b"abcd"[..]], &b"efgh"[..]);
///    let res_b: (Vec<&[u8]>, &[u8]) = (Vec::new(), &b"efgh"[..]);
///    assert_eq!(multi(&a[..]), Done(&b"abcd"[..], res_a));
///    assert_eq!(multi(&b[..]), Done(&b"abcd"[..], res_b));
///    assert_eq!(multi(&c[..]), Error(error_node_position!(ErrorKind::ManyTill,&c[..],error_position!(ErrorKind::Tag,&c[..]))));
/// # }
/// ```
#[macro_export]
macro_rules! many_till(
  ($i:expr, $submac1:ident!( $($args1:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      use $crate::InputLength;

      let ret;
      let mut res   = ::std::vec::Vec::new();
      let mut input = $i.clone();

      loop {
        match $submac2!(input, $($args2)*) {
          $crate::IResult::Done(i, o) => {
            ret = $crate::IResult::Done(i, (res, o));
            break;
          },
          _                           => {
            match $submac1!(input, $($args1)*) {
              $crate::IResult::Error(err)                            => {
                ret = $crate::IResult::Error(error_node_position!($crate::ErrorKind::ManyTill,input, err));
                break;
              },
              $crate::IResult::Incomplete($crate::Needed::Unknown) => {
                ret = $crate::IResult::Incomplete($crate::Needed::Unknown);
                break;
              },
              $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
                let (size,overflowed) = i.overflowing_add(($i).input_len() - input.input_len());
                ret = match overflowed {
                    true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                    false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
                };
                break;
              },
              $crate::IResult::Done(i, o)                          => {
                // loop trip must always consume (otherwise infinite loops)
                if i == input {
                  ret = $crate::IResult::Error(error_position!($crate::ErrorKind::ManyTill,input));
                  break;
                }

                res.push(o);
                input = i;
              },
            }
          },
        }
      }

      ret
    }
  );
  ($i:expr, $f:expr, $g: expr) => (
    many_till!($i, call!($f), call!($g));
  );
);

/// `many_m_n!(usize, usize, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// Applies the parser between m and n times (n included) and returns the list of
/// results in a Vec
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >, many_m_n!(2, 4, tag!( "abcd" ) ) );
///
///  let a = b"abcdefgh";
///  let b = b"abcdabcdefgh";
///  let c = b"abcdabcdabcdabcdabcdefgh";
///
///  assert_eq!(multi(&a[..]),Error(error_position!(ErrorKind::ManyMN,&a[..])));
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&b[..]), Done(&b"efgh"[..], res));
///  let res2 = vec![&b"abcd"[..], &b"abcd"[..], &b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&c[..]), Done(&b"abcdefgh"[..], res2));
/// # }
/// ```
#[macro_export]
macro_rules! many_m_n(
  ($i:expr, $m:expr, $n: expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::InputLength;
      let mut res          = ::std::vec::Vec::with_capacity($m);
      let mut input        = $i.clone();
      let mut count: usize = 0;
      let mut err          = false;
      let mut incomplete: ::std::option::Option<$crate::Needed> = ::std::option::Option::None;
      loop {
        if count == $n { break }
        let i_ = input.clone();
        match $submac!(i_, $($args)*) {
          $crate::IResult::Done(i, o) => {
            // do not allow parsers that do not consume input (causes infinite loops)
            if i.input_len() == input.input_len() {
              break;
            }
            res.push(o);
            input  = i;
            count += 1;
          }
          $crate::IResult::Error(_)                    => {
            err = true;
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown) => {
            incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
            let (size,overflowed) = i.overflowing_add($i.input_len() - input.input_len());
            incomplete = ::std::option::Option::Some(
              match overflowed {
                  true  => $crate::Needed::Unknown,
                  false => $crate::Needed::Size(size),
              }
            );
            break;
          },
        }
        if input.input_len() == 0 {
          break;
        }
      }

      if count < $m {
        if err {
          $crate::IResult::Error(error_position!($crate::ErrorKind::ManyMN,$i))
        } else {
          match incomplete {
            ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
            ::std::option::Option::None    => $crate::IResult::Incomplete(
              $crate::Needed::Unknown
            )
          }
        }
      } else {
        match incomplete {
          ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
          ::std::option::Option::None    => $crate::IResult::Done(input, res)
        }
      }
    }
  );
  ($i:expr, $m:expr, $n: expr, $f:expr) => (
    many_m_n!($i, $m, $n, call!($f));
  );
);

/// `count!(I -> IResult<I,O>, nb) => I -> IResult<I, Vec<O>>`
/// Applies the child parser a specified number of times
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done,Error};
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(counter< Vec<&[u8]> >, count!( tag!( "abcd" ), 2 ) );
///
///  let a = b"abcdabcdabcdef";
///  let b = b"abcdefgh";
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///
///  assert_eq!(counter(&a[..]), Done(&b"abcdef"[..], res));
///  assert_eq!(counter(&b[..]), Error(error_position!(ErrorKind::Count, &b[..])));
/// # }
/// ```
///
#[macro_export]
macro_rules! count(
  ($i:expr, $submac:ident!( $($args:tt)* ), $count: expr) => (
    {
      let ret: $crate::IResult<_,_>;
      let mut input = $i.clone();
      let mut res   = ::std::vec::Vec::new();

      loop {
        if res.len() == $count {
          ret = $crate::IResult::Done(input, res);
          break;
        }

        let input_ = input.clone();
        match $submac!(input_, $($args)*) {
          $crate::IResult::Done(i,o) => {
            res.push(o);
            input = i;
          },
          $crate::IResult::Error(_)  => {
            ret = $crate::IResult::Error(error_position!($crate::ErrorKind::Count,$i));
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown) => {
            ret = $crate::IResult::Incomplete($crate::Needed::Unknown);
            break;
          }
          $crate::IResult::Incomplete($crate::Needed::Size(sz)) => {
            let (size,overflowed) = sz.overflowing_add(
              $crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&input)
            );
            ret = match overflowed {
                true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
            };
            break;
          }
        }
      }

      ret
    }
  );
  ($i:expr, $f:expr, $count: expr) => (
    count!($i, call!($f), $count);
  );
);

/// `count_fixed!(O, I -> IResult<I,O>, nb) => I -> IResult<I, [O; nb]>`
/// Applies the child parser a fixed number of times and returns a fixed size array
/// The type must be specified and it must be `Copy`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done,Error};
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(counter< [&[u8]; 2] >, count_fixed!( &[u8], tag!( "abcd" ), 2 ) );
///  // can omit the type specifier if returning slices
///  // named!(counter< [&[u8]; 2] >, count_fixed!( tag!( "abcd" ), 2 ) );
///
///  let a = b"abcdabcdabcdef";
///  let b = b"abcdefgh";
///  let res = [&b"abcd"[..], &b"abcd"[..]];
///
///  assert_eq!(counter(&a[..]), Done(&b"abcdef"[..], res));
///  assert_eq!(counter(&b[..]), Error(error_position!(ErrorKind::Count, &b[..])));
/// # }
/// ```
///
#[macro_export]
macro_rules! count_fixed (
  ($i:expr, $typ:ty, $submac:ident!( $($args:tt)* ), $count: expr) => (
    {
      let ret;
      let mut input = $i.clone();
      // `$typ` must be Copy, and thus having no destructor, this is panic safe
      let mut res: [$typ; $count] = unsafe{[::std::mem::uninitialized(); $count as usize]};
      let mut cnt: usize = 0;

      loop {
        if cnt == $count {
          ret = $crate::IResult::Done(input, res); break;
        }

        match $submac!(input, $($args)*) {
          $crate::IResult::Done(i,o) => {
            res[cnt] = o;
            cnt += 1;
            input = i;
          },
          $crate::IResult::Error(_)  => {
            ret = $crate::IResult::Error(error_position!($crate::ErrorKind::Count,$i));
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown) => {
            ret = $crate::IResult::Incomplete($crate::Needed::Unknown);
            break;
          }
          $crate::IResult::Incomplete($crate::Needed::Size(sz)) => {
            let (size,overflowed) = sz.overflowing_add(
              $crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&input)
            );
            ret = match overflowed {
                true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
            };
            break;
          }
        }
      }

      ret
    }
);
  ($i:expr, $typ: ty, $f:ident, $count: expr) => (
    count_fixed!($i, $typ, call!($f), $count);
  );
);

/// `length_count!(I -> IResult<I, nb>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// gets a number from the first parser, then applies the second parser that many times
#[macro_export]
macro_rules! length_count(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i, o)    => {
          match count!(i, $submac2!($($args2)*), o as usize) {
            $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
            $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
            $crate::IResult::Incomplete($crate::Needed::Size(n)) => {
              let (size,overflowed) = n.overflowing_add(
                $crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i)
              );
              match overflowed {
                  true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                  false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
              }
            },
            $crate::IResult::Done(i2, o2)  =>  $crate::IResult::Done(i2, o2)
          }
        }
      }
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    length_count!($i, $submac!($($args)*), call!($g));
  );

  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    length_count!($i, call!($f), $submac!($($args)*));
  );

  ($i:expr, $f:expr, $g:expr) => (
    length_count!($i, call!($f), call!($g));
  );
);

/// `length_data!(I -> IResult<I, nb>) => O`
///
/// `length_data` gets a number from the first parser, than takes a subslice of the input
/// of that size, and returns that subslice
#[macro_export]
macro_rules! length_data(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    match $submac!($i, $($args)*) {
      $crate::IResult::Error(e)      => $crate::IResult::Error(e),
      $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
      $crate::IResult::Done(i, o)    => {
        match take!(i, o as usize) {
          $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
          $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
          $crate::IResult::Incomplete($crate::Needed::Size(n)) => {
            let (size,overflowed) = n.overflowing_add(
              $crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i)
            );
            match overflowed {
                true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
            }
          },
          $crate::IResult::Done(i2, o2)  =>  $crate::IResult::Done(i2, o2)
        }
      }
    }
  );

  ($i:expr, $f:expr) => (
    length_data!($i, call!($f));
  );
);

/// `length_value!(I -> IResult<I, nb>, I -> IResult<I,O>) => I -> IResult<I, Vec<O>>`
/// gets a number from the first parser, takes a subslice of the input of that size,
/// then applies the second parser on that subslice. If the second parser returns
/// `Incomplete`, `length_value` will return an error
#[macro_export]
macro_rules! length_value(
  ($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(e)      => $crate::IResult::Error(e),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i, o)    => {
          match take!(i, o as usize) {
            $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
            $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
            $crate::IResult::Incomplete($crate::Needed::Size(n)) => {
              let (size,overflowed) = n.overflowing_add(
                $crate::InputLength::input_len(&($i)) - $crate::InputLength::input_len(&i)
              );
              match overflowed {
                  true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                  false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
              }
            },
            $crate::IResult::Done(i2, o2)  => {
              match complete!(o2, $submac2!($($args2)*)) {
                $crate::IResult::Error(e)      => $crate::IResult::Error(e),
                $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
                $crate::IResult::Done(_, o3)   => $crate::IResult::Done(i2, o3)
              }
            }
          }
        }
      }
    }
  );

  ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
    length_value!($i, $submac!($($args)*), call!($g));
  );

  ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
    length_value!($i, call!($f), $submac!($($args)*));
  );

  ($i:expr, $f:expr, $g:expr) => (
    length_value!($i, call!($f), call!($g));
  );
);

/// `fold_many0!(I -> IResult<I,O>, R, Fn(R, O) -> R) => I -> IResult<I, R>`
/// Applies the parser 0 or more times and folds the list of return values
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >,
///    fold_many0!( tag!( "abcd" ), Vec::new(), |mut acc: Vec<_>, item| {
///      acc.push(item);
///      acc
///  }));
///
///  let a = b"abcdabcdefgh";
///  let b = b"azerty";
///
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&a[..]), Done(&b"efgh"[..], res));
///  assert_eq!(multi(&b[..]), Done(&b"azerty"[..], Vec::new()));
/// # }
/// ```
/// 0 or more
#[macro_export]
macro_rules! fold_many0(
  ($i:expr, $submac:ident!( $($args:tt)* ), $init:expr, $f:expr) => (
    {
      use $crate::InputLength;
      let ret;
      let f         = $f;
      let mut res   = $init;
      let mut input = $i.clone();

      loop {
        if input.input_len() == 0 {
          ret = $crate::IResult::Done(input, res);
          break;
        }

        match $submac!(input, $($args)*) {
          $crate::IResult::Error(_)                            => {
            ret = $crate::IResult::Done(input, res);
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown) => {
            ret = $crate::IResult::Incomplete($crate::Needed::Unknown);
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
            let (size,overflowed) = i.overflowing_add( ($i).input_len() - input.input_len() );
            ret = match overflowed {
                true  => $crate::IResult::Incomplete($crate::Needed::Unknown),
                false => $crate::IResult::Incomplete($crate::Needed::Size(size)),
            };
            break;
          },
          $crate::IResult::Done(i, o)                          => {
            // loop trip must always consume (otherwise infinite loops)
            if i == input {
              ret = $crate::IResult::Error(
                error_position!($crate::ErrorKind::Many0,input)
              );
              break;
            }

            res = f(res, o);
            input = i;
          }
        }
      }

      ret
    }
  );
  ($i:expr, $f:expr, $init:expr, $fold_f:expr) => (
    fold_many0!($i, call!($f), $init, $fold_f);
  );
);

/// `fold_many1!(I -> IResult<I,O>, R, Fn(R, O) -> R) => I -> IResult<I, R>`
/// Applies the parser 1 or more times and folds the list of return values
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >,
///    fold_many1!( tag!( "abcd" ), Vec::new(), |mut acc: Vec<_>, item| {
///      acc.push(item);
///      acc
///  }));
///
///  let a = b"abcdabcdefgh";
///  let b = b"azerty";
///
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&a[..]), Done(&b"efgh"[..], res));
///  assert_eq!(multi(&b[..]), Error(error_position!(ErrorKind::Many1,&b[..])));
/// # }
/// ```
#[macro_export]
macro_rules! fold_many1(
  ($i:expr, $submac:ident!( $($args:tt)* ), $init:expr, $f:expr) => (
    {
      use $crate::InputLength;
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(_)      => $crate::IResult::Error(
          error_position!($crate::ErrorKind::Many1,$i)
        ),
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i1,o1)   => {
          let acc = $init;
          let f = $f;
          if i1.input_len() == 0 {
            let acc = f(acc, o1);
            $crate::IResult::Done(i1,acc)
          } else {
            let mut acc = f(acc, o1);
            let mut input  = i1;
            let mut incomplete: ::std::option::Option<$crate::Needed> =
              ::std::option::Option::None;
            loop {
              if input.input_len() == 0 {
                break;
              }
              match $submac!(input, $($args)*) {
                $crate::IResult::Error(_)                    => {
                  break;
                },
                $crate::IResult::Incomplete($crate::Needed::Unknown) => {
                  incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
                  break;
                },
                $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
                  let (size,overflowed) = i.overflowing_add( ($i).input_len() - input.input_len() );
                  incomplete = ::std::option::Option::Some(
                      match overflowed {
                          true  => $crate::Needed::Unknown,
                          false => $crate::Needed::Size(size),
                      }
                  );
                  break;
                },
                $crate::IResult::Done(i, o) => {
                  if i.input_len() == input.input_len() {
                    break;
                  }
                  acc = f(acc, o);
                  input = i;
                }
              }
            }

            match incomplete {
              ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
              ::std::option::Option::None    => $crate::IResult::Done(input, acc)
            }
          }
        }
      }
    }
  );
  ($i:expr, $f:expr, $init:expr, $fold_f:expr) => (
    fold_many1!($i, call!($f), $init, $fold_f);
  );
);

/// `fold_many_m_n!(usize, usize, I -> IResult<I,O>, R, Fn(R, O) -> R) => I -> IResult<I, R>`
/// Applies the parser between m and n times (n included) and folds the list of return value
///
/// the embedded parser may return Incomplete
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{Done, Error};
/// # #[cfg(feature = "verbose-errors")]
/// # use nom::Err::Position;
/// # use nom::ErrorKind;
/// # fn main() {
///  named!(multi<&[u8], Vec<&[u8]> >,
///    fold_many_m_n!(2, 4, tag!( "abcd" ), Vec::new(), |mut acc: Vec<_>, item| {
///      acc.push(item);
///      acc
///  }));
///
///  let a = b"abcdefgh";
///  let b = b"abcdabcdefgh";
///  let c = b"abcdabcdabcdabcdabcdefgh";
///
///  assert_eq!(multi(&a[..]),Error(error_position!(ErrorKind::ManyMN,&a[..])));
///  let res = vec![&b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&b[..]), Done(&b"efgh"[..], res));
///  let res2 = vec![&b"abcd"[..], &b"abcd"[..], &b"abcd"[..], &b"abcd"[..]];
///  assert_eq!(multi(&c[..]), Done(&b"abcdefgh"[..], res2));
/// # }
/// ```
#[macro_export]
macro_rules! fold_many_m_n(
  ($i:expr, $m:expr, $n: expr, $submac:ident!( $($args:tt)* ), $init:expr, $f:expr) => (
    {
      use $crate::InputLength;
      let mut acc          = $init;
      let     f            = $f;
      let mut input        = $i.clone();
      let mut count: usize = 0;
      let mut err          = false;
      let mut incomplete: ::std::option::Option<$crate::Needed> = ::std::option::Option::None;
      loop {
        if count == $n { break }
        match $submac!(input, $($args)*) {
          $crate::IResult::Done(i, o) => {
            // do not allow parsers that do not consume input (causes infinite loops)
            if i.input_len() == input.input_len() {
              break;
            }
            acc = f(acc, o);
            input  = i;
            count += 1;
          }
          $crate::IResult::Error(_)                    => {
            err = true;
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Unknown) => {
            incomplete = ::std::option::Option::Some($crate::Needed::Unknown);
            break;
          },
          $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
            let (size,overflowed) = i.overflowing_add( ($i).input_len() - input.input_len() );
            incomplete = ::std::option::Option::Some(
              match overflowed {
                  true  => $crate::Needed::Unknown,
                  false => $crate::Needed::Size(size),
              }
            );
            break;
          },
        }
        if input.input_len() == 0 {
          break;
        }
      }

      if count < $m {
        if err {
          $crate::IResult::Error(error_position!($crate::ErrorKind::ManyMN,$i))
        } else {
          match incomplete {
            ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
            ::std::option::Option::None    => $crate::IResult::Incomplete($crate::Needed::Unknown)
          }
        }
      } else {
        match incomplete {
          ::std::option::Option::Some(i) => $crate::IResult::Incomplete(i),
          ::std::option::Option::None    => $crate::IResult::Done(input, acc)
        }
      }
    }
  );
  ($i:expr, $m:expr, $n: expr, $f:expr, $init:expr, $fold_f:expr) => (
    fold_many_m_n!($i, $m, $n, call!($f), $init, $fold_f);
  );
);

#[cfg(test)]
mod tests {
  use internal::{Needed,IResult};

  use internal::IResult::*;
  use util::ErrorKind;
  use nom::{alpha,be_u8,be_u16,le_u16,digit};
  use std::str::{self,FromStr};

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
    )
  );

  #[test]
  #[cfg(feature = "std")]
  fn separated_list() {
    named!(multi<&[u8],Vec<&[u8]> >, separated_list!(tag!(","), tag!("abcd")));
    named!(multi_empty<&[u8],Vec<&[u8]> >, separated_list!(tag!(","), tag!("")));
    named!(multi_longsep<&[u8],Vec<&[u8]> >, separated_list!(tag!(".."), tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"azerty"[..];
    let d = &b",,abc"[..];
    let e = &b"abcd,abcd,ef"[..];
    let f = &b"abc"[..];
    let g = &b"abcd."[..];
    let h = &b"abcd,abc"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"ef"[..], res2));
    assert_eq!(multi(c), Done(&b"azerty"[..], Vec::new()));
    assert_eq!(multi_empty(d), Error(error_position!(ErrorKind::SeparatedList, d)));
    //let res3 = vec![&b""[..], &b""[..], &b""[..]];
    //assert_eq!(multi_empty(d), Done(&b"abc"[..], res3));
    let res4 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(e), Done(&b",ef"[..], res4));

    assert_eq!(multi(f), Incomplete(Needed::Size(4)));
    assert_eq!(multi_longsep(g), Incomplete(Needed::Size(6)));
    assert_eq!(multi(h), Incomplete(Needed::Size(9)));
  }

  #[test]
  #[cfg(feature = "std")]
  fn separated_list_complete() {
    named!(multi<&[u8],Vec<&[u8]> >, separated_list_complete!(tag!(","), alpha));
    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"abcd,abcd,ef"[..];
    let d = &b"abc."[..];
    let e = &b"abcd,ef."[..];
    let f = &b"123"[..];

    assert_eq!(multi(a), Done(&b""[..], vec!(a)));
    assert_eq!(multi(b), Done(&b""[..], vec!(&b"abcd"[..], &b"abcdef"[..])));
    assert_eq!(multi(c), Done(&b""[..], vec!(&b"abcd"[..], &b"abcd"[..], &b"ef"[..])));
    assert_eq!(multi(d), Done(&b"."[..], vec!(&b"abc"[..])));
    assert_eq!(multi(e), Done(&b"."[..], vec!(&b"abcd"[..], &b"ef"[..])));
    assert_eq!(multi(f), Done(&b"123"[..], Vec::new()));
  }


  #[test]
  #[cfg(feature = "std")]
  fn separated_nonempty_list() {
    named!(multi<&[u8],Vec<&[u8]> >, separated_nonempty_list!(tag!(","), tag!("abcd")));
    named!(multi_longsep<&[u8],Vec<&[u8]> >, separated_nonempty_list!(tag!(".."), tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"azerty"[..];
    let d = &b"abcd,abcd,ef"[..];

    let f = &b"abc"[..];
    let g = &b"abcd."[..];
    let h = &b"abcd,abc"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"ef"[..], res2));
    assert_eq!(multi(c), Error(error_position!(ErrorKind::Tag,c)));
    let res3 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(d), Done(&b",ef"[..], res3));

    assert_eq!(multi(f), Incomplete(Needed::Size(4)));
    assert_eq!(multi_longsep(g), Incomplete(Needed::Size(6)));
    assert_eq!(multi(h), Incomplete(Needed::Size(9)));
  }

  #[test]
  #[cfg(feature = "std")]
  fn separated_nonempty_list_complete() {
    named!(multi<&[u8],Vec<&[u8]> >, separated_nonempty_list_complete!(tag!(","), alpha));
    let a = &b"abcdef"[..];
    let b = &b"abcd,abcdef"[..];
    let c = &b"abcd,abcd,ef"[..];
    let d = &b"abc."[..];
    let e = &b"abcd,ef."[..];
    let f = &b"123"[..];

    assert_eq!(multi(a), Done(&b""[..], vec!(a)));
    assert_eq!(multi(b), Done(&b""[..], vec!(&b"abcd"[..], &b"abcdef"[..])));
    assert_eq!(multi(c), Done(&b""[..], vec!(&b"abcd"[..], &b"abcd"[..], &b"ef"[..])));
    assert_eq!(multi(d), Done(&b"."[..], vec!(&b"abc"[..])));
    assert_eq!(multi(e), Done(&b"."[..], vec!(&b"abcd"[..], &b"ef"[..])));
    assert_eq!(multi(f), Error(error_position!(ErrorKind::Alpha, &b"123"[..])));
  }


  #[test]
  #[cfg(feature = "std")]
  fn many0() {
    named!( tag_abcd, tag!("abcd") );
    named!( tag_empty, tag!("") );
    named!( multi<&[u8],Vec<&[u8]> >, many0!(tag_abcd) );
    named!( multi_empty<&[u8],Vec<&[u8]> >, many0!(tag_empty) );

    assert_eq!(multi(&b"abcdef"[..]), Done(&b"ef"[..], vec![&b"abcd"[..]]));
    assert_eq!(multi(&b"abcdabcdefgh"[..]), Done(&b"efgh"[..], vec![&b"abcd"[..], &b"abcd"[..]]));
    assert_eq!(multi(&b"azerty"[..]), Done(&b"azerty"[..], Vec::new()));
    assert_eq!(multi(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(multi(&b"abcd"[..]), Done(&b""[..], vec![&b"abcd"[..]]));
    assert_eq!(multi(&b""[..]), Done(&b""[..], Vec::new()));
    assert_eq!(multi_empty(&b"abcdef"[..]), Error(error_position!(ErrorKind::Many0, &b"abcdef"[..])));
  }

  #[cfg(feature = "nightly")]
  use test::Bencher;

  #[cfg(feature = "nightly")]
  #[bench]
  fn many0_bench(b: &mut Bencher) {
    named!(multi<&[u8],Vec<&[u8]> >, many0!(tag!("abcd")));
    b.iter(|| {
      multi(&b"abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"[..])
    });
  }

  #[test]
  #[cfg(feature = "std")]
  fn many1() {
    named!(multi<&[u8],Vec<&[u8]> >, many1!(tag!("abcd")));

    let a = &b"abcdef"[..];
    let b = &b"abcdabcdefgh"[..];
    let c = &b"azerty"[..];
    let d = &b"abcdab"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res2));
    assert_eq!(multi(c), Error(error_position!(ErrorKind::Many1,c)));
    assert_eq!(multi(d), Incomplete(Needed::Size(8)));
  }

  #[test]
  #[cfg(feature = "std")]
  fn many_till() {
    named!(multi<&[u8], (Vec<&[u8]>, &[u8]) >, many_till!( tag!( "abcd" ), tag!( "efgh" ) ) );

    let a = b"abcdabcdefghabcd";
    let b = b"efghabcd";
    let c = b"azerty";

    let res_a = (vec![&b"abcd"[..], &b"abcd"[..]], &b"efgh"[..]);
    let res_b: (Vec<&[u8]>, &[u8]) = (Vec::new(), &b"efgh"[..]);
    assert_eq!(multi(&a[..]), Done(&b"abcd"[..], res_a));
    assert_eq!(multi(&b[..]), Done(&b"abcd"[..], res_b));
    assert_eq!(multi(&c[..]), Error(error_node_position!(ErrorKind::ManyTill,&c[..], error_position!(ErrorKind::Tag,&c[..]))));
  }

  #[test]
  #[cfg(feature = "std")]
  fn infinite_many() {
    fn tst(input: &[u8]) -> IResult<&[u8], &[u8]> {
      println!("input: {:?}", input);
      Error(error_position!(ErrorKind::Custom(0),input))
    }

    // should not go into an infinite loop
    named!(multi0<&[u8],Vec<&[u8]> >, many0!(tst));
    let a = &b"abcdef"[..];
    assert_eq!(multi0(a), Done(a, Vec::new()));

    named!(multi1<&[u8],Vec<&[u8]> >, many1!(tst));
    let a = &b"abcdef"[..];
    assert_eq!(multi1(a), Error(error_position!(ErrorKind::Many1,a)));
  }

  #[test]
  #[cfg(feature = "std")]
  fn many_m_n() {
    named!(multi<&[u8],Vec<&[u8]> >, many_m_n!(2, 4, tag!("Abcd")));

    let a = &b"Abcdef"[..];
    let b = &b"AbcdAbcdefgh"[..];
    let c = &b"AbcdAbcdAbcdAbcdefgh"[..];
    let d = &b"AbcdAbcdAbcdAbcdAbcdefgh"[..];
    let e = &b"AbcdAb"[..];

    assert_eq!(multi(a), Error(error_position!(ErrorKind::ManyMN,a)));
    let res1 = vec![&b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res1));
    let res2 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(c), Done(&b"efgh"[..], res2));
    let res3 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(d), Done(&b"Abcdefgh"[..], res3));
    assert_eq!(multi(e), Incomplete(Needed::Size(8)));
  }

  #[test]
  #[cfg(feature = "std")]
  fn count() {
    const TIMES: usize = 2;
    named!( tag_abc, tag!("abc") );
    named!( cnt_2<&[u8], Vec<&[u8]> >, count!(tag_abc, TIMES ) );

    assert_eq!(cnt_2(&b"abcabcabcdef"[..]), Done(&b"abcdef"[..], vec![&b"abc"[..], &b"abc"[..]]));
    assert_eq!(cnt_2(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(cnt_2(&b"abcab"[..]), Incomplete(Needed::Size(6)));
    assert_eq!(cnt_2(&b"xxx"[..]), Error(error_position!(ErrorKind::Count, &b"xxx"[..])));
    assert_eq!(cnt_2(&b"xxxabcabcdef"[..]), Error(error_position!(ErrorKind::Count, &b"xxxabcabcdef"[..])));
    assert_eq!(cnt_2(&b"abcxxxabcdef"[..]), Error(error_position!(ErrorKind::Count, &b"abcxxxabcdef"[..])));
  }

  #[test]
  #[cfg(feature = "std")]
  fn count_zero() {
    const TIMES: usize = 0;
    named!( tag_abc, tag!("abc") );
    named!( counter_2<&[u8], Vec<&[u8]> >, count!(tag_abc, TIMES ) );

    let done = &b"abcabcabcdef"[..];
    let parsed_done = Vec::new();
    let rest = done;
    let incomplete_1 = &b"ab"[..];
    let parsed_incompl_1 = Vec::new();
    let incomplete_2 = &b"abcab"[..];
    let parsed_incompl_2 = Vec::new();
    let error = &b"xxx"[..];
    let error_remain = &b"xxx"[..];
    let parsed_err = Vec::new();
    let error_1 = &b"xxxabcabcdef"[..];
    let parsed_err_1 = Vec::new();
    let error_1_remain = &b"xxxabcabcdef"[..];
    let error_2 = &b"abcxxxabcdef"[..];
    let parsed_err_2 = Vec::new();
    let error_2_remain = &b"abcxxxabcdef"[..];

    assert_eq!(counter_2(done), Done(rest, parsed_done));
    assert_eq!(counter_2(incomplete_1), Done(incomplete_1, parsed_incompl_1));
    assert_eq!(counter_2(incomplete_2), Done(incomplete_2, parsed_incompl_2));
    assert_eq!(counter_2(error), Done(error_remain, parsed_err));
    assert_eq!(counter_2(error_1), Done(error_1_remain, parsed_err_1));
    assert_eq!(counter_2(error_2), Done(error_2_remain, parsed_err_2));
  }

  #[test]
  fn count_fixed() {
    const TIMES: usize = 2;
    named!( tag_abc, tag!("abc") );
    named!( cnt_2<&[u8], [&[u8]; TIMES] >, count_fixed!(&[u8], tag_abc, TIMES ) );

    assert_eq!(cnt_2(&b"abcabcabcdef"[..]), Done(&b"abcdef"[..], [&b"abc"[..], &b"abc"[..]]));
    assert_eq!(cnt_2(&b"ab"[..]), Incomplete(Needed::Size(3)));
    assert_eq!(cnt_2(&b"abcab"[..]), Incomplete(Needed::Size(6)));
    assert_eq!(cnt_2(&b"xxx"[..]), Error(error_position!(ErrorKind::Count, &b"xxx"[..])));
    assert_eq!(cnt_2(&b"xxxabcabcdef"[..]), Error(error_position!(ErrorKind::Count, &b"xxxabcabcdef"[..])));
    assert_eq!(cnt_2(&b"abcxxxabcdef"[..]), Error(error_position!(ErrorKind::Count, &b"abcxxxabcdef"[..])));
  }

  #[allow(dead_code)]
  pub fn compile_count_fixed(input: &[u8]) -> IResult<&[u8], ()> {
    do_parse!(input,
      tag!("abcd")                   >>
      count_fixed!( u16, le_u16, 4 ) >>
      eof!()                         >>
      ()
    )
  }

  #[allow(unused_variables)]
  #[test]
  fn count_fixed_no_type() {
    const TIMES: usize = 2;
    named!( tag_abc, tag!("abc") );
    named!( counter_2<&[u8], [&[u8]; TIMES], () >, count_fixed!(&[u8], tag_abc, TIMES ) );

    let done = &b"abcabcabcdef"[..];
    let parsed_main = [&b"abc"[..], &b"abc"[..]];
    let rest = &b"abcdef"[..];
    let incomplete_1 = &b"ab"[..];
    let incomplete_2 = &b"abcab"[..];
    let error = &b"xxx"[..];
    let error_1 = &b"xxxabcabcdef"[..];
    let error_1_remain = &b"xxxabcabcdef"[..];
    let error_2 = &b"abcxxxabcdef"[..];
    let error_2_remain = &b"abcxxxabcdef"[..];

    assert_eq!(counter_2(done), Done(rest, parsed_main));
    assert_eq!(counter_2(incomplete_1), Incomplete(Needed::Size(3)));
    assert_eq!(counter_2(incomplete_2), Incomplete(Needed::Size(6)));
    assert_eq!(counter_2(error), Error(error_position!(ErrorKind::Count, error)));
    assert_eq!(counter_2(error_1), Error(error_position!(ErrorKind::Count, error_1_remain)));
    assert_eq!(counter_2(error_2), Error(error_position!(ErrorKind::Count, error_2_remain)));
  }

  named!(pub number<u32>, map_res!(
    map_res!(
      digit,
      str::from_utf8
    ),
    FromStr::from_str
  ));

  #[test]
  #[cfg(feature = "std")]
  fn length_count() {
    named!(tag_abc, tag!(&b"abc"[..]) );
    named!( cnt<&[u8], Vec<&[u8]> >, length_count!(number, tag_abc) );

    assert_eq!(cnt(&b"2abcabcabcdef"[..]), Done(&b"abcdef"[..], vec![&b"abc"[..], &b"abc"[..]]));
    assert_eq!(cnt(&b"2ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(cnt(&b"3abcab"[..]), Incomplete(Needed::Size(7)));
    assert_eq!(cnt(&b"xxx"[..]), Error(error_position!(ErrorKind::Digit, &b"xxx"[..])));
    assert_eq!(cnt(&b"2abcxxx"[..]), Error(error_position!(ErrorKind::Count, &b"abcxxx"[..])));
  }

  #[test]
  fn length_data() {
    named!( take<&[u8], &[u8]>, length_data!(number) );

    assert_eq!(take(&b"6abcabcabcdef"[..]), Done(&b"abcdef"[..], &b"abcabc"[..]));
    assert_eq!(take(&b"3ab"[..]), Incomplete(Needed::Size(4)));
    assert_eq!(take(&b"xxx"[..]), Error(error_position!(ErrorKind::Digit, &b"xxx"[..])));
    assert_eq!(take(&b"2abcxxx"[..]), Done(&b"cxxx"[..], &b"ab"[..]));
  }

  #[test]
  fn length_value_test() {
    named!(length_value_1<&[u8], u16 >, length_value!(be_u8, be_u16));
    named!(length_value_2<&[u8], (u8, u8) >, length_value!(be_u8, tuple!(be_u8, be_u8)));

    let i1 = [0, 5, 6];
    assert_eq!(length_value_1(&i1), IResult::Error(error_position!(ErrorKind::Complete, &b""[..])));
    assert_eq!(length_value_2(&i1), IResult::Error(error_position!(ErrorKind::Complete, &b""[..])));

    let i2 = [1, 5, 6, 3];
    assert_eq!(length_value_1(&i2), IResult::Error(error_position!(ErrorKind::Complete, &i2[1..2])));
    assert_eq!(length_value_2(&i2), IResult::Error(error_position!(ErrorKind::Complete, &i2[1..2])));

    let i3 = [2, 5, 6, 3, 4, 5, 7];
    assert_eq!(length_value_1(&i3), IResult::Done(&i3[3..], 1286));
    assert_eq!(length_value_2(&i3), IResult::Done(&i3[3..], (5, 6)));

    let i4 = [3, 5, 6, 3, 4, 5];
    assert_eq!(length_value_1(&i4), IResult::Done(&i4[4..], 1286));
    assert_eq!(length_value_2(&i4), IResult::Done(&i4[4..], (5, 6)));
  }

  #[test]
  #[cfg(feature = "std")]
  fn fold_many0() {
    fn fold_into_vec<T>(mut acc: Vec<T>, item: T) -> Vec<T> {
      acc.push(item);
      acc
    };
    named!( tag_abcd, tag!("abcd") );
    named!( tag_empty, tag!("") );
    named!( multi<&[u8],Vec<&[u8]> >, fold_many0!(tag_abcd, Vec::new(), fold_into_vec) );
    named!( multi_empty<&[u8],Vec<&[u8]> >, fold_many0!(tag_empty, Vec::new(), fold_into_vec) );

    assert_eq!(multi(&b"abcdef"[..]), Done(&b"ef"[..], vec![&b"abcd"[..]]));
    assert_eq!(multi(&b"abcdabcdefgh"[..]), Done(&b"efgh"[..], vec![&b"abcd"[..], &b"abcd"[..]]));
    assert_eq!(multi(&b"azerty"[..]), Done(&b"azerty"[..], Vec::new()));
    assert_eq!(multi(&b"abcdab"[..]), Incomplete(Needed::Size(8)));
    assert_eq!(multi(&b"abcd"[..]), Done(&b""[..], vec![&b"abcd"[..]]));
    assert_eq!(multi(&b""[..]), Done(&b""[..], Vec::new()));
    assert_eq!(multi_empty(&b"abcdef"[..]), Error(error_position!(ErrorKind::Many0, &b"abcdef"[..])));
  }

  #[test]
  #[cfg(feature = "std")]
  fn fold_many1() {
    fn fold_into_vec<T>(mut acc: Vec<T>, item: T) -> Vec<T> {
      acc.push(item);
      acc
    };
    named!(multi<&[u8],Vec<&[u8]> >, fold_many1!(tag!("abcd"), Vec::new(), fold_into_vec));

    let a = &b"abcdef"[..];
    let b = &b"abcdabcdefgh"[..];
    let c = &b"azerty"[..];
    let d = &b"abcdab"[..];

    let res1 = vec![&b"abcd"[..]];
    assert_eq!(multi(a), Done(&b"ef"[..], res1));
    let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res2));
    assert_eq!(multi(c), Error(error_position!(ErrorKind::Many1,c)));
    assert_eq!(multi(d), Incomplete(Needed::Size(8)));
  }

  #[test]
  #[cfg(feature = "std")]
  fn fold_many_m_n() {
    fn fold_into_vec<T>(mut acc: Vec<T>, item: T) -> Vec<T> {
      acc.push(item);
      acc
    };
    named!(multi<&[u8],Vec<&[u8]> >, fold_many_m_n!(2, 4, tag!("Abcd"), Vec::new(), fold_into_vec));

    let a = &b"Abcdef"[..];
    let b = &b"AbcdAbcdefgh"[..];
    let c = &b"AbcdAbcdAbcdAbcdefgh"[..];
    let d = &b"AbcdAbcdAbcdAbcdAbcdefgh"[..];
    let e = &b"AbcdAb"[..];

    assert_eq!(multi(a), Error(error_position!(ErrorKind::ManyMN,a)));
    let res1 = vec![&b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(b), Done(&b"efgh"[..], res1));
    let res2 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(c), Done(&b"efgh"[..], res2));
    let res3 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
    assert_eq!(multi(d), Done(&b"Abcdefgh"[..], res3));
    assert_eq!(multi(e), Incomplete(Needed::Size(8)));
  }

}
