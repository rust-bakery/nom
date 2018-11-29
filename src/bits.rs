//! Bit level parsers and combinators
//!
//! Bit parsing is handled by tweaking the input in most macros.
//! In byte level parsing, the input is generally a `&[u8]` passed from combinator
//! to combinator as the slices are manipulated.
//!
//! Bit parsers take a `(&[u8], usize)` as input. The first part of the tuple is a byte slice,
//! the second part is a bit offset in the first byte of the slice.
//!
//! By passing a pair like this, we can leverage most of the existing combinators, and avoid
//! transforming the whole slice to a vector of booleans. This should make it easy
//! to see a byte slice as a bit stream, and parse code points of arbitrary bit length.
//!

/// Transforms its byte slice input into a bit stream for the underlying parser. This allows the
/// given bit stream parser to work on a byte slice input.
///
/// Signature:
/// `bits!( parser ) => ( &[u8], (&[u8], usize) -> IResult<(&[u8], usize), T> ) -> IResult<&[u8], T>`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!( take_4_bits<u8>, bits!( take_bits!( u8, 4 ) ) );
///
///  let input = vec![0xAB, 0xCD, 0xEF, 0x12];
///  let sl    = &input[..];
///
///  assert_eq!(take_4_bits( sl ), Ok( (&sl[1..], 0xA) ));
/// # }
#[macro_export]
macro_rules! bits (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    bits_impl!($i, $submac!($($args)*));
  );
  ($i:expr, $f:expr) => (
    bits_impl!($i, call!($f));
  );
);

#[cfg(feature = "verbose-errors")]
/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! bits_impl (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::lib::std::result::Result::*;
      use $crate::{Context,Err,Needed};

      let input = ($i, 0usize);
      match $submac!(input, $($args)*) {
        Err(Err::Error(e)) => {
          let err = match e {
            Context::Code((i,b), kind) => Context::Code(&i[b/8..], kind),
            Context::List(mut v) => {
              Context::List(v.drain(..).map(|((i,b), kind)| (&i[b/8..], kind)).collect())
            }
          };
          Err(Err::Error(err))
        },
        Err(Err::Failure(e)) => {
          let err = match e {
            Context::Code((i,b), kind) => Context::Code(&i[b/8..], kind),
            Context::List(mut v) => {
              Context::List(v.drain(..).map(|((i,b), kind)| (&i[b/8..], kind)).collect())
            }
          };
          Err(Err::Failure(err))
        },
        Err(Err::Incomplete(Needed::Unknown)) => Err(Err::Incomplete(Needed::Unknown)),
        Err(Err::Incomplete(Needed::Size(i))) => {
          //println!("bits parser returned Needed::Size({})", i);
          Err(Err::Incomplete(Needed::Size(i / 8 + 1)))
        },
        Ok(((i, bit_index), o))             => {
          let byte_index = bit_index / 8 + if bit_index % 8 == 0 { 0 } else { 1 } ;
          //println!("bit index=={} => byte index=={}", bit_index, byte_index);
          Ok((&i[byte_index..], o))
        }
      }
    }
  );
);

#[cfg(not(feature = "verbose-errors"))]
/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! bits_impl (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::lib::std::result::Result::*;
      use $crate::{Err,Needed,Context};

      let input = ($i, 0usize);
      match $submac!(input, $($args)*) {
        Err(Err::Error(e)) => {
          let Context::Code(_,err) = e;
          Err(Err::Error(error_position!($i, err)))
        },
        Err(Err::Failure(e)) => {
          let Context::Code(_,err) = e;
          Err(Err::Failure(error_position!($i, err)))
        },
        Err(Err::Incomplete(Needed::Unknown)) => Err(Err::Incomplete(Needed::Unknown)),
        Err(Err::Incomplete(Needed::Size(i))) => {
          //println!("bits parser returned Needed::Size({})", i);
          $crate::need_more($i, $crate::Needed::Size(i / 8 + 1))
        },
        Ok(((i, bit_index), o))             => {
          let byte_index = bit_index / 8 + if bit_index % 8 == 0 { 0 } else { 1 } ;
          //println!("bit index=={} => byte index=={}", bit_index, byte_index);
          Ok((&i[byte_index..], o))
        }
      }
    }
  );
);

/// Counterpart to bits, bytes! transforms its bit stream input into a byte slice for the underlying
/// parser, allowing byte-slice parsers to work on bit streams.
///
/// Signature:
/// `bytes!( parser ) => ( (&[u8], usize), &[u8] -> IResult<&[u8], T> ) -> IResult<(&[u8], usize), T>`,
///
/// A partial byte remaining in the input will be ignored and the given parser will start parsing
/// at the next full byte.
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::rest;
/// # fn main() {
///  named!( parse<(u8, u8, &[u8])>,  bits!( tuple!(
///    take_bits!(u8, 4),
///    take_bits!(u8, 8),
///    bytes!(rest)
/// )));
///
///  let input = &[0xde, 0xad, 0xbe, 0xaf];
///
///  assert_eq!(parse( input ), Ok(( &[][..], (0xd, 0xea, &[0xbe, 0xaf][..]) )));
/// # }
#[macro_export]
macro_rules! bytes (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    bytes_impl!($i, $submac!($($args)*));
  );
  ($i:expr, $f:expr) => (
    bytes_impl!($i, call!($f));
  );
);

#[cfg(feature = "verbose-errors")]
/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! bytes_impl (
  ($macro_i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::lib::std::result::Result::*;
      use $crate::{Err,Needed,Context};

      let inp;
      if $macro_i.1 % 8 != 0 {
        inp = & $macro_i.0[1 + $macro_i.1 / 8 ..];
      }
      else {
        inp = & $macro_i.0[$macro_i.1 / 8 ..];
      }

      let sub = $submac!(inp, $($args)*);
      let res = match sub {
        Err(Err::Incomplete(Needed::Size(i))) => {
          Err(Err::Incomplete(Needed::Size(i * 8)))
        },
        Err(Err::Incomplete(Needed::Unknown)) => Err(Err::Incomplete(Needed::Unknown)),
        Ok((i, o)) => {
          Ok(((i, 0), o))
        },
        Err(Err::Error(e)) => {
          let err = match e {
            Context::Code(i, c) => Context::Code((i,0), c),
            Context::List(mut v) => {
              let (i, c) = v.remove(0);
              Context::Code((i,0), c)
            }
          };
          Err(Err::Error(err))
        },
        Err(Err::Failure(e)) => {
          let err = match e {
            Context::Code(i, c) => Context::Code((i,0), c),
            Context::List(mut v) => {
              let (i, c) = v.remove(0);
              Context::Code((i,0), c)
            }
          };
          Err(Err::Error(err))
        },
        Err(Err::Incomplete(Needed::Unknown)) => Err(Err::Incomplete(Needed::Unknown)),
        Err(Err::Incomplete(Needed::Size(i))) => {
          Err(Err::Incomplete(Needed::Size(i * 8)))
        },
        Ok((i, o)) => {
          Ok(((i, 0), o))
        }
      };
      res
    }
  );
);

#[cfg(not(feature = "verbose-errors"))]
/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! bytes_impl (
  ($macro_i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::lib::std::result::Result::*;
      use $crate::{Err,Needed,Context};

      let inp;
      if $macro_i.1 % 8 != 0 {
        inp = & $macro_i.0[1 + $macro_i.1 / 8 ..];
      }
      else {
        inp = & $macro_i.0[$macro_i.1 / 8 ..];
      }

      let sub = $submac!(inp, $($args)*);
      let res = match sub {
        Err(Err::Incomplete(Needed::Size(i))) => {
          Err(Err::Incomplete(Needed::Size(i * 8)))
        },
        Err(Err::Incomplete(Needed::Unknown)) => Err(Err::Incomplete(Needed::Unknown)),
        Ok((i, o)) => {
          Ok(((i, 0), o))
        },
        Err(Err::Error(e)) => {
          let Context::Code(i, c) = e;
          Err(Err::Error(Context::Code((i,0), c)))
        },
        Err(Err::Failure(e)) => {
          let Context::Code(i, c) = e;
          Err(Err::Failure(Context::Code((i,0), c)))
        },
      };
      res
    }
  );
);

/// Consumes the specified number of bits and returns them as the specified type.
///
/// Signature:
/// `take_bits!(type, count) => ( (&[T], usize), U, usize) -> IResult<(&[T], usize), U>`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!( take_pair<(u8, u8)>, bits!( pair!( take_bits!(u8, 4), take_bits!(u8, 4) ) ) );
///
///  let input = vec![0xAB, 0xCD, 0xEF];
///  let sl    = &input[..];
///
///  assert_eq!(take_pair( sl ),       Ok((&sl[1..], (0xA, 0xB))) );
///  assert_eq!(take_pair( &sl[1..] ), Ok((&sl[2..], (0xC, 0xD))) );
/// # }
/// ```
#[macro_export]
macro_rules! take_bits (
  ($i:expr, $t:ty, $count:expr) => (
    {
      use $crate::lib::std::result::Result::*;
      use $crate::{Needed,IResult};

      use $crate::lib::std::ops::Div;
      use $crate::lib::std::convert::Into;
      //println!("taking {} bits from {:?}", $count, $i);
      let (input, bit_offset) = $i;
      let res : IResult<(&[u8],usize), $t> = if $count == 0 {
        Ok(( (input, bit_offset), (0 as u8).into()))
      } else {
        let cnt = ($count as usize + bit_offset).div(8);
        if input.len() * 8 < $count as usize + bit_offset {
          //println!("returning incomplete: {}", $count as usize + bit_offset);
          $crate::need_more($i, Needed::Size($count as usize))
        } else {
          let mut acc:$t            = (0 as u8).into();
          let mut offset: usize     = bit_offset;
          let mut remaining: usize  = $count;
          let mut end_offset: usize = 0;

          for byte in input.iter().take(cnt + 1) {
            if remaining == 0 {
              break;
            }
            let val: $t = if offset == 0 {
              (*byte as u8).into()
            } else {
              (((*byte as u8) << offset) as u8 >> offset).into()
            };

            if remaining < 8 - offset {
              acc += val >> (8 - offset - remaining);
              end_offset = remaining + offset;
              break;
            } else {
              acc += val << (remaining - (8 - offset));
              remaining -= 8 - offset;
              offset = 0;
            }
          }
          Ok(( (&input[cnt..], end_offset) , acc))
        }
      };
      res
    }
  );
);

/// Matches the given bit pattern.
///
/// Signature:
/// `tag_bits!(type, count, pattern) => ( (&[T], usize), U, usize, U) -> IResult<(&[T], usize), U>`
///
/// The caller must specify the number of bits to consume. The matched value is included in the
/// result on success.
///
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!( take_a<u8>, bits!( tag_bits!(u8, 4, 0xA) ) );
///
///  let input = vec![0xAB, 0xCD, 0xEF];
///  let sl    = &input[..];
///
///  assert_eq!(take_a( sl ),       Ok((&sl[1..], 0xA)) );
/// # }
/// ```
#[macro_export]
macro_rules! tag_bits (
  ($i:expr, $t:ty, $count:expr, $p: pat) => (
    {
      use $crate::lib::std::result::Result::*;
      use $crate::{Err,IResult};

      match take_bits!($i, $t, $count) {
        Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
        Ok((i, o))    => {
          if let $p = o {
            let res: IResult<(&[u8],usize),$t> = Ok((i, o));
            res
          } else {
            let e: $crate::ErrorKind<u32> = $crate::ErrorKind::TagBits;
            Err(Err::Error(error_position!($i, e)))
          }
        },
        _                              => {
          let e: $crate::ErrorKind<u32> = $crate::ErrorKind::TagBits;
          Err(Err::Error(error_position!($i, e)))
        }
      }
    }
  )
);

#[cfg(test)]
mod tests {
  use lib::std::ops::{AddAssign, Shl, Shr};
  use internal::{Err, Needed};
  use util::ErrorKind;

  #[test]
  fn take_bits() {
    let input = [0b10_10_10_10, 0b11_11_00_00, 0b00_11_00_11];
    let sl = &input[..];

    assert_eq!(take_bits!((sl, 0), u8, 0), Ok(((sl, 0), 0)));
    assert_eq!(take_bits!((sl, 0), u8, 8), Ok(((&sl[1..], 0), 170)));
    assert_eq!(take_bits!((sl, 0), u8, 3), Ok(((&sl[0..], 3), 5)));
    assert_eq!(take_bits!((sl, 0), u8, 6), Ok(((&sl[0..], 6), 42)));
    assert_eq!(take_bits!((sl, 1), u8, 1), Ok(((&sl[0..], 2), 0)));
    assert_eq!(take_bits!((sl, 1), u8, 2), Ok(((&sl[0..], 3), 1)));
    assert_eq!(take_bits!((sl, 1), u8, 3), Ok(((&sl[0..], 4), 2)));
    assert_eq!(take_bits!((sl, 6), u8, 3), Ok(((&sl[1..], 1), 5)));
    assert_eq!(take_bits!((sl, 0), u16, 10), Ok(((&sl[1..], 2), 683)));
    assert_eq!(take_bits!((sl, 0), u16, 8), Ok(((&sl[1..], 0), 170)));
    assert_eq!(take_bits!((sl, 6), u16, 10), Ok(((&sl[2..], 0), 752)));
    assert_eq!(take_bits!((sl, 6), u16, 11), Ok(((&sl[2..], 1), 1504)));
    assert_eq!(take_bits!((sl, 0), u32, 20), Ok(((&sl[2..], 4), 700_163)));
    assert_eq!(take_bits!((sl, 4), u32, 20), Ok(((&sl[3..], 0), 716_851)));
    assert_eq!(
      take_bits!((sl, 4), u32, 22),
      Err(Err::Incomplete(Needed::Size(22)))
    );
  }

  #[test]
  fn tag_bits() {
    let input = [0b10_10_10_10, 0b11_11_00_00, 0b00_11_00_11];
    let sl = &input[..];

    assert_eq!(tag_bits!((sl, 0), u8, 3, 0b101), Ok(((&sl[0..], 3), 5)));
    assert_eq!(tag_bits!((sl, 0), u8, 4, 0b1010), Ok(((&sl[0..], 4), 10)));
  }

  named!(ch<(&[u8],usize),(u8,u8)>,
    do_parse!(
      tag_bits!(u8, 3, 0b101) >>
      x: take_bits!(u8, 4)    >>
      y: take_bits!(u8, 5)    >>
      (x,y)
    )
  );

  #[test]
  fn chain_bits() {
    let input = [0b10_10_10_10, 0b11_11_00_00, 0b00_11_00_11];
    let sl = &input[..];
    assert_eq!(ch((&input[..], 0)), Ok(((&sl[1..], 4), (5, 15))));
    assert_eq!(ch((&input[..], 4)), Ok(((&sl[2..], 0), (7, 16))));
    assert_eq!(ch((&input[..1], 0)), Err(Err::Incomplete(Needed::Size(5))));
  }

  named!(ch_bytes<(u8, u8)>, bits!(ch));
  #[test]
  fn bits_to_bytes() {
    let input = [0b10_10_10_10, 0b11_11_00_00, 0b00_11_00_11];
    assert_eq!(ch_bytes(&input[..]), Ok((&input[2..], (5, 15))));
    assert_eq!(ch_bytes(&input[..1]), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      ch_bytes(&input[1..]),
      Err(Err::Error(error_position!(&input[1..], ErrorKind::TagBits)))
    );
  }

  #[derive(PartialEq, Debug)]
  struct FakeUint(u32);

  impl AddAssign for FakeUint {
    fn add_assign(&mut self, other: FakeUint) {
      *self = FakeUint(self.0 + other.0);
    }
  }

  impl Shr<usize> for FakeUint {
    type Output = FakeUint;

    fn shr(self, shift: usize) -> FakeUint {
      FakeUint(self.0 >> shift)
    }
  }

  impl Shl<usize> for FakeUint {
    type Output = FakeUint;

    fn shl(self, shift: usize) -> FakeUint {
      FakeUint(self.0 << shift)
    }
  }

  impl From<u8> for FakeUint {
    fn from(i: u8) -> FakeUint {
      FakeUint(u32::from(i))
    }
  }

  #[test]
  fn non_privitive_type() {
    let input = [0b10_10_10_10, 0b11_11_00_00, 0b00_11_00_11];
    let sl = &input[..];

    assert_eq!(
      take_bits!((sl, 0), FakeUint, 20),
      Ok(((&sl[2..], 4), FakeUint(700_163)))
    );
    assert_eq!(
      take_bits!((sl, 4), FakeUint, 20),
      Ok(((&sl[3..], 0), FakeUint(716_851)))
    );
    assert_eq!(
      take_bits!((sl, 4), FakeUint, 22),
      Err(Err::Incomplete(Needed::Size(22)))
    );
  }
}
