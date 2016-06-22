//! Bit level parsers and combinators
//!
//! Bit parsing is handled by tweaking the input in most macros.
//! In byte level parsing, the input is generally a `&[u8]` passed from combinator
//! to combinator until the slices are manipulated.
//!
//! Bit parsers take a `(&[u8], usize)` as input. The first part of the tuple is an byte slice,
//! the second part is a bit offset in the first byte of the slice.
//!
//! By passing a pair like this, we can leverage most of the combinators, and avoid
//! transforming the whole slice to a vector of booleans. This should make it easy
//! to see a byte slice as a bit stream, and parse code points of arbitrary bit length.


/// `bits!( parser ) => ( &[u8], (&[u8], usize) -> IResult<(&[u8], usize), T> ) -> IResult<&[u8], T>`
/// transforms its byte slice input into a bit stream for the underlying parsers
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!( take_3_bits<u8>, bits!( take_bits!( u8, 3 ) ) );
///
///  let input = vec![0b10101010, 0b11110000, 0b00110011];
///  let sl    = &input[..];
///
///  assert_eq!(take_3_bits( sl ), Done(&sl[1..], 5) );
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

/// Internal parser, do not use directly
#[doc(hidden)]
#[macro_export]
macro_rules! bits_impl (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let input = ($i, 0usize);
      match $submac!(input, $($args)*) {
        $crate::IResult::Error(e)                            => {
          let err = match e {
            $crate::Err::Code(k) | $crate::Err::Node(k, _) => $crate::Err::Code(k),
            $crate::Err::Position(k, (i,b)) | $crate::Err::NodePosition(k, (i,b), _) => {
              $crate::Err::Position(k, &i[b/8..])
            }
          };
          $crate::IResult::Error(err)
        }
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => {
          //println!("bits parser returned Needed::Size({})", i);
          $crate::IResult::Incomplete($crate::Needed::Size(i / 8 + 1))
        },
        $crate::IResult::Done((i, bit_index), o)             => {
          let byte_index = bit_index / 8 + if bit_index % 8 == 0 { 0 } else { 1 } ;
          //println!("bit index=={} => byte index=={}", bit_index, byte_index);
          $crate::IResult::Done(&i[byte_index..], o)
        }
      }
    }
  );
);

/// `take_bits!(type, nb) => ( (&[T], usize), U, usize) -> IResult<(&[T], usize), U>`
/// generates a parser consuming the specified number of bits.
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!( take_pair<(u8, u8)>, bits!( pair!( take_bits!( u8, 3 ), take_bits!(u8, 5) ) ) );
///
///  let input = vec![0b10101010, 0b11110000, 0b00110011];
///  let sl    = &input[..];
///
///  assert_eq!(take_pair( sl ),       Done(&sl[1..], (5, 10)) );
///  assert_eq!(take_pair( &sl[1..] ), Done(&sl[2..], (7, 16)) );
/// # }
/// ```
#[macro_export]
macro_rules! take_bits (
  ($i:expr, $t:ty, $count:expr) => (
    {
      use std::ops::Div;
      //println!("taking {} bits from {:?}", $count, $i);
      let (input, bit_offset) = $i;
      let res : $crate::IResult<(&[u8],usize), $t> = if $count == 0 {
        $crate::IResult::Done( (input, bit_offset), 0)
      } else {
        let cnt = ($count as usize + bit_offset).div(8);
        if input.len() * 8 < $count as usize + bit_offset {
          //println!("returning incomplete: {}", $count as usize + bit_offset);
          $crate::IResult::Incomplete($crate::Needed::Size($count as usize))
        } else {
          let mut acc:$t            = 0;
          let mut offset: usize     = bit_offset;
          let mut remaining: usize  = $count;
          let mut end_offset: usize = 0;

          for byte in input.iter().take(cnt + 1) {
            if remaining == 0 {
              break;
            }
            let val: $t = if offset == 0 {
              *byte as $t
            } else {
              ((*byte << offset) as u8 >> offset) as $t
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
          $crate::IResult::Done( (&input[cnt..], end_offset) , acc)
        }
      };
      res
    }
  );
);

/// matches an integer pattern to a bitstream. The number of bits of the input to compare must be specified
#[macro_export]
macro_rules! tag_bits (
  ($i:expr, $t:ty, $count:expr, $p: pat) => (
    {
      match take_bits!($i, $t, $count) {
        $crate::IResult::Incomplete(i) => $crate::IResult::Incomplete(i),
        $crate::IResult::Done(i, o)    => {
          if let $p = o {
            let res: $crate::IResult<(&[u8],usize),$t> = $crate::IResult::Done(i, o);
            res
          } else {
            $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::TagBits, $i))
          }
        },
        _                              => {
          $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::TagBits, $i))
        }
      }
    }
  )
);

#[cfg(test)]
mod tests {
  use internal::{IResult,Needed,Err};
  use ErrorKind;

  #[test]
  fn take_bits() {
    let input = vec![0b10101010, 0b11110000, 0b00110011];
    let sl    = &input[..];

    assert_eq!(take_bits!( (sl, 0), u8,   0 ), IResult::Done((sl, 0), 0));
    assert_eq!(take_bits!( (sl, 0), u8,   8 ), IResult::Done((&sl[1..], 0), 170));
    assert_eq!(take_bits!( (sl, 0), u8,   3 ), IResult::Done((&sl[0..], 3), 5));
    assert_eq!(take_bits!( (sl, 0), u8,   6 ), IResult::Done((&sl[0..], 6), 42));
    assert_eq!(take_bits!( (sl, 1), u8,   1 ), IResult::Done((&sl[0..], 2), 0));
    assert_eq!(take_bits!( (sl, 1), u8,   2 ), IResult::Done((&sl[0..], 3), 1));
    assert_eq!(take_bits!( (sl, 1), u8,   3 ), IResult::Done((&sl[0..], 4), 2));
    assert_eq!(take_bits!( (sl, 6), u8,   3 ), IResult::Done((&sl[1..], 1), 5));
    assert_eq!(take_bits!( (sl, 0), u16, 10 ), IResult::Done((&sl[1..], 2), 683));
    assert_eq!(take_bits!( (sl, 0), u16,  8 ), IResult::Done((&sl[1..], 0), 170));
    assert_eq!(take_bits!( (sl, 6), u16, 10 ), IResult::Done((&sl[2..], 0), 752));
    assert_eq!(take_bits!( (sl, 6), u16, 11 ), IResult::Done((&sl[2..], 1), 1504));
    assert_eq!(take_bits!( (sl, 0), u32, 20 ), IResult::Done((&sl[2..], 4), 700163));
    assert_eq!(take_bits!( (sl, 4), u32, 20 ), IResult::Done((&sl[3..], 0), 716851));
    assert_eq!(take_bits!( (sl, 4), u32, 22 ), IResult::Incomplete(Needed::Size(22)));
  }

  #[test]
  fn tag_bits() {
    let input = vec![0b10101010, 0b11110000, 0b00110011];
    let sl    = &input[..];

    assert_eq!(tag_bits!( (sl, 0), u8,   3, 0b101), IResult::Done((&sl[0..], 3), 5));
    assert_eq!(tag_bits!( (sl, 0), u8,   4, 0b1010), IResult::Done((&sl[0..], 4), 10));
  }

  named!(ch<(&[u8],usize),(u8,u8)>,
    chain!(
      tag_bits!(u8, 3, 0b101) ~
      x: take_bits!(u8, 4)    ~
      y: take_bits!(u8, 5)    ,
      || { (x,y) }
    )
  );

  #[test]
  fn chain_bits() {
    let input = vec![0b10101010, 0b11110000, 0b00110011];
    let sl    = &input[..];
    assert_eq!(ch((&input[..],0)), IResult::Done((&sl[1..], 4), (5,15)));
    assert_eq!(ch((&input[..],4)), IResult::Done((&sl[2..], 0), (7,16)));
    assert_eq!(ch((&input[..1],0)), IResult::Incomplete(Needed::Size(12)));
  }

  named!(ch_bytes<(u8,u8)>, bits!(ch));
  #[test]
  fn bits_to_bytes() {
    let input = vec![0b10101010, 0b11110000, 0b00110011];
    assert_eq!(ch_bytes(&input[..]), IResult::Done(&input[2..], (5,15)));
    assert_eq!(ch_bytes(&input[..1]), IResult::Incomplete(Needed::Size(2)));
    assert_eq!(ch_bytes(&input[1..]), IResult::Error(Err::Position(ErrorKind::TagBits, &input[1..])));
  }
}
