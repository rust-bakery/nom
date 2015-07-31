//! Bit level parsers and combinators
//!
//!

#[macro_export]
macro_rules! bits (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    bit_impl!($i, $submac!($($args)*));
  );
  ($i:expr, $f:expr, $g:expr) => (
    bit_impl!($i, call!($f));
  );
);

#[macro_export]
macro_rules! bits_impl (
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    {
      match $submac!( ($i, 0usize), $($args)*) {
        $crate::IResult::Error(e)                            => $crate::IResult::Error(e),
        $crate::IResult::Incomplete($crate::Needed::Unknown) => $crate::IResult::Incomplete($crate::Needed::Unknown),
        $crate::IResult::Incomplete($crate::Needed::Size(i)) => $crate::IResult::Incomplete($crate::Needed::Size(i)),
        $crate::IResult::Done((i, bit_index), o)             => {
          let byte_index = if bit_index == 0 { 0 } else { 1 };

          $crate::IResult::Done(&i[byte_index..], o)
        }
      }
    }
  );
);

/// `take!(nb) => &[T] -> IResult<&[T], &[T]>`
/// generates a parser consuming the specified number of bytes
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  // Desmond parser
///  named!(take5, take!( 5 ) );
///
///  let a = b"abcdefgh";
///
///  assert_eq!(take5(&a[..]), Done(&b"fgh"[..], &b"abcde"[..]));
/// # }
/// ```
#[macro_export]
macro_rules! take_bits (
  (($i:expr, $bit_offset:expr), $t:ty, $count:expr) => (
    {
      use std::ops::Div;
      if $count == 0 {
        $crate::IResult::Done( ($i, $bit_offset) , 0)
      } else {
        let cnt = ($count as usize + $bit_offset).div(8);
        if $i.len() * 8 < $count as usize + $bit_offset {
          $crate::IResult::Incomplete($crate::Needed::Size(cnt+1))
        } else {
          let mut acc:$t            = 0;
          let mut offset: usize     = $bit_offset;
          let mut remaining: usize  = $count;
          let mut end_offset: usize = 0;

          for it in 0..cnt+1 {
            if remaining == 0 {
              break;
            }
            let val: $t = if offset == 0 {
              $i[it] as $t
            } else {
              (($i[it] << offset) as u8 >> offset) as $t
            };

            if remaining < 8 - offset {
              acc += val >> (8 - offset - remaining);
              end_offset = remaining + offset;
              break;
            } else {
              acc += val << remaining - (8 - offset);
              remaining -= 8 - offset;
              offset = 0;
            }
          }
          $crate::IResult::Done( (&$i[cnt..], end_offset) , acc)
        }
      }
    }
  );
);

#[cfg(test)]
mod tests {
  use internal::{IResult,Needed};

  #[test]
  fn take_bits() {
    let input = vec![0b10101010, 0b11110000, 0b00110011];
    let sl    = &input[..];

    assert_eq!(take_bits!( (sl, 0), u8,   0 ), IResult::Done((sl, 0), 0));
    assert_eq!(take_bits!( (sl, 0), u8,   8 ), IResult::Done((&sl[1..], 0), 170));
    assert_eq!(take_bits!( (sl, 0), u8,   3 ), IResult::Done((&sl[0..], 3), 5));
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
    assert_eq!(take_bits!( (sl, 4), u32, 22 ), IResult::Incomplete(Needed::Size(4)));
  }
}
