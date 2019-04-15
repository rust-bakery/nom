use internal::*;
use error::ParseError;
use traits::{AsChar, InputIter, InputLength, InputTakeAtPosition};
use traits::{need_more, need_more_err, AtEof, ParseTo};
use lib::std::ops::{Range, RangeFrom, RangeTo};
use traits::{Compare, CompareResult, Offset, Slice};
use error::ErrorKind;
use lib::std::mem::transmute;
use character::streaming::digit;

pub mod streaming;
pub mod complete;

/// Configurable endianness
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Endianness {
  Big,
  Little,
}

/// if the parameter is nom::Endianness::Big, parse a big endian u16 integer,
/// otherwise a little endian u16 integer
#[macro_export(local_inner_macros)]
macro_rules! u16 ( ($i:expr, $e:expr) => ( {if $crate::number::Endianness::Big == $e { $crate::number::streaming::be_u16($i) } else { $crate::number::streaming::le_u16($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian u32 integer,
/// otherwise a little endian u32 integer
#[macro_export(local_inner_macros)]
macro_rules! u32 ( ($i:expr, $e:expr) => ( {if $crate::number::Endianness::Big == $e { $crate::number::streaming::be_u32($i) } else { $crate::number::streaming::le_u32($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian u64 integer,
/// otherwise a little endian u64 integer
#[macro_export(local_inner_macros)]
macro_rules! u64 ( ($i:expr, $e:expr) => ( {if $crate::number::Endianness::Big == $e { $crate::number::streaming::be_u64($i) } else { $crate::number::streaming::le_u64($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian u128 integer,
/// otherwise a little endian u128 integer
#[macro_export(local_inner_macros)]
#[cfg(stable_i128)]
macro_rules! u128 ( ($i:expr, $e:expr) => ( {if $crate::number::Endianness::Big == $e { $crate::number::streaming::be_u128($i) } else { $crate::number::streaming::le_u128($i) } } ););

/// if the parameter is nom::Endianness::Big, parse a big endian i16 integer,
/// otherwise a little endian i16 integer
#[macro_export(local_inner_macros)]
macro_rules! i16 ( ($i:expr, $e:expr) => ( {if $crate::number::Endianness::Big == $e { $crate::number::streaming::be_i16($i) } else { $crate::number::streaming::le_i16($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian i32 integer,
/// otherwise a little endian i32 integer
#[macro_export(local_inner_macros)]
macro_rules! i32 ( ($i:expr, $e:expr) => ( {if $crate::number::Endianness::Big == $e { $crate::number::streaming::be_i32($i) } else { $crate::number::streaming::le_i32($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian i64 integer,
/// otherwise a little endian i64 integer
#[macro_export(local_inner_macros)]
macro_rules! i64 ( ($i:expr, $e:expr) => ( {if $crate::number::Endianness::Big == $e { $crate::number::streaming::be_i64($i) } else { $crate::number::streaming::le_i64($i) } } ););
/// if the parameter is nom::Endianness::Big, parse a big endian i64 integer,
/// otherwise a little endian i64 integer
#[macro_export(local_inner_macros)]
#[cfg(stable_i128)]
macro_rules! i128 ( ($i:expr, $e:expr) => ( {if $crate::number::Endianness::Big == $e { $crate::number::streaming::be_i128($i) } else { $crate::number::streaming::le_i128($i) } } ););

/// Recognizes a hex-encoded integer
#[inline]
pub fn hex_u32<'a, E: ParseError<&'a [u8]>>(input: &'a[u8]) -> IResult<&'a[u8], u32, E> {
  match is_a!(input, &b"0123456789abcdefABCDEF"[..]) {
    Err(e) => Err(e),
    Ok((i, o)) => {
      // Do not parse more than 8 characters for a u32
      let (parsed, remaining) = if o.len() <= 8 {
        (o, i)
      } else {
        (&input[..8], &input[8..])
      };

      let res = parsed
        .iter()
        .rev()
        .enumerate()
        .map(|(k, &v)| {
          let digit = v as char;
          digit.to_digit(16).unwrap_or(0) << (k * 4)
        })
        .sum();

      Ok((remaining, res))
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Err, IResult, Needed};
  use types::{CompleteByteSlice, CompleteStr};

  macro_rules! assert_parse(
    ($left: expr, $right: expr) => {
      let res: $crate::IResult<_, _, (_, ErrorKind)> = $left;
      assert_eq!(res, $right);
    };
  );

  #[test]
  fn hex_u32_tests() {
    assert_parse!(
      hex_u32(&b";"[..]),
      Err(Err::Error(error_position!(&b";"[..], ErrorKind::IsA)))
    );
    assert_parse!(hex_u32(&b"ff;"[..]), Ok((&b";"[..], 255)));
    assert_parse!(hex_u32(&b"1be2;"[..]), Ok((&b";"[..], 7138)));
    assert_parse!(hex_u32(&b"c5a31be2;"[..]), Ok((&b";"[..], 3_315_801_058)));
    assert_parse!(hex_u32(&b"C5A31be2;"[..]), Ok((&b";"[..], 3_315_801_058)));
    assert_parse!(hex_u32(&b"00c5a31be2;"[..]), Ok((&b"e2;"[..], 12_952_347)));
    assert_parse!(
      hex_u32(&b"c5a31be201;"[..]),
      Ok((&b"01;"[..], 3_315_801_058))
    );
    assert_parse!(hex_u32(&b"ffffffff;"[..]), Ok((&b";"[..], 4_294_967_295)));
    assert_parse!(hex_u32(&b"0x1be2;"[..]), Ok((&b"x1be2;"[..], 0)));
  }

  #[test]
  fn configurable_endianness() {
    named!(be_tst16<u16>, u16!(Endianness::Big));
    named!(le_tst16<u16>, u16!(Endianness::Little));
    assert_eq!(be_tst16(&[0x80, 0x00]), Ok((&b""[..], 32_768_u16)));
    assert_eq!(le_tst16(&[0x80, 0x00]), Ok((&b""[..], 128_u16)));

    named!(be_tst32<u32>, u32!(Endianness::Big));
    named!(le_tst32<u32>, u32!(Endianness::Little));
    assert_eq!(
      be_tst32(&[0x12, 0x00, 0x60, 0x00]),
      Ok((&b""[..], 302_014_464_u32))
    );
    assert_eq!(
      le_tst32(&[0x12, 0x00, 0x60, 0x00]),
      Ok((&b""[..], 6_291_474_u32))
    );

    named!(be_tst64<u64>, u64!(Endianness::Big));
    named!(le_tst64<u64>, u64!(Endianness::Little));
    assert_eq!(
      be_tst64(&[0x12, 0x00, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 1_297_142_246_100_992_000_u64))
    );
    assert_eq!(
      le_tst64(&[0x12, 0x00, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 36_028_874_334_666_770_u64))
    );

    named!(be_tsti16<i16>, i16!(Endianness::Big));
    named!(le_tsti16<i16>, i16!(Endianness::Little));
    assert_eq!(be_tsti16(&[0x00, 0x80]), Ok((&b""[..], 128_i16)));
    assert_eq!(le_tsti16(&[0x00, 0x80]), Ok((&b""[..], -32_768_i16)));

    named!(be_tsti32<i32>, i32!(Endianness::Big));
    named!(le_tsti32<i32>, i32!(Endianness::Little));
    assert_eq!(
      be_tsti32(&[0x00, 0x12, 0x60, 0x00]),
      Ok((&b""[..], 1_204_224_i32))
    );
    assert_eq!(
      le_tsti32(&[0x00, 0x12, 0x60, 0x00]),
      Ok((&b""[..], 6_296_064_i32))
    );

    named!(be_tsti64<i64>, i64!(Endianness::Big));
    named!(le_tsti64<i64>, i64!(Endianness::Little));
    assert_eq!(
      be_tsti64(&[0x00, 0xFF, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 71_881_672_479_506_432_i64))
    );
    assert_eq!(
      le_tsti64(&[0x00, 0xFF, 0x60, 0x00, 0x12, 0x00, 0x80, 0x00]),
      Ok((&b""[..], 36_028_874_334_732_032_i64))
    );
  }

  //FIXME
  /*
  #[test]
  #[cfg(feature = "std")]
  fn manual_configurable_endianness_test() {
    let x = 1;
    let int_parse: Box<Fn(&[u8]) -> IResult<&[u8], u16, (&[u8], ErrorKind)>> = if x == 2 {
      Box::new(be_u16)
    } else {
      Box::new(le_u16)
    };
    println!("{:?}", int_parse(&b"3"[..]));
    assert_eq!(int_parse(&[0x80, 0x00]), Ok((&b""[..], 128_u16)));
  }
  */
}
