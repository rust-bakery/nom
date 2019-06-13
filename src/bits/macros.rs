/// Transforms its byte slice input into a bit stream for the underlying parser. This allows the
/// given bit stream parser to work on a byte slice input.
///
/// Signature:
/// `bits!( parser ) => ( &[u8], (&[u8], usize) -> IResult<(&[u8], usize), T> ) -> IResult<&[u8], T>`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!( take_4_bits<u8>, bits!( take_bits!( 4 ) ) );
///
///  let input = vec![0xAB, 0xCD, 0xEF, 0x12];
///  let sl    = &input[..];
///
///  assert_eq!(take_4_bits( sl ), Ok( (&sl[1..], 0xA) ));
/// # }
#[macro_export(local_inner_macros)]
macro_rules! bits (
  ($i:expr, $submac:ident!( $($args:tt)* )) => ({
    $crate::bits::bitsc($i, move |i| { $submac!(i, $($args)*) })
  });
  ($i:expr, $f:expr) => (
    bits!($i, call!($f))
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
/// # use nom::combinator::rest;
/// # fn main() {
///  named!( parse<(u8, u8, &[u8])>,  bits!( tuple!(
///    take_bits!(4),
///    take_bits!(8),
///    bytes!(rest)
/// )));
///
///  let input = &[0xde, 0xad, 0xbe, 0xaf];
///
///  assert_eq!(parse( input ), Ok(( &[][..], (0xd, 0xea, &[0xbe, 0xaf][..]) )));
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! bytes (
  ($i:expr, $submac:ident!( $($args:tt)* )) => ({
    $crate::bits::bytesc($i, move |i| { $submac!(i, $($args)*) })
  });
  ($i:expr, $f:expr) => (
    bytes!($i, call!($f))
  );
);

/// Consumes the specified number of bits and returns them as the specified type.
///
/// Signature:
/// `take_bits!(count) => ( (&[T], usize), usize) -> IResult<(&[T], usize), U>`
///
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!( take_pair<(u8, u8)>, bits!( pair!( take_bits!(4), take_bits!(4) ) ) );
///
///  let input = vec![0xAB, 0xCD, 0xEF];
///  let sl    = &input[..];
///
///  assert_eq!(take_pair( sl ),       Ok((&sl[1..], (0xA, 0xB))) );
///  assert_eq!(take_pair( &sl[1..] ), Ok((&sl[2..], (0xC, 0xD))) );
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! take_bits (
  ($i:expr, $count:expr) => ({
    $crate::bits::streaming::take_bits::<_, _, usize, _>($count)($i)
  });
);

/// Matches the given bit pattern.
///
/// Signature:
/// `tag_bits!(count, pattern) => ((&[T], usize), usize) -> IResult<(&[T], usize), U>`
///
/// The caller must specify the number of bits to consume. The matched value is included in the
/// result on success.
///
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///  named!( take_a<u8>, bits!( tag_bits!(4, 0xA) ) );
///
///  let input = vec![0xAB, 0xCD, 0xEF];
///  let sl    = &input[..];
///
///  assert_eq!(take_a( sl ),       Ok((&sl[1..], 0xA)) );
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! tag_bits (
  ($i:expr, $count:expr, $p:expr) => ({
    $crate::bits::streaming::tag_bits::<_, _, usize, _>($count, $p)($i)
  })
);

#[cfg(test)]
mod tests {
  use crate::combinator::rest;
  use crate::error::ErrorKind;
  use crate::internal::{Err, IResult, Needed};
  use crate::lib::std::ops::{AddAssign, Shl, Shr};

  fn take(input: (&[u8], usize), take: usize) -> IResult<(&[u8], usize), usize> {
    take_bits!(input, take)
  }

  #[test]
  fn take_bits() {
    let input = [0b10_10_10_10, 0b11_11_00_00, 0b00_11_00_11];
    let sl = &input[..];

    assert_eq!(take((sl, 0), 0), Ok(((sl, 0), 0)));
    assert_eq!(take((sl, 0), 8), Ok(((&sl[1..], 0), 170)));
    assert_eq!(take((sl, 0), 3), Ok(((&sl[0..], 3), 5)));
    assert_eq!(take((sl, 0), 6), Ok(((&sl[0..], 6), 42)));
    assert_eq!(take((sl, 1), 1), Ok(((&sl[0..], 2), 0)));
    assert_eq!(take((sl, 1), 2), Ok(((&sl[0..], 3), 1)));
    assert_eq!(take((sl, 1), 3), Ok(((&sl[0..], 4), 2)));
    assert_eq!(take((sl, 6), 3), Ok(((&sl[1..], 1), 5)));
    assert_eq!(take((sl, 0), 10), Ok(((&sl[1..], 2), 683)));
    assert_eq!(take((sl, 0), 8), Ok(((&sl[1..], 0), 170)));
    assert_eq!(take((sl, 6), 10), Ok(((&sl[2..], 0), 752)));
    assert_eq!(take((sl, 6), 11), Ok(((&sl[2..], 1), 1504)));
    assert_eq!(take((sl, 0), 20), Ok(((&sl[2..], 4), 700_163)));
    assert_eq!(take((sl, 4), 20), Ok(((&sl[3..], 0), 716_851)));
    assert_eq!(take((sl, 4), 22), Err(Err::Incomplete(Needed::Size(22))));
  }

  fn tag_parser(input: (&[u8], usize), count: usize, tag: u8) -> IResult<(&[u8], usize), u8> {
    tag_bits!(input, count, tag)
  }

  #[test]
  fn tag_bits() {
    let input = [0b10_10_10_10, 0b11_11_00_00, 0b00_11_00_11];

    assert_eq!(tag_parser((&input[..], 0), 3, 0b101), Ok(((&input[0..], 3), 5)));
    assert_eq!(tag_parser((&input[..], 0), 4, 0b1010), Ok(((&input[0..], 4), 10)));
  }

  fn ch(input: (&[u8], usize)) -> IResult<(&[u8], usize), (u8, u8)> {
    do_parse!(
      input,
      tag_bits!(3usize, 0b101) >> x: take_bits!(4usize) >> y: take_bits!(5usize) >> (x, y)
    )
  }

  #[test]
  fn chain_bits() {
    let input = [0b10_10_10_10, 0b11_11_00_00, 0b00_11_00_11];
    let sl = &input[..];
    assert_eq!(ch((&sl[..], 0)), Ok(((&sl[1..], 4), (5, 15))));
    assert_eq!(ch((&sl[..], 4)), Ok(((&sl[2..], 0), (7, 16))));
    assert_eq!(ch((&sl[..1], 0)), Err(Err::Incomplete(Needed::Size(5))));
  }

  fn ch_bytes(input: &[u8]) -> IResult<&[u8], (u8, u8), ((&[u8], usize), ErrorKind)> {
    bits!(input, ch)
  }

  #[test]
  fn bits_to_bytes() {
    let input = [0b10_10_10_10, 0b11_11_00_00, 0b00_11_00_11];
    assert_eq!(ch_bytes(&input[..]), Ok((&input[2..], (5, 15))));
    assert_eq!(ch_bytes(&input[..1]), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(ch_bytes(&input[1..]), Err(Err::Error(((&input[1..], 3), ErrorKind::TagBits))));
  }

  named!(bits_bytes_bs, bits!(bytes!(rest)));
  #[test]
  fn bits_bytes() {
    let input = [0b10_10_10_10];
    assert_eq!(bits_bytes_bs(&input[..]), Ok((&[][..], &[0b10_10_10_10][..])));
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

  fn take_uint(input: (&[u8], usize), take: usize) -> IResult<(&[u8], usize), FakeUint, (&[u8], ErrorKind)> {
    take_bits!(input, take)
  }

  #[test]
  fn non_primitive_type() {
    let input = [0b10_10_10_10, 0b11_11_00_00, 0b00_11_00_11];
    let sl = &input[..];

    assert_eq!(take_uint((sl, 0), 20), Ok(((&sl[2..], 4), FakeUint(700_163))));
    assert_eq!(take_uint((sl, 4), 20), Ok(((&sl[3..], 0), FakeUint(716_851))));
    assert_eq!(take_uint((sl, 4), 22), Err(Err::Incomplete(Needed::Size(22))));
  }
}
