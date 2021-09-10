//! Parsers recognizing numbers

pub mod complete;
pub mod streaming;

/// Configurable endianness
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Endianness {
  /// Big endian
  Big,
  /// Little endian
  Little,
  /// Will match the host's endianness
  Native,
}

/// Case-insensitive comparison of digits. Only works if `y` is only ASCII letters.
#[inline]
fn case_insensitive_cmp(x: &[u8], y: &[u8]) -> bool {
    let d = (x.iter().zip(y.iter())).fold(0, |d, (xi, yi)| d | xi ^ yi);
    // This uses the trick that 'a' - 'A' == 0x20, and this is true
    // for all characters, so as long as `yi` is a valid ASCII letter,
    // `xi ^ yi` can only be 0 or 0x20.
    d == 0 || d == 0x20
}
