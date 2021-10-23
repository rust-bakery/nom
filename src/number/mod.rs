//! Parsers recognizing numbers

#[cfg(feature = "complete")]
pub mod complete;
#[cfg(feature = "streaming")]
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
