//! Parsers recognizing bytes streams

#[cfg(feature = "complete")]
pub mod complete;
#[cfg(feature = "streaming")]
pub mod streaming;
