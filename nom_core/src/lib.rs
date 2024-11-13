
//! Core nom implementation
//!
//! This is inteded to be re-exported by the `nom` crate itself. This allows
//! other crates that extend `nom`, such as `nom-supreme`, to also be re-exported
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "docsrs", feature(doc_cfg))]
#![allow(clippy::doc_markdown)]
#![deny(missing_docs)]
#[cfg(feature = "alloc")]
#[macro_use]
extern crate alloc;

/// Lib module to re-export everything needed from `std` or `core`/`alloc`. This is how `serde` does
/// it, albeit there it is not public.
pub mod lib {
  /// `std` facade allowing `std`/`core` to be interchangeable. Reexports `alloc` crate optionally,
  /// as well as `core` or `std`
  #[cfg(not(feature = "std"))]
  /// internal std exports for no_std compatibility
  pub mod std {
    #[doc(hidden)]
    #[cfg(not(feature = "alloc"))]
    pub use core::borrow;

    #[cfg(feature = "alloc")]
    #[doc(hidden)]
    pub use alloc::{borrow, boxed, string, vec};

    #[doc(hidden)]
    pub use core::{cmp, convert, fmt, iter, mem, num, ops, option, result, slice, str};

    /// internal reproduction of std prelude
    #[doc(hidden)]
    pub mod prelude {
      pub use core::prelude as v1;
    }
  }

  #[cfg(feature = "std")]
  /// internal std exports for no_std compatibility
  pub mod std {
    #[doc(hidden)]
    pub use std::{
      alloc, borrow, boxed, cmp, collections, convert, fmt, hash, iter, mem, num, ops, option,
      result, slice, str, string, vec,
    };

    /// internal reproduction of std prelude
    #[doc(hidden)]
    pub mod prelude {
      pub use std::prelude as v1;
    }
  }
}

pub use self::internal::*;
pub use self::traits::*;

#[macro_use]
mod macros;
#[macro_use]
pub mod error;

pub mod branch;
pub mod combinator;
mod internal;
pub mod multi;
pub mod sequence;
mod traits;

pub mod bits;
pub mod bytes;

pub mod character;

mod str;

pub mod number;

