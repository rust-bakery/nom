#![cfg_attr(all(feature = "complete", feature = "streaming"), doc = include_str!("readme.md"))]
#![cfg_attr(not(all(feature = "complete", feature = "streaming")), doc = "todo")]

#![cfg_attr(not(feature = "std"), no_std)]

#![cfg_attr(feature = "cargo-clippy", allow(clippy::doc_markdown))]
#![cfg_attr(nightly, feature(test))]
#![cfg_attr(feature = "docsrs", feature(doc_cfg))]
#![cfg_attr(feature = "docsrs", feature(extended_key_value_attributes))]
#![deny(missing_docs)]

#[cfg_attr(nightly, warn(rustdoc::missing_doc_code_examples))]
#[cfg(feature = "alloc")]
#[macro_use]
extern crate alloc;
#[cfg(doctest)]
extern crate doc_comment;

#[cfg(nightly)]
extern crate test;

#[cfg(doctest)]
#[cfg(all(feature = "complete", feature = "streaming"))]
doc_comment::doctest!("../README.md");

/// Lib module to re-export everything needed from `std` or `core`/`alloc`. This is how `serde` does
/// it, albeit there it is not public.
#[cfg_attr(nightly, allow(rustdoc::missing_doc_code_examples))]
pub mod lib {
  /// `std` facade allowing `std`/`core` to be interchangeable. Reexports `alloc` crate optionally,
  /// as well as `core` or `std`
  #[cfg(not(feature = "std"))]
  #[cfg_attr(nightly, allow(rustdoc::missing_doc_code_examples))]
  /// internal std exports for no_std compatibility
  pub mod std {
    #[doc(hidden)]
    #[cfg(not(feature = "alloc"))]
    pub use core::borrow;

    #[cfg(feature = "alloc")]
    #[doc(hidden)]
    pub use alloc::{borrow, boxed, string, vec};

    #[doc(hidden)]
    pub use core::{cmp, convert, fmt, iter, mem, ops, option, result, slice, str};

    /// internal reproduction of std prelude
    #[doc(hidden)]
    pub mod prelude {
      pub use core::prelude as v1;
    }
  }

  #[cfg(feature = "std")]
  #[cfg_attr(nightly, allow(rustdoc::missing_doc_code_examples))]
  /// internal std exports for no_std compatibility
  pub mod std {
    #[doc(hidden)]
    pub use std::{
      alloc, borrow, boxed, cmp, collections, convert, fmt, hash, iter, mem, ops, option, result,
      slice, str, string, vec,
    };

    /// internal reproduction of std prelude
    #[doc(hidden)]
    pub mod prelude {
      pub use std::prelude as v1;
    }
  }
}

pub use self::bits::*;
pub use self::internal::*;
pub use self::traits::*;

pub use self::str::*;

#[macro_use]
pub mod error;

pub mod combinator;
mod internal;
mod traits;
#[macro_use]
pub mod branch;
pub mod multi;
pub mod sequence;

pub mod bits;
pub mod bytes;

pub mod character;

mod str;

pub mod number;

#[cfg(feature = "docsrs")]
#[cfg_attr(feature = "docsrs", cfg_attr(feature = "docsrs", doc = include_str!("../doc/nom_recipes.md")))]
pub mod recipes {}
