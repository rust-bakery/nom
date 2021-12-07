//! Reexport the content of many modules, except `complete` and `streaming` modules
//! which have their own reexports as `prelude::complete` and `prelude::streaming`.

pub use crate::{
  bits::{complete as _, streaming as _, *},
  branch::*,
  character::{complete as _, streaming as _, *},
  combinator::{complete as _, *},
  multi::*,
  number::{complete as _, streaming as _, *},
  sequence::*,
  *,
};

/// Reexport all `complete` modules content but standard type names from `nom::number::complete`.
pub mod complete {
  pub use crate::{
    bits::complete::*,
    bytes::complete::*,
    character::complete::*,
    number::complete::{
      f32 as _, f64 as _, i128 as _, i16 as _, i32 as _, i64 as _, i8 as _, u128 as _, u16 as _,
      u32 as _, u64 as _, u8 as _, *,
    },
  };
}

/// Reexport all `streaming` modules content but standard type names from `nom::number::streaming`.
pub mod streaming {
  pub use crate::{
    bits::streaming::*,
    bytes::streaming::*,
    character::streaming::*,
    number::streaming::{
      f32 as _, f64 as _, i128 as _, i16 as _, i32 as _, i64 as _, i8 as _, u128 as _, u16 as _,
      u32 as _, u64 as _, u8 as _, *,
    },
  };
}
