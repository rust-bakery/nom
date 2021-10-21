use core::ops::{Bound, RangeBounds};

/// Abstractions for range-like types.
/// Mostly a copy of [RangeBounds](https://doc.rust-lang.org/std/ops/trait.RangeBounds.html
pub trait NomRangeBounds<T: ?Sized> {
  /// `true` if `item` is contained in the range.
  fn contains<Item>(&self, item: &Item) -> bool
  where
    T: PartialOrd<Item>,
    Item: ?Sized + PartialOrd<T>,
  {
    RangeBounds::contains(&NomRangeBounds::bounds(self), item)
  }

  /// Start index bound.
  ///
  /// Returns the start value as a `Bound`.
  fn start_bound(&self) -> Bound<&T>;

  /// End index bound.
  ///
  /// Returns the end value as a `Bound`.
  fn end_bound(&self) -> Bound<&T>;

  /// Shortcut for calling both start_bound and end_bound
  fn bounds(&self) -> (Bound<&T>, Bound<&T>) {
    (
      NomRangeBounds::start_bound(self),
      NomRangeBounds::end_bound(self),
    )
  }
}

// TODO maybe one day [#31844](https://github.com/rust-lang/rust/issues/31844)
// impl<Range, Item> NomRange<Item> for Range
// where
//   Range: RangeBounds<Item>,
// {
//   fn start_bound(&self) -> Bound<&Item> {
//     self.start_bound()
//   }
//
//   fn end_bound(&self) -> Bound<&Item> {
//     self.end_bound()
//   }
// }

macro_rules! impl_nom_range {
  ($range:ty | $t:ty) => {
    impl $crate::traits::NomRangeBounds<$t> for $range {
      fn start_bound(&self) -> core::ops::Bound<&$t> {
        core::ops::RangeBounds::start_bound(self)
      }

      fn end_bound(&self) -> core::ops::Bound<&$t> {
        core::ops::RangeBounds::end_bound(self)
      }
    }
  };
}

macro_rules! impl_nom_ranges {
    ($($range:ty),*) => {
        $(impl_nom_range!{$range | usize})*
    }
  }

impl_nom_ranges!(
  (Bound<usize>, Bound<usize>),
  (Bound<&usize>, Bound<&usize>),
  core::ops::Range<usize>,
  core::ops::Range<&usize>,
  core::ops::RangeFrom<usize>,
  core::ops::RangeFrom<&usize>,
  core::ops::RangeFull,
  core::ops::RangeInclusive<usize>,
  core::ops::RangeInclusive<&usize>,
  core::ops::RangeTo<usize>,
  core::ops::RangeTo<&usize>,
  core::ops::RangeToInclusive<usize>,
  core::ops::RangeToInclusive<&usize>
);

impl NomRangeBounds<usize> for usize {
  fn start_bound(&self) -> Bound<&usize> {
    Bound::Included(self)
  }

  fn end_bound(&self) -> Bound<&usize> {
    Bound::Included(self)
  }
}

#[test]
fn nom_range() {
  use crate::traits::NomRangeBounds;
  use core::ops::Bound;

  assert_eq!(5.bounds(), (5..=5).bounds());
  assert_eq!((..).bounds(), (Bound::Unbounded, Bound::Unbounded));
}
