use core::ops::ControlFlow;
use core::ops::{Bound, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

/// The value when next return to break
pub enum Break {
  /// Tell you can loop forever without call next anymore
  Infinite,
  /// We reach the upper bound
  Finish,
}

/// This allow nom conbinator to be use with Range like `5..10`
pub trait NomBounds {
  /// next check if the current iteration is in bounds
  /// this will mostly check for upper bound
  /// if no check is needed anymore the return will be Break and Break value will
  /// tell if it was an Out of Bound error or just that we reach the min bound and
  /// we don't have any upper bound
  fn next(&self) -> ControlFlow<Break, ()>;

  /// todo
  fn advance(&mut self);

  /// this need to be call at the end to check if the min number of iteration have been reach
  /// no need to call this when next return a Break::Infinite
  fn is_min_reach(self) -> bool;

  /// todo
  fn is_broken(&self) -> bool;
}

/// This trait help type inference of Rust to allow to transparently use Rust range
pub trait IntoNomBounds {
  /// todo
  type NomBounds: NomBounds;

  /// todo
  fn into_nom_bounds(self) -> Self::NomBounds;
}

/// todo
#[derive(Clone, Debug)]
pub struct NomBoundsRange {
  range: Range<usize>,
  i: usize,
}

impl From<Range<usize>> for NomBoundsRange {
  fn from(range: Range<usize>) -> Self {
    Self { range, i: 0 }
  }
}

impl IntoNomBounds for Range<usize> {
  type NomBounds = NomBoundsRange;

  fn into_nom_bounds(self) -> Self::NomBounds {
    self.into()
  }
}

impl NomBounds for NomBoundsRange {
  fn next(&self) -> ControlFlow<Break> {
    if self.i < self.range.end {
      ControlFlow::Continue(())
    } else {
      ControlFlow::Break(Break::Finish)
    }
  }

  fn advance(&mut self) {
    self.i += 1;
  }

  fn is_min_reach(self) -> bool {
    self.i >= self.range.start
  }

  fn is_broken(&self) -> bool {
    self.range.start > self.range.end
  }
}

/// todo
#[derive(Clone, Debug)]
pub struct NomBoundsRangeInclusive {
  range: RangeInclusive<usize>,
  i: usize,
  is_exhausted: bool,
}

impl From<RangeInclusive<usize>> for NomBoundsRangeInclusive {
  fn from(range: RangeInclusive<usize>) -> Self {
    Self {
      range,
      i: 0,
      is_exhausted: false,
    }
  }
}

impl IntoNomBounds for RangeInclusive<usize> {
  type NomBounds = NomBoundsRangeInclusive;

  fn into_nom_bounds(self) -> Self::NomBounds {
    self.into()
  }
}

impl From<usize> for NomBoundsRangeInclusive {
  fn from(n: usize) -> Self {
    Self {
      range: n..=n,
      i: 0,
      is_exhausted: false,
    }
  }
}

impl IntoNomBounds for usize {
  type NomBounds = NomBoundsRangeInclusive;

  fn into_nom_bounds(self) -> Self::NomBounds {
    self.into()
  }
}

impl NomBounds for NomBoundsRangeInclusive {
  fn next(&self) -> ControlFlow<Break> {
    if self.i < *self.range.end() {
      ControlFlow::Continue(())
    } else if self.i == *self.range.end() && !self.is_exhausted {
      ControlFlow::Continue(())
    } else {
      ControlFlow::Break(Break::Finish)
    }
  }

  fn advance(&mut self) {
    if self.i != *self.range.end() {
      self.i += 1;
    } else {
      self.is_exhausted = true;
    }
  }

  fn is_min_reach(self) -> bool {
    self.i >= *self.range.start()
  }

  fn is_broken(&self) -> bool {
    self.range.start() > self.range.end()
      && (*self.range.end() == usize::MAX || *self.range.start() > *self.range.end() + 1)
  }
}

/// todo
#[derive(Clone, Debug)]
pub struct NomBoundsRangeFrom {
  range: RangeFrom<usize>,
  i: usize,
}

impl From<RangeFrom<usize>> for NomBoundsRangeFrom {
  fn from(range: RangeFrom<usize>) -> Self {
    Self { range, i: 0 }
  }
}

impl IntoNomBounds for RangeFrom<usize> {
  type NomBounds = NomBoundsRangeFrom;

  fn into_nom_bounds(self) -> Self::NomBounds {
    self.into()
  }
}

impl NomBounds for NomBoundsRangeFrom {
  fn next(&self) -> ControlFlow<Break> {
    if self.i < self.range.start {
      ControlFlow::Continue(())
    } else {
      ControlFlow::Break(Break::Infinite)
    }
  }

  fn advance(&mut self) {
    self.i += 1;
  }

  fn is_min_reach(self) -> bool {
    self.i >= self.range.start
  }

  fn is_broken(&self) -> bool {
    false
  }
}

/// todo
#[derive(Clone, Debug)]
pub struct NomBoundsRangeTo {
  range: RangeTo<usize>,
  i: usize,
}

impl From<RangeTo<usize>> for NomBoundsRangeTo {
  fn from(range: RangeTo<usize>) -> Self {
    Self { range, i: 0 }
  }
}

impl IntoNomBounds for RangeTo<usize> {
  type NomBounds = NomBoundsRangeTo;

  fn into_nom_bounds(self) -> Self::NomBounds {
    self.into()
  }
}

impl NomBounds for NomBoundsRangeTo {
  fn next(&self) -> ControlFlow<Break> {
    if self.i < self.range.end {
      ControlFlow::Continue(())
    } else {
      ControlFlow::Break(Break::Finish)
    }
  }

  fn advance(&mut self) {
    self.i += 1;
  }

  fn is_min_reach(self) -> bool {
    true
  }

  fn is_broken(&self) -> bool {
    false
  }
}

/// todo
#[derive(Clone, Debug)]
pub struct NomBoundsRangeToInclusive {
  range: RangeToInclusive<usize>,
  i: usize,
  is_exhausted: bool,
}

impl From<RangeToInclusive<usize>> for NomBoundsRangeToInclusive {
  fn from(range: RangeToInclusive<usize>) -> Self {
    Self {
      range,
      i: 0,
      is_exhausted: false,
    }
  }
}

impl IntoNomBounds for RangeToInclusive<usize> {
  type NomBounds = NomBoundsRangeToInclusive;

  fn into_nom_bounds(self) -> Self::NomBounds {
    self.into()
  }
}

impl NomBounds for NomBoundsRangeToInclusive {
  fn next(&self) -> ControlFlow<Break> {
    if self.i < self.range.end {
      ControlFlow::Continue(())
    } else if self.i == self.range.end && !self.is_exhausted {
      ControlFlow::Continue(())
    } else {
      ControlFlow::Break(Break::Finish)
    }
  }

  fn advance(&mut self) {
    if self.i != self.range.end {
      self.i += 1;
    } else {
      self.is_exhausted = true;
    }
  }

  fn is_min_reach(self) -> bool {
    true
  }

  fn is_broken(&self) -> bool {
    false
  }
}

impl IntoNomBounds for RangeFull {
  type NomBounds = RangeFull;

  fn into_nom_bounds(self) -> Self::NomBounds {
    self
  }
}

impl NomBounds for RangeFull {
  fn next(&self) -> ControlFlow<Break> {
    ControlFlow::Break(Break::Infinite)
  }

  fn advance(&mut self) {}

  fn is_min_reach(self) -> bool {
    true
  }

  fn is_broken(&self) -> bool {
    false
  }
}

/// todo
#[derive(Clone, Debug)]
pub struct NomBoundsBounds {
  i: usize,
  start: Bound<usize>,
  end: Bound<usize>,
  is_exhausted: bool,
}

impl From<(Bound<usize>, Bound<usize>)> for NomBoundsBounds {
  fn from((start, end): (Bound<usize>, Bound<usize>)) -> Self {
    Self {
      i: 0,
      start,
      end,
      is_exhausted: false,
    }
  }
}

impl NomBounds for NomBoundsBounds {
  fn next(&self) -> ControlFlow<Break> {
    match self.end {
      Bound::Included(end) => {
        if self.i < end {
          ControlFlow::Continue(())
        } else if self.i == end && !self.is_exhausted {
          ControlFlow::Continue(())
        } else {
          ControlFlow::Break(Break::Finish)
        }
      }
      Bound::Excluded(end) => {
        if self.i < end {
          ControlFlow::Continue(())
        } else {
          ControlFlow::Break(Break::Finish)
        }
      }
      Bound::Unbounded => match self.start {
        Bound::Included(start) => {
          if self.i < start {
            ControlFlow::Continue(())
          } else {
            ControlFlow::Break(Break::Infinite)
          }
        }
        Bound::Excluded(start) => {
          if self.i < start {
            ControlFlow::Continue(())
          } else if self.i == start && !self.is_exhausted {
            ControlFlow::Continue(())
          } else {
            ControlFlow::Break(Break::Infinite)
          }
        }
        Bound::Unbounded => ControlFlow::Break(Break::Infinite),
      },
    }
  }

  fn advance(&mut self) {
    match self.end {
      Bound::Included(end) => {
        if self.i != end {
          self.i += 1;
        } else {
          self.is_exhausted = true;
        }
      }
      Bound::Excluded(_) => self.i += 1,
      Bound::Unbounded => match self.start {
        Bound::Included(_) => self.i += 1,
        Bound::Excluded(start) => {
          if self.i != start {
            self.i += 1;
          } else {
            self.is_exhausted = true;
          }
        }
        Bound::Unbounded => {}
      },
    }
  }

  fn is_min_reach(self) -> bool {
    match self.start {
      Bound::Included(start) => self.i >= start,
      Bound::Excluded(start) => self.i > start,
      Bound::Unbounded => true,
    }
  }

  fn is_broken(&self) -> bool {
    match (self.start, self.end) {
      (Bound::Included(start), Bound::Included(end)) => {
        start > end && (end == usize::MAX || start > end + 1)
      }
      (Bound::Included(start), Bound::Excluded(end))
      | (Bound::Excluded(start), Bound::Included(end)) => start > end,
      (Bound::Excluded(start), Bound::Excluded(end)) => start >= end,
      (Bound::Excluded(_), Bound::Unbounded)
      | (Bound::Unbounded, Bound::Excluded(_))
      | (Bound::Included(_), Bound::Unbounded)
      | (Bound::Unbounded, Bound::Included(_))
      | (Bound::Unbounded, Bound::Unbounded) => false,
    }
  }
}
