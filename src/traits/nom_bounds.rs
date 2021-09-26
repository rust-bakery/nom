use core::ops::{
  Bound, ControlFlow, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};

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
  fn next(&mut self) -> ControlFlow<Break, usize>;

  /// this need to be call at the end to check if the min number of iteration have been reach
  /// no need to call this when next return a Break::Infinite
  fn is_min_reach(self, n: usize) -> bool;

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

impl<'a> IntoNomBounds for &'a Range<usize> {
  type NomBounds = NomBoundsRange;

  fn into_nom_bounds(self) -> Self::NomBounds {
    Self::NomBounds {
      range: self.clone(),
      i: 0,
    } // https://github.com/rust-lang/rust/issues/90190
  }
}

impl NomBounds for NomBoundsRange {
  fn next(&mut self) -> ControlFlow<Break, usize> {
    if self.i < self.range.end {
      ControlFlow::Continue(replace(self.i + 1, &mut self.i))
    } else {
      ControlFlow::Break(Break::Finish)
    }
  }

  fn is_min_reach(self, n: usize) -> bool {
    n >= self.range.start
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

impl<'a> IntoNomBounds for &'a RangeInclusive<usize> {
  type NomBounds = NomBoundsRangeInclusive;

  fn into_nom_bounds(self) -> Self::NomBounds {
    Self::NomBounds {
      range: self.clone(), // https://github.com/rust-lang/rust/issues/90190
      i: 0,
      is_exhausted: false,
    }
  }
}

impl<'a> IntoNomBounds for &'a usize {
  type NomBounds = NomBoundsRangeInclusive;

  fn into_nom_bounds(self) -> Self::NomBounds {
    Self::NomBounds {
      range: *self..=*self,
      i: 0,
      is_exhausted: false,
    }
  }
}

impl NomBounds for NomBoundsRangeInclusive {
  fn next(&mut self) -> ControlFlow<Break, usize> {
    if self.i < *self.range.end() {
      ControlFlow::Continue(replace(self.i + 1, &mut self.i))
    } else if self.i == *self.range.end() && !self.is_exhausted {
      self.is_exhausted = true;
      ControlFlow::Continue(self.i)
    } else {
      ControlFlow::Break(Break::Finish)
    }
  }

  fn is_min_reach(self, n: usize) -> bool {
    n >= *self.range.start()
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

impl<'a> IntoNomBounds for &'a RangeFrom<usize> {
  type NomBounds = NomBoundsRangeFrom;

  fn into_nom_bounds(self) -> Self::NomBounds {
    Self::NomBounds {
      range: self.clone(),
      i: 0,
    } // https://github.com/rust-lang/rust/issues/90190
  }
}

impl NomBounds for NomBoundsRangeFrom {
  fn next(&mut self) -> ControlFlow<Break, usize> {
    if self.i < self.range.start {
      ControlFlow::Continue(replace(self.i + 1, &mut self.i))
    } else {
      ControlFlow::Break(Break::Infinite)
    }
  }

  fn is_min_reach(self, n: usize) -> bool {
    n >= self.range.start
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

impl<'a> IntoNomBounds for &'a RangeTo<usize> {
  type NomBounds = NomBoundsRangeTo;

  fn into_nom_bounds(self) -> Self::NomBounds {
    Self::NomBounds { range: *self, i: 0 }
  }
}

impl NomBounds for NomBoundsRangeTo {
  fn next(&mut self) -> ControlFlow<Break, usize> {
    if self.i < self.range.end {
      ControlFlow::Continue(replace(self.i + 1, &mut self.i))
    } else {
      ControlFlow::Break(Break::Finish)
    }
  }

  fn is_min_reach(self, _n: usize) -> bool {
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

impl<'a> IntoNomBounds for &'a RangeToInclusive<usize> {
  type NomBounds = NomBoundsRangeToInclusive;

  fn into_nom_bounds(self) -> Self::NomBounds {
    Self::NomBounds {
      range: *self,
      i: 0,
      is_exhausted: false,
    }
  }
}

impl NomBounds for NomBoundsRangeToInclusive {
  fn next(&mut self) -> ControlFlow<Break, usize> {
    if self.i < self.range.end {
      ControlFlow::Continue(replace(self.i + 1, &mut self.i))
    } else if self.i == self.range.end && !self.is_exhausted {
      self.is_exhausted = true;
      ControlFlow::Continue(self.i)
    } else {
      ControlFlow::Break(Break::Finish)
    }
  }

  fn is_min_reach(self, _n: usize) -> bool {
    true
  }

  fn is_broken(&self) -> bool {
    false
  }
}

impl<'a> IntoNomBounds for &'a RangeFull {
  type NomBounds = RangeFull;

  fn into_nom_bounds(self) -> Self::NomBounds {
    *self
  }
}

impl NomBounds for RangeFull {
  fn next(&mut self) -> ControlFlow<Break, usize> {
    ControlFlow::Break(Break::Infinite)
  }

  fn is_min_reach(self, _n: usize) -> bool {
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

impl<'a> IntoNomBounds for &'a (Bound<usize>, Bound<usize>) {
  type NomBounds = NomBoundsBounds;

  fn into_nom_bounds(self) -> Self::NomBounds {
    let (start, end) = *self;
    Self::NomBounds {
      i: 0,
      start,
      end,
      is_exhausted: false,
    }
  }
}

impl NomBounds for NomBoundsBounds {
  fn next(&mut self) -> ControlFlow<Break, usize> {
    match self.end {
      Bound::Included(end) => {
        if self.i < end {
          ControlFlow::Continue(replace(self.i + 1, &mut self.i))
        } else if self.i == end && !self.is_exhausted {
          self.is_exhausted = true;
          ControlFlow::Continue(self.i)
        } else {
          ControlFlow::Break(Break::Finish)
        }
      }
      Bound::Excluded(end) => {
        if self.i < end {
          ControlFlow::Continue(replace(self.i + 1, &mut self.i))
        } else {
          ControlFlow::Break(Break::Finish)
        }
      }
      Bound::Unbounded => match self.start {
        Bound::Included(start) => {
          if self.i < start {
            ControlFlow::Continue(replace(self.i + 1, &mut self.i))
          } else {
            ControlFlow::Break(Break::Infinite)
          }
        }
        Bound::Excluded(start) => {
          if self.i < start {
            ControlFlow::Continue(replace(self.i + 1, &mut self.i))
          } else if self.i == start && !self.is_exhausted {
            self.is_exhausted = true;
            ControlFlow::Continue(self.i)
          } else {
            ControlFlow::Break(Break::Infinite)
          }
        }
        Bound::Unbounded => ControlFlow::Break(Break::Infinite),
      },
    }
  }

  fn is_min_reach(self, n: usize) -> bool {
    match self.start {
      Bound::Included(start) => n >= start,
      Bound::Excluded(start) => n > start,
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

fn replace<T>(src: T, dest: &mut T) -> T {
  core::mem::replace(dest, src)
}
