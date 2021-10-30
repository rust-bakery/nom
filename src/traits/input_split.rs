use crate::Needed;

/// Abstracts split_first
pub trait InputSplit: Sized {
  /// The current input type is a sequence of that `Item` type.
  ///
  /// Example: `u8` for `&[u8]` or `char` for `&str`
  type Item;

  /// Divides one input into two at an index.
  ///
  /// Return the head first then the tail `Ok((head, tail))`
  fn split_at(&self, mid: usize) -> Result<(Self, Self), Needed>;

  /// Returns the first and all the rest of the elements of the slice, or None if it is empty.
  fn split_first(&self) -> Option<(Self::Item, Self)>;

  /// Returns the last and all the rest of the elements of the slice, or None if it is empty.
  /// 
  /// The return order of the tuple is the opposite of split_first.
  /// It's reduce potencial mistake and match slice pattern matching
  fn split_last(&self) -> Option<(Self, Self::Item)>;
}

impl<'a> InputSplit for &'a str {
  type Item = char;

  fn split_at(&self, mid: usize) -> Result<(Self, Self), Needed> {
    if mid <= self.len() {
      Ok(str::split_at(self, mid))
    } else {
      Err(Needed::new(mid - self.len()))
    }
  }

  fn split_first(&self) -> Option<(Self::Item, Self)> {
    let mut chars = self.chars();
    chars.next().map(|c| (c, chars.as_str()))
  }

  fn split_last(&self) -> Option<(Self, Self::Item)> {
    let mut chars = self.chars();
    chars.next_back().map(|c| (chars.as_str(), c))
  }
}

impl<'a> InputSplit for &'a [u8] {
  type Item = u8;

  fn split_at(&self, mid: usize) -> Result<(Self, Self), Needed> {
    if mid <= self.len() {
      Ok(<[u8]>::split_at(self, mid))
    } else {
      Err(Needed::new(mid - self.len()))
    }
  }

  fn split_first(&self) -> Option<(Self::Item, Self)> {
    if let [first, tail @ ..] = *self {
      Some((*first, tail))
    } else {
      None
    }
  }

  fn split_last(&self) -> Option<(Self, Self::Item)> {
    if let [tail @ .., last] = *self {
      Some((tail, *last))
    } else {
      None
    }
  }
}

#[cfg(test)]
mod tests {
  use crate::Needed;
  use core::fmt::Debug;

  use super::InputSplit;

  fn split_at_aux<Input>(input: Input, n: usize, expected: Result<(Input, Input), Needed>)
  where
    Input: InputSplit + Debug + PartialEq,
  {
    assert_eq!(input.split_at(n), expected);
  }

  #[test]
  fn split_at_slice() {
    let input = &b"abcd"[..];

    for n in 0..input.len() {
      split_at_aux(input, n, Ok((&input[..n], &input[n..])));
    }

    let n = input.len() + 1;
    split_at_aux(input, n, Err(Needed::new(1)));
  }

  #[test]
  fn split_at_str() {
    let input = &"abcd"[..];

    for n in 0..input.len() {
      split_at_aux(input, n, Ok((&input[..n], &input[n..])));
    }

    let n = input.len() + 1;
    split_at_aux(input, n, Err(Needed::new(1)));
  }

  fn split_first_aux<Input>(input: Input, expected: Option<(<Input as InputSplit>::Item, Input)>)
  where
    Input: InputSplit + Debug + PartialEq,
    <Input as InputSplit>::Item: PartialEq + Debug,
  {
    assert_eq!(input.split_first(), expected);
  }

  #[test]
  fn split_first_slice() {
    let input = &b"abcd"[..];
    split_first_aux(input, Some((b'a', &input[1..])));

    let input = &b""[..];
    split_first_aux(input, None);
  }

  #[test]
  fn split_first_str() {
    let input = &"abcd"[..];
    split_first_aux(input, Some(('a', &input[1..])));

    let input = &""[..];
    split_first_aux(input, None);
  }

  fn split_last_aux<Input>(input: Input, expected: Option<(Input, <Input as InputSplit>::Item)>)
  where
    Input: InputSplit + Debug + PartialEq,
    <Input as InputSplit>::Item: PartialEq + Debug,
  {
    assert_eq!(input.split_last(), expected);
  }

  #[test]
  fn split_last_slice() {
    let input = &b"abcd"[..];
    split_last_aux(input, Some((&input[..3], b'd')));

    let input = &b""[..];
    split_last_aux(input, None);
  }

  #[test]
  fn split_last_str() {
    let input = &"abcd"[..];
    split_last_aux(input, Some((&input[..3], 'd')));

    let input = &""[..];
    split_last_aux(input, None);
  }
}
