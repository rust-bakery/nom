//! Implements the required traits to enable parsing of [`Tendril`s](https://github.com/servo/tendril).
//!

use crate::lib::std::iter::Enumerate;
use crate::lib::std::iter::Map;
use crate::lib::std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use crate::lib::std::slice::Iter;
use crate::lib::std::str::CharIndices;
use crate::lib::std::str::Chars;
use crate::traits::*;

use tendril::{fmt, Atomicity, Tendril};

impl<'a, F: fmt::Format, A: Atomicity> InputLength for Tendril<F, A> {
  #[inline]
  fn input_len(&self) -> usize {
    self.len32() as usize
  }
}

impl<'a, F: fmt::Format, A: Atomicity> InputLength for &'a Tendril<F, A> {
  #[inline]
  fn input_len(&self) -> usize {
    self.len32() as usize
  }
}

impl<'a, A: Atomicity> Offset for Tendril<fmt::UTF8, A> {
  fn offset(&self, second: &Self) -> usize {
    let fst: &str = &self;
    let snd: &str = &second;
    let fst_ptr = fst.as_ptr();
    let snd_ptr = snd.as_ptr();

    snd_ptr as usize - fst_ptr as usize
  }
}

impl<'a, A: Atomicity> Offset for Tendril<fmt::Bytes, A> {
  fn offset(&self, second: &Self) -> usize {
    let fst: &[u8] = &self;
    let snd: &[u8] = &second;
    let fst_ptr = fst.as_ptr();
    let snd_ptr = snd.as_ptr();

    snd_ptr as usize - fst_ptr as usize
  }
}

impl<'a, A: Atomicity> Offset for &'a Tendril<fmt::UTF8, A> {
  fn offset(&self, second: &Self) -> usize {
    let fst: &str = &self;
    let snd: &str = &second;
    let fst_ptr = fst.as_ptr();
    let snd_ptr = snd.as_ptr();

    snd_ptr as usize - fst_ptr as usize
  }
}

impl<'a, A: Atomicity> Offset for &'a Tendril<fmt::Bytes, A> {
  fn offset(&self, second: &Self) -> usize {
    let fst: &[u8] = &self;
    let snd: &[u8] = &second;
    let fst_ptr = fst.as_ptr();
    let snd_ptr = snd.as_ptr();

    snd_ptr as usize - fst_ptr as usize
  }
}

impl<'a, A: Atomicity> AsBytes for Tendril<fmt::Bytes, A> {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    &self
  }
}

impl<'a, A: Atomicity> AsBytes for Tendril<fmt::UTF8, A> {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    &self.as_bytes()
  }
}

impl<'a, A: Atomicity> AsBytes for &'a Tendril<fmt::Bytes, A> {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    <Tendril<fmt::Bytes, A> as AsBytes>::as_bytes(self)
  }
}

impl<'a, A: Atomicity> AsBytes for &'a Tendril<fmt::UTF8, A> {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    <Tendril<fmt::UTF8, A> as AsBytes>::as_bytes(self)
  }
}

impl<'a, A: Atomicity> InputIter for &'a Tendril<fmt::Bytes, A> {
  type Item = u8;
  type Iter = Enumerate<Self::IterElem>;
  type IterElem = Map<Iter<'a, Self::Item>, fn(&u8) -> u8>;

  #[inline]
  fn iter_indices(&self) -> Self::Iter {
    self.iter_elements().enumerate()
  }
  #[inline]
  fn iter_elements(&self) -> Self::IterElem {
    self.iter().map(star)
  }
  #[inline]
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::Item) -> bool,
  {
    self.iter().position(|b| predicate(*b))
  }
  #[inline]
  fn slice_index(&self, count: usize) -> Option<usize> {
    if self.len() >= count {
      Some(count)
    } else {
      None
    }
  }
}

impl<'a, A: Atomicity> InputIter for &'a Tendril<fmt::UTF8, A> {
  type Item = char;
  type Iter = CharIndices<'a>;
  type IterElem = Chars<'a>;

  #[inline]
  fn iter_indices(&self) -> Self::Iter {
    self.char_indices()
  }
  #[inline]
  fn iter_elements(&self) -> Self::IterElem {
    self.chars()
  }
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::Item) -> bool,
  {
    for (o, c) in self.char_indices() {
      if predicate(c) {
        return Some(o);
      }
    }
    None
  }
  #[inline]
  fn slice_index(&self, count: usize) -> Option<usize> {
    let mut cnt = 0;
    for (index, _) in self.char_indices() {
      if cnt == count {
        return Some(index);
      }
      cnt += 1;
    }
    if cnt == count {
      return Some(self.len());
    }
    None
  }
}

impl<F: fmt::Format, A: Atomicity> InputTake for Tendril<F, A> {
  #[inline]
  fn take(&self, count: usize) -> Self {
    self.subtendril(0, count as u32).into()
  }

  // return byte index
  #[inline]
  fn take_split(&self, count: usize) -> (Self, Self) {
    split_tendril_at(self, count as u32)
  }
}

fn split_tendril_at<'a, F: fmt::Format, A: Atomicity>(t: &Tendril<F, A>, i: u32) -> (Tendril<F, A>, Tendril<F, A>) {
  let len = t.len32();
  assert!(i < len);

  (t.subtendril(i, len - i).into(), t.subtendril(0, i).into())
}

impl<F: fmt::Format, A: Atomicity> UnspecializedInput for Tendril<F, A> {}

impl<'a, F: fmt::Format, A: Atomicity> UnspecializedInput for &'a Tendril<F, A> {}

impl<'a, 'b, A: Atomicity> Compare<&'b Tendril<fmt::UTF8, A>> for &'a Tendril<fmt::UTF8, A> {
  #[inline(always)]
  fn compare(&self, t: &'b Tendril<fmt::UTF8, A>) -> CompareResult {
    let a: &str = &self;
    let b: &str = &t;
    a.compare(b)
  }

  #[inline(always)]
  fn compare_no_case(&self, t: &'b Tendril<fmt::UTF8, A>) -> CompareResult {
    let a: &str = &self;
    let b: &str = &t;
    a.compare_no_case(b)
  }
}

impl<'a, A: Atomicity> Compare<&'a Tendril<fmt::UTF8, A>> for Tendril<fmt::UTF8, A> {
  #[inline(always)]
  fn compare(&self, t: &'a Tendril<fmt::UTF8, A>) -> CompareResult {
    let a: &str = &self;
    let b: &str = &t;
    a.compare(b)
  }

  #[inline(always)]
  fn compare_no_case(&self, t: &'a Tendril<fmt::UTF8, A>) -> CompareResult {
    let a: &str = &self;
    let b: &str = &t;
    a.compare_no_case(b)
  }
}

impl<'a, 'b, A: Atomicity> Compare<&'b Tendril<fmt::Bytes, A>> for &'a Tendril<fmt::Bytes, A> {
  #[inline(always)]
  fn compare(&self, t: &'b Tendril<fmt::Bytes, A>) -> CompareResult {
    let a: &[u8] = &self;
    let b: &[u8] = &t;
    a.compare(b)
  }

  #[inline(always)]
  fn compare_no_case(&self, t: &'b Tendril<fmt::Bytes, A>) -> CompareResult {
    let a: &[u8] = &self;
    let b: &[u8] = &t;
    a.compare_no_case(b)
  }
}

impl<'a, 'b, A: Atomicity> Compare<&'b Tendril<fmt::UTF8, A>> for &'a Tendril<fmt::Bytes, A> {
  #[inline(always)]
  fn compare(&self, t: &'b Tendril<fmt::UTF8, A>) -> CompareResult {
    let a: &[u8] = &self;
    let b: &str = &t;
    a.compare(b)
  }

  #[inline(always)]
  fn compare_no_case(&self, t: &'b Tendril<fmt::UTF8, A>) -> CompareResult {
    let a: &[u8] = &self;
    let b: &str = &t;
    a.compare_no_case(b)
  }
}

impl<'a, A: Atomicity> Compare<&'a str> for Tendril<fmt::UTF8, A> {
  #[inline(always)]
  fn compare(&self, t: &'a str) -> CompareResult {
    let a: &str = &self;
    a.compare(t)
  }

  #[inline(always)]
  fn compare_no_case(&self, t: &'a str) -> CompareResult {
    let a: &str = &self;
    a.compare_no_case(t)
  }
}

impl<'a, A: Atomicity> Compare<&'a Tendril<fmt::UTF8, A>> for Tendril<fmt::Bytes, A> {
  #[inline(always)]
  fn compare(&self, t: &'a Tendril<fmt::UTF8, A>) -> CompareResult {
    let a: &[u8] = &self;
    let b: &str = &t;
    a.compare(b)
  }

  #[inline(always)]
  fn compare_no_case(&self, t: &'a Tendril<fmt::UTF8, A>) -> CompareResult {
    let a: &[u8] = &self;
    let b: &str = &t;
    a.compare_no_case(b)
  }
}

impl<'a, A: Atomicity> FindToken<char> for &'a Tendril<fmt::UTF8, A> {
  fn find_token(&self, token: char) -> bool {
    (&self[..]).find_token(token)
  }
}

impl<'a, A: Atomicity> FindToken<u8> for &'a Tendril<fmt::UTF8, A> {
  fn find_token(&self, token: u8) -> bool {
    (&self[..]).find_token(token)
  }
}

impl<'a, 'b, A: Atomicity> FindToken<&'a u8> for &'b Tendril<fmt::UTF8, A> {
  fn find_token(&self, token: &'a u8) -> bool {
    (&self[..]).find_token(token)
  }
}

impl<'a, A: Atomicity> FindToken<char> for &'a Tendril<fmt::Bytes, A> {
  fn find_token(&self, token: char) -> bool {
    (&self[..]).find_token(token)
  }
}

impl<'a, A: Atomicity> FindToken<u8> for &'a Tendril<fmt::Bytes, A> {
  fn find_token(&self, token: u8) -> bool {
    (&self[..]).find_token(token)
  }
}

impl<'a, 'b, A: Atomicity> FindToken<&'a u8> for &'b Tendril<fmt::Bytes, A> {
  fn find_token(&self, token: &'a u8) -> bool {
    (&self[..]).find_token(token)
  }
}

// Substring -- Tendril<fmt::Bytes>

impl<'a, 'b, A: Atomicity> FindSubstring<&'b str> for &'a Tendril<fmt::Bytes, A> {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    let a: &[u8] = &self;
    let b: &[u8] = AsBytes::as_bytes(substr);
    a.find_substring(b)
  }
}

impl<'a, 'b, A: Atomicity> FindSubstring<&'b [u8]> for &'a Tendril<fmt::Bytes, A> {
  fn find_substring(&self, substr: &'b [u8]) -> Option<usize> {
    let a: &[u8] = &self;
    a.find_substring(substr)
  }
}

impl<'a, 'b, A: Atomicity> FindSubstring<&'b Tendril<fmt::Bytes, A>> for &'a Tendril<fmt::Bytes, A> {
  fn find_substring(&self, substr: &'b Tendril<fmt::Bytes, A>) -> Option<usize> {
    let a: &[u8] = &self;
    let b: &[u8] = &substr;
    a.find_substring(b)
  }
}

impl<'a, 'b, A: Atomicity> FindSubstring<&'b Tendril<fmt::UTF8, A>> for &'a Tendril<fmt::Bytes, A> {
  fn find_substring(&self, substr: &'b Tendril<fmt::UTF8, A>) -> Option<usize> {
    let a: &[u8] = &self;
    let b: &[u8] = AsBytes::as_bytes(substr);
    a.find_substring(b)
  }
}

// Substring -- Tendril<fmt::UTF8>

impl<'a, 'b, A: Atomicity> FindSubstring<&'b str> for &'a Tendril<fmt::UTF8, A> {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    let a: &[u8] = AsBytes::as_bytes(self);
    let b: &[u8] = AsBytes::as_bytes(substr);
    a.find_substring(b)
  }
}

impl<'a, 'b, A: Atomicity> FindSubstring<&'b [u8]> for &'a Tendril<fmt::UTF8, A> {
  fn find_substring(&self, substr: &'b [u8]) -> Option<usize> {
    let a: &[u8] = AsBytes::as_bytes(self);
    a.find_substring(substr)
  }
}

impl<'a, 'b, A: Atomicity> FindSubstring<&'b Tendril<fmt::Bytes, A>> for &'a Tendril<fmt::UTF8, A> {
  fn find_substring(&self, substr: &'b Tendril<fmt::Bytes, A>) -> Option<usize> {
    let a: &[u8] = AsBytes::as_bytes(self);
    let b: &[u8] = &substr;
    a.find_substring(b)
  }
}

impl<'a, 'b, A: Atomicity> FindSubstring<&'b Tendril<fmt::UTF8, A>> for &'a Tendril<fmt::UTF8, A> {
  fn find_substring(&self, substr: &'b Tendril<fmt::UTF8, A>) -> Option<usize> {
    let a: &[u8] = AsBytes::as_bytes(self);
    let b: &[u8] = AsBytes::as_bytes(substr);
    a.find_substring(b)
  }
}

// Substring -- &[u8]

impl<'a, 'b, A: Atomicity> FindSubstring<&'b Tendril<fmt::Bytes, A>> for &'a [u8] {
  fn find_substring(&self, substr: &'b Tendril<fmt::Bytes, A>) -> Option<usize> {
    let b: &[u8] = &substr;
    self.find_substring(b)
  }
}

impl<'a, 'b, A: Atomicity> FindSubstring<&'b Tendril<fmt::UTF8, A>> for &'a [u8] {
  fn find_substring(&self, substr: &'b Tendril<fmt::UTF8, A>) -> Option<usize> {
    let b: &[u8] = AsBytes::as_bytes(substr);
    self.find_substring(b)
  }
}

// Substring -- &str

impl<'a, 'b, A: Atomicity> FindSubstring<&'b Tendril<fmt::Bytes, A>> for &'a str {
  fn find_substring(&self, substr: &'b Tendril<fmt::Bytes, A>) -> Option<usize> {
    let a: &[u8] = AsBytes::as_bytes(self);
    let b: &[u8] = &substr;
    a.find_substring(b)
  }
}

impl<'a, 'b, A: Atomicity> FindSubstring<&'b Tendril<fmt::UTF8, A>> for &'a str {
  fn find_substring(&self, substr: &'b Tendril<fmt::UTF8, A>) -> Option<usize> {
    let a: &[u8] = AsBytes::as_bytes(self);
    let b: &[u8] = AsBytes::as_bytes(substr);
    a.find_substring(b)
  }
}

impl<F: fmt::Format, A: Atomicity> Slice<Range<usize>> for Tendril<F, A> {
  fn slice(&self, range: Range<usize>) -> Self {
    let start = range.start as u32;
    let end = range.end as u32;
    let len = self.len32();
    assert!(start <= len);
    assert!(end <= len);

    self.subtendril(start, end - start)
  }
}

impl<F: fmt::Format, A: Atomicity> Slice<RangeTo<usize>> for Tendril<F, A> {
  fn slice(&self, range: RangeTo<usize>) -> Self {
    let end = range.end as u32;
    let len = self.len32();
    assert!(end <= len);

    self.subtendril(0, end)
  }
}

impl<F: fmt::Format, A: Atomicity> Slice<RangeFrom<usize>> for Tendril<F, A> {
  fn slice(&self, range: RangeFrom<usize>) -> Self {
    let start = range.start as u32;
    let len = self.len32();
    assert!(start <= len);

    self.subtendril(start, len - start)
  }
}

impl<F: fmt::Format, A: Atomicity> Slice<RangeFull> for Tendril<F, A> {
  fn slice(&self, _range: RangeFull) -> Self {
    self.clone()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::bytes::complete::{tag, take_while};
  use crate::{error::ErrorKind, Err, IResult, Needed};

  #[test]
  fn test_tag() {
    fn parser(s: Tendril<fmt::UTF8>) -> IResult<Tendril<fmt::UTF8>, Tendril<fmt::UTF8>> {
      tag("Hello")(s)
    }

    assert_eq!(parser("Hello, World!".into()), Ok((", World!".into(), "Hello".into())));
    assert_eq!(parser("Something".into()), Err(Err::Error(("Something".into(), ErrorKind::Tag))));
    assert_eq!(parser("".into()), Err(Err::Error(("".into(), ErrorKind::Tag))));
  }

  #[test]
  fn test_take_while() {
    fn parser(s: Tendril<fmt::UTF8>) -> IResult<Tendril<fmt::UTF8>, Tendril<fmt::UTF8>> {
      take_while(|c| c == 'a')(s)
    }

    assert_eq!(parser(Tendril::from("aaaabba")), Ok(("bba".into(), "aaaa".into())));
  }
}
