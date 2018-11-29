//! Custom input types
//!

use traits::{AsBytes, AtEof, Compare, CompareResult, FindSubstring, FindToken, InputIter, InputLength, InputTake, Offset, ParseTo, Slice};

#[cfg(feature = "alloc")]
use traits::ExtendInto;

use lib::std::iter::{Enumerate, Map};
use lib::std::ops::{Deref, Range, RangeFrom, RangeFull, RangeTo};
use lib::std::slice::Iter;
use lib::std::str::{self, CharIndices, Chars, FromStr};
use lib::std::convert::From;
use lib::std::fmt::{Display, Formatter, Result};
#[cfg(feature = "alloc")]
use lib::std::string::String;

/// Holds a complete String, for which the `at_eof` method always returns true
///
/// This means that this input type will completely avoid nom's streaming features
/// and `Incomplete` results.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CompleteStr<'a>(pub &'a str);

impl<'a> From<&'a str> for CompleteStr<'a> {
  fn from(src: &'a str) -> Self {
    CompleteStr(src)
  }
}

impl<'a, 'b> From<&'b &'a str> for CompleteStr<'a> {
  fn from(src: &'b &'a str) -> Self {
    CompleteStr(*src)
  }
}

impl<'a> Display for CompleteStr<'a> {
  fn fmt(&self, f: &mut Formatter) -> Result {
    self.0.fmt(f)
  }
}

impl<'a> AsRef<str> for CompleteStr<'a> {
  fn as_ref(&self) -> &str {
    self.0
  }
}

impl<'a> Deref for CompleteStr<'a> {
  type Target = &'a str;

  #[inline]
  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

impl<'a> AtEof for CompleteStr<'a> {
  #[inline]
  fn at_eof(&self) -> bool {
    true
  }
}

impl<'a> Slice<Range<usize>> for CompleteStr<'a> {
  #[inline]
  fn slice(&self, range: Range<usize>) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> Slice<RangeTo<usize>> for CompleteStr<'a> {
  #[inline]
  fn slice(&self, range: RangeTo<usize>) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> Slice<RangeFrom<usize>> for CompleteStr<'a> {
  #[inline]
  fn slice(&self, range: RangeFrom<usize>) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> Slice<RangeFull> for CompleteStr<'a> {
  #[inline]
  fn slice(&self, range: RangeFull) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> InputIter for CompleteStr<'a> {
  type Item = char;
  type RawItem = char;
  type Iter = CharIndices<'a>;
  type IterElem = Chars<'a>;

  fn iter_indices(&self) -> Self::Iter {
    self.0.iter_indices()
  }
  fn iter_elements(&self) -> Self::IterElem {
    self.0.iter_elements()
  }
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::RawItem) -> bool,
  {
    self.0.position(predicate)
  }
  fn slice_index(&self, count: usize) -> Option<usize> {
    self.0.slice_index(count)
  }
}

impl<'a> InputTake for CompleteStr<'a> {
  fn take(&self, count: usize) -> Self {
    CompleteStr(self.0.take(count))
  }

  fn take_split(&self, count: usize) -> (Self, Self) {
    let (left, right) = self.0.take_split(count);
    (CompleteStr(left), CompleteStr(right))
  }
}

impl<'a> InputLength for CompleteStr<'a> {
  fn input_len(&self) -> usize {
    self.0.input_len()
  }
}

impl<'a, 'b> Compare<&'b str> for CompleteStr<'a> {
  fn compare(&self, t: &'b str) -> CompareResult {
    self.0.compare(t)
  }
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    self.0.compare_no_case(t)
  }
}

impl<'a, 'b> FindSubstring<&'b str> for CompleteStr<'a> {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.0.find_substring(substr)
  }
}

impl<'a> FindToken<char> for CompleteStr<'a> {
  fn find_token(&self, token: char) -> bool {
    self.0.find_token(token)
  }
}

impl<'a> FindToken<u8> for CompleteStr<'a> {
  fn find_token(&self, token: u8) -> bool {
    self.0.find_token(token)
  }
}

impl<'a, 'b> FindToken<&'a u8> for CompleteStr<'b> {
  fn find_token(&self, token: &u8) -> bool {
    self.0.find_token(token)
  }
}

impl<'a, R: FromStr> ParseTo<R> for CompleteStr<'a> {
  fn parse_to(&self) -> Option<R> {
    self.0.parse().ok()
  }
}

impl<'a> Offset for CompleteStr<'a> {
  fn offset(&self, second: &CompleteStr<'a>) -> usize {
    self.0.offset(second.0)
  }
}

impl<'a> AsBytes for CompleteStr<'a> {
  fn as_bytes(&self) -> &[u8] {
    AsBytes::as_bytes(self.0)
  }
}

#[cfg(feature = "alloc")]
impl<'a> ExtendInto for CompleteStr<'a> {
  type Item = char;
  type Extender = String;

  #[inline]
  fn new_builder(&self) -> String {
    String::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut String) {
    acc.extend(self.0.chars());
  }
}

/// Holds a complete byte array, for which the `at_eof` method always returns true
///
/// This means that this input type will completely avoid nom's streaming features
/// and `Incomplete` results.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CompleteByteSlice<'a>(pub &'a [u8]);

impl<'a> From<&'a [u8]> for CompleteByteSlice<'a> {
  fn from(src: &'a [u8]) -> Self {
    CompleteByteSlice(src)
  }
}

impl<'a, 'b> From<&'b &'a [u8]> for CompleteByteSlice<'a> {
  fn from(src: &'b &'a [u8]) -> Self {
    CompleteByteSlice(*src)
  }
}

impl<'a> Deref for CompleteByteSlice<'a> {
  type Target = &'a [u8];

  #[inline]
  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

impl<'a> AtEof for CompleteByteSlice<'a> {
  #[inline]
  fn at_eof(&self) -> bool {
    true
  }
}

impl<'a> Slice<Range<usize>> for CompleteByteSlice<'a> {
  #[inline]
  fn slice(&self, range: Range<usize>) -> Self {
    CompleteByteSlice(self.0.slice(range))
  }
}

impl<'a> Slice<RangeTo<usize>> for CompleteByteSlice<'a> {
  #[inline]
  fn slice(&self, range: RangeTo<usize>) -> Self {
    CompleteByteSlice(self.0.slice(range))
  }
}

impl<'a> Slice<RangeFrom<usize>> for CompleteByteSlice<'a> {
  #[inline]
  fn slice(&self, range: RangeFrom<usize>) -> Self {
    CompleteByteSlice(self.0.slice(range))
  }
}

impl<'a> Slice<RangeFull> for CompleteByteSlice<'a> {
  #[inline]
  fn slice(&self, range: RangeFull) -> Self {
    CompleteByteSlice(self.0.slice(range))
  }
}

impl<'a> InputIter for CompleteByteSlice<'a> {
  type Item = u8;
  type RawItem = u8;
  type Iter = Enumerate<Self::IterElem>;
  type IterElem = Map<Iter<'a, Self::Item>, fn(&u8) -> u8>; //Iter<'a, Self::RawItem>;

  fn iter_indices(&self) -> Self::Iter {
    self.0.iter_indices()
  }
  fn iter_elements(&self) -> Self::IterElem {
    self.0.iter_elements()
  }
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::RawItem) -> bool,
  {
    self.0.position(predicate)
  }
  fn slice_index(&self, count: usize) -> Option<usize> {
    self.0.slice_index(count)
  }
}

impl<'a> InputTake for CompleteByteSlice<'a> {
  fn take(&self, count: usize) -> Self {
    CompleteByteSlice(self.0.take(count))
  }

  fn take_split(&self, count: usize) -> (Self, Self) {
    let (left, right) = self.0.take_split(count);
    (CompleteByteSlice(left), CompleteByteSlice(right))
  }
}

impl<'a> InputLength for CompleteByteSlice<'a> {
  fn input_len(&self) -> usize {
    self.0.input_len()
  }
}

impl<'a, 'b> Compare<&'b [u8]> for CompleteByteSlice<'a> {
  fn compare(&self, t: &'b [u8]) -> CompareResult {
    self.0.compare(t)
  }
  fn compare_no_case(&self, t: &'b [u8]) -> CompareResult {
    self.0.compare_no_case(t)
  }
}

impl<'a, 'b> Compare<&'b str> for CompleteByteSlice<'a> {
  fn compare(&self, t: &'b str) -> CompareResult {
    self.0.compare(t)
  }
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    self.0.compare_no_case(t)
  }
}

impl<'a, 'b> FindSubstring<&'b [u8]> for CompleteByteSlice<'a> {
  fn find_substring(&self, substr: &'b [u8]) -> Option<usize> {
    self.0.find_substring(substr)
  }
}

impl<'a, 'b> FindSubstring<&'b str> for CompleteByteSlice<'a> {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.0.find_substring(substr)
  }
}

impl<'a> FindToken<char> for CompleteByteSlice<'a> {
  fn find_token(&self, token: char) -> bool {
    self.0.find_token(token)
  }
}

impl<'a> FindToken<u8> for CompleteByteSlice<'a> {
  fn find_token(&self, token: u8) -> bool {
    self.0.find_token(token)
  }
}

impl<'a, 'b> FindToken<&'a u8> for CompleteByteSlice<'b> {
  fn find_token(&self, token: &u8) -> bool {
    self.0.find_token(token)
  }
}

impl<'a, R: FromStr> ParseTo<R> for CompleteByteSlice<'a> {
  fn parse_to(&self) -> Option<R> {
    self.0.parse_to()
  }
}

impl<'a> Offset for CompleteByteSlice<'a> {
  fn offset(&self, second: &CompleteByteSlice<'a>) -> usize {
    self.0.offset(second.0)
  }
}

impl<'a> AsBytes for CompleteByteSlice<'a> {
  fn as_bytes(&self) -> &[u8] {
    self.0.as_bytes()
  }
}

#[cfg(feature = "std")]
impl<'a> super::util::HexDisplay for CompleteByteSlice<'a> {
  fn to_hex(&self, chunk_size: usize) -> String {
    self.0.to_hex(chunk_size)
  }

  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
    self.0.to_hex_from(chunk_size, from)
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Hash)]
pub struct Input<T> {
  pub inner: T,
  pub at_eof: bool,
}

impl<T> AtEof for Input<T> {
  fn at_eof(&self) -> bool {
    self.at_eof
  }
}

impl<T: Slice<Range<usize>>> Slice<Range<usize>> for Input<T> {
  fn slice(&self, range: Range<usize>) -> Self {
    Input {
      inner: self.inner.slice(range),
      at_eof: self.at_eof,
    }
  }
}

impl<T: Slice<RangeTo<usize>>> Slice<RangeTo<usize>> for Input<T> {
  fn slice(&self, range: RangeTo<usize>) -> Self {
    Input {
      inner: self.inner.slice(range),
      at_eof: self.at_eof,
    }
  }
}

impl<T: Slice<RangeFrom<usize>>> Slice<RangeFrom<usize>> for Input<T> {
  fn slice(&self, range: RangeFrom<usize>) -> Self {
    Input {
      inner: self.inner.slice(range),
      at_eof: self.at_eof,
    }
  }
}

impl<T: Slice<RangeFull>> Slice<RangeFull> for Input<T> {
  fn slice(&self, range: RangeFull) -> Self {
    Input {
      inner: self.inner.slice(range),
      at_eof: self.at_eof,
    }
  }
}

impl<T: InputIter> InputIter for Input<T> {
  type Item = <T as InputIter>::Item;
  type RawItem = <T as InputIter>::RawItem;
  type Iter = <T as InputIter>::Iter;
  type IterElem = <T as InputIter>::IterElem;

  fn iter_indices(&self) -> Self::Iter {
    self.inner.iter_indices()
  }
  fn iter_elements(&self) -> Self::IterElem {
    self.inner.iter_elements()
  }
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::RawItem) -> bool,
  {
    self.inner.position(predicate)
  }
  fn slice_index(&self, count: usize) -> Option<usize> {
    self.inner.slice_index(count)
  }
}

impl<T: InputTake> InputTake for Input<T> {
  fn take(&self, count: usize) -> Self {
    Input {
      inner: self.inner.take(count),
      at_eof: self.at_eof,
    }
  }

  fn take_split(&self, count: usize) -> (Self, Self) {
    let (left, right) = self.inner.take_split(count);
    (
      Input {
        inner: left,
        at_eof: self.at_eof,
      },
      Input {
        inner: right,
        at_eof: self.at_eof,
      },
    )
  }
}

impl<T: InputLength> InputLength for Input<T> {
  fn input_len(&self) -> usize {
    self.inner.input_len()
  }
}

impl<'b, T: Compare<&'b str>> Compare<&'b str> for Input<T> {
  fn compare(&self, t: &'b str) -> CompareResult {
    self.inner.compare(t)
  }
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    self.inner.compare_no_case(t)
  }
}

impl<'b, T: FindSubstring<&'b str>> FindSubstring<&'b str> for Input<T> {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.inner.find_substring(substr)
  }
}

impl<T: FindToken<char>> FindToken<char> for Input<T> {
  fn find_token(&self, token: char) -> bool {
    self.inner.find_token(token)
  }
}

impl<T: FindToken<u8>> FindToken<u8> for Input<T> {
  fn find_token(&self, token: u8) -> bool {
    self.inner.find_token(token)
  }
}

impl<'a, T: FindToken<&'a u8>> FindToken<&'a u8> for Input<T> {
  fn find_token(&self, token: &'a u8) -> bool {
    self.inner.find_token(token)
  }
}

impl<'a, R: FromStr, T: ParseTo<R>> ParseTo<R> for Input<T> {
  fn parse_to(&self) -> Option<R> {
    self.inner.parse_to()
  }
}

impl<T: Offset> Offset for Input<T> {
  fn offset(&self, second: &Input<T>) -> usize {
    self.inner.offset(&second.inner)
  }
}

impl<T: AsBytes> AsBytes for Input<T> {
  fn as_bytes(&self) -> &[u8] {
    AsBytes::as_bytes(&self.inner)
  }
}
