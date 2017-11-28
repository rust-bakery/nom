use traits::{AtEof,Compare,CompareResult,InputLength,InputIter,InputTake,Slice,FindSubstring,FindToken,ParseTo};
use util::Offset;

use std::str::{self,FromStr,Chars,CharIndices};
use std::ops::{Range,RangeTo,RangeFrom,RangeFull};
use std::iter::Enumerate;
use std::slice::Iter;

#[derive(Clone,Copy,Debug,PartialEq)]
pub struct CompleteStr<'a>(pub &'a str);

impl<'a> AtEof for CompleteStr<'a> {
  fn at_eof(&self) -> bool { true }
}

impl<'a> Slice<Range<usize>> for CompleteStr<'a> {
  fn slice(&self, range:Range<usize>) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> Slice<RangeTo<usize>> for CompleteStr<'a> {
  fn slice(&self, range:RangeTo<usize>) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> Slice<RangeFrom<usize>> for CompleteStr<'a> {
  fn slice(&self, range:RangeFrom<usize>) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> Slice<RangeFull> for CompleteStr<'a> {
  fn slice(&self, range:RangeFull) -> Self {
    CompleteStr(self.0.slice(range))
  }
}

impl<'a> InputIter for CompleteStr<'a> {
  type Item     = char;
  type RawItem  = char;
  type Iter     = CharIndices<'a>;
  type IterElem = Chars<'a>;

  fn iter_indices(&self)  -> Self::Iter {
    self.0.iter_indices()
  }
  fn iter_elements(&self) -> Self::IterElem {
    self.0.iter_elements()
  }
  fn position<P>(&self, predicate: P) -> Option<usize> where P: Fn(Self::RawItem) -> bool {
    self.0.position(predicate)
  }
  fn slice_index(&self, count:usize) -> Option<usize> {
    self.0.slice_index(count)
  }
}

impl<'a> InputTake for CompleteStr<'a> {
  fn take(&self, count: usize)  -> Option<Self> {
    self.0.take(count).map(|s| CompleteStr(s))
  }

  fn take_split(&self, count: usize) -> Option<(Self,Self)> {
    self.0.take_split(count).map(|(s1, s2)| (CompleteStr(s1), CompleteStr(s2)))
  }
}

impl<'a> InputLength for CompleteStr<'a> {
  fn input_len(&self) -> usize {
    self.0.input_len()
  }
}

impl<'a,'b> Compare<&'b str> for CompleteStr<'a> {
  fn compare(&self, t: &'b str) -> CompareResult {
    self.0.compare(t)
  }
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    self.0.compare_no_case(t)
  }
}


impl<'a,'b> FindSubstring<&'b str> for CompleteStr<'a> {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.0.find_substring(substr)
  }
}

impl<'a> FindToken<CompleteStr<'a>> for u8 {
  fn find_token(&self, input: CompleteStr<'a>) -> bool {
    self.find_token(input.0)
  }
}

impl<'a, 'b> FindToken<CompleteStr<'a>> for &'b u8 {
  fn find_token(&self, input: CompleteStr<'a>) -> bool {
    self.find_token(input.0)
  }
}

impl<'a, R:FromStr> ParseTo<R> for CompleteStr<'a> {
  fn parse_to(&self) -> Option<R> {
    self.0.parse().ok()
  }
}

impl<'a> Offset for CompleteStr<'a> {
  fn offset(&self, second:&CompleteStr<'a>) -> usize {
    self.0.offset(second.0)
  }
}

#[derive(Clone,Copy,Debug,PartialEq)]
pub struct CompleteByteSlice<'a>(pub &'a [u8]);

impl<'a> AtEof for CompleteByteSlice<'a> {
  fn at_eof(&self) -> bool { true }
}

impl<'a> Slice<Range<usize>> for CompleteByteSlice<'a> {
  fn slice(&self, range:Range<usize>) -> Self {
    CompleteByteSlice(self.0.slice(range))
  }
}

impl<'a> Slice<RangeTo<usize>> for CompleteByteSlice<'a> {
  fn slice(&self, range:RangeTo<usize>) -> Self {
    CompleteByteSlice(self.0.slice(range))
  }
}

impl<'a> Slice<RangeFrom<usize>> for CompleteByteSlice<'a> {
  fn slice(&self, range:RangeFrom<usize>) -> Self {
    CompleteByteSlice(self.0.slice(range))
  }
}

impl<'a> Slice<RangeFull> for CompleteByteSlice<'a> {
  fn slice(&self, range:RangeFull) -> Self {
    CompleteByteSlice(self.0.slice(range))
  }
}

impl<'a> InputIter for CompleteByteSlice<'a> {
  type Item     = &'a u8;
  type RawItem  = u8;
  type Iter     = Enumerate<Iter<'a, Self::RawItem>>;
  type IterElem = Iter<'a, Self::RawItem>;

  fn iter_indices(&self)  -> Self::Iter {
    self.0.iter_indices()
  }
  fn iter_elements(&self) -> Self::IterElem {
    self.0.iter_elements()
  }
  fn position<P>(&self, predicate: P) -> Option<usize> where P: Fn(Self::RawItem) -> bool {
    self.0.position(predicate)
  }
  fn slice_index(&self, count:usize) -> Option<usize> {
    self.0.slice_index(count)
  }
}

impl<'a> InputTake for CompleteByteSlice<'a> {
  fn take(&self, count: usize)  -> Option<Self> {
    self.0.take(count).map(|s| CompleteByteSlice(s))
  }

  fn take_split(&self, count: usize) -> Option<(Self,Self)> {
    self.0.take_split(count).map(|(s1, s2)| (CompleteByteSlice(s1), CompleteByteSlice(s2)))
  }
}

impl<'a> InputLength for CompleteByteSlice<'a> {
  fn input_len(&self) -> usize {
    self.0.input_len()
  }
}

impl<'a,'b> Compare<&'b [u8]> for CompleteByteSlice<'a> {
  fn compare(&self, t: &'b [u8]) -> CompareResult {
    self.0.compare(t)
  }
  fn compare_no_case(&self, t: &'b [u8]) -> CompareResult {
    self.0.compare_no_case(t)
  }
}

impl<'a,'b> Compare<&'b str> for CompleteByteSlice<'a> {
  fn compare(&self, t: &'b str) -> CompareResult {
    self.0.compare(t)
  }
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    self.0.compare_no_case(t)
  }
}

impl<'a,'b> FindSubstring<&'b [u8]> for CompleteByteSlice<'a> {
  fn find_substring(&self, substr: &'b [u8]) -> Option<usize> {
    self.0.find_substring(substr)
  }
}

impl<'a,'b> FindSubstring<&'b str> for CompleteByteSlice<'a> {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.0.find_substring(substr)
  }
}

impl<'a> FindToken<CompleteByteSlice<'a>> for u8 {
  fn find_token(&self, input: CompleteByteSlice<'a>) -> bool {
    self.find_token(input.0)
  }
}

impl<'a, 'b> FindToken<CompleteByteSlice<'a>> for &'b u8 {
  fn find_token(&self, input: CompleteByteSlice<'a>) -> bool {
    self.find_token(input.0)
  }
}

impl<'a, R:FromStr> ParseTo<R> for CompleteByteSlice<'a> {
  fn parse_to(&self) -> Option<R> {
    self.0.parse_to()
  }
}

impl<'a> Offset for CompleteByteSlice<'a> {
  fn offset(&self, second:&CompleteByteSlice<'a>) -> usize {
    self.0.offset(second.0)
  }
}
