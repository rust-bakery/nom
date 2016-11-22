//! Traits input types have to implement to work with nom combinators
//!
use std::ops::{Range,RangeTo,RangeFrom,RangeFull};

#[cfg(not(feature = "core"))]
use std::str::Chars;

pub trait InputLength {
  #[inline]
  fn input_len(&self) -> usize;
}

impl<'a, T> InputLength for &'a[T] {
  #[inline]
  fn input_len(&self) -> usize {
    self.len()
  }
}

#[cfg(not(feature = "core"))]
impl<'a> InputLength for &'a str {
  #[inline]
  fn input_len(&self) -> usize {
    self.len()
  }
}

impl<'a> InputLength for (&'a [u8], usize) {
  #[inline]
  fn input_len(&self) -> usize {
    //println!("bit input length for ({:?}, {}):", self.0, self.1);
    let res = self.0.len() * 8 - self.1;
    //println!("-> {}", res);
    res
  }
}

use std::iter::Enumerate;
#[cfg(not(feature = "core"))]
use std::str::CharIndices;

pub trait AsChar {
    #[inline]
    fn as_char(self)      -> char;
    #[inline]
    fn is_alpha(self)     -> bool;
    #[inline]
    fn is_alphanum(self)  -> bool;
    #[inline]
    fn is_dec_digit(self) -> bool;
    #[inline]
    fn is_hex_digit(self) -> bool;
    #[inline]
    fn is_oct_digit(self) -> bool;
}

impl AsChar for u8 {
    #[inline]
    fn as_char(self)      -> char { self as char }
    #[inline]
    fn is_alpha(self)     -> bool {
      (self >= 0x41 && self <= 0x5A) || (self >= 0x61 && self <= 0x7A)
    }
    #[inline]
    fn is_alphanum(self)  -> bool { self.is_alpha() || self.is_dec_digit() }
    #[inline]
    fn is_dec_digit(self) -> bool {
      self >= 0x30 && self <= 0x39
    }
    #[inline]
    fn is_hex_digit(self) -> bool {
      (self >= 0x30 && self <= 0x39) ||
      (self >= 0x41 && self <= 0x46) ||
      (self >= 0x61 && self <= 0x66)
    }
    #[inline]
    fn is_oct_digit(self) -> bool {
      self >= 0x30 && self <= 0x37
    }
}
impl<'a> AsChar for &'a u8 {
    #[inline]
    fn as_char(self)      -> char { *self as char }
    #[inline]
    fn is_alpha(self)     -> bool {
      (*self >= 0x41 && *self <= 0x5A) || (*self >= 0x61 && *self <= 0x7A)
    }
    #[inline]
    fn is_alphanum(self)  -> bool { self.is_alpha() || self.is_dec_digit() }
    #[inline]
    fn is_dec_digit(self) -> bool {
      *self >= 0x30 && *self <= 0x39
    }
    #[inline]
    fn is_hex_digit(self) -> bool {
      (*self >= 0x30 && *self <= 0x39) ||
      (*self >= 0x41 && *self <= 0x46) ||
      (*self >= 0x61 && *self <= 0x66)
    }
    #[inline]
    fn is_oct_digit(self)   -> bool {
      *self >= 0x30 && *self <= 0x37
    }
}

impl AsChar for char {
    #[inline]
    fn as_char(self)      -> char { self }
    #[inline]
    fn is_alpha(self)     -> bool { self.is_alphabetic() }
    #[inline]
    fn is_alphanum(self)  -> bool { self.is_alpha() || self.is_dec_digit() }
    #[inline]
    fn is_dec_digit(self) -> bool { self.is_digit(10) }
    #[inline]
    fn is_hex_digit(self) -> bool { self.is_digit(16) }
    #[inline]
    fn is_oct_digit(self) -> bool { self.is_digit(8) }
}

pub trait InputIter {
    type Item     : AsChar;
    type RawItem  : AsChar;
    type Iter     : Iterator<Item=(usize, Self::Item)>;
    type IterElem : Iterator<Item=Self::Item>;

    fn iter_indices(&self)  -> Self::Iter;
    fn iter_elements(&self) -> Self::IterElem;
    fn position<P>(&self, predicate: P) -> Option<usize> where P: Fn(Self::RawItem) -> bool;
    fn slice_index(&self, count:usize) -> Option<usize>;
}

pub trait InputTake {
    fn take<P>(&self, count: usize)  -> Option<&Self>;
    fn take_split<P>(&self, count: usize) -> Option<(&Self,&Self)>;
}

impl<'a> InputIter for &'a [u8] {
    type Item     = &'a u8;
    type RawItem  = u8;
    type Iter     = Enumerate<::std::slice::Iter<'a, u8>>;
    type IterElem = ::std::slice::Iter<'a, u8>;

    #[inline]
    fn iter_indices(&self) -> Enumerate<::std::slice::Iter<'a, u8>> {
        self.iter().enumerate()
    }
    #[inline]
    fn iter_elements(&self) -> ::std::slice::Iter<'a,u8> {
      self.iter()
    }
    #[inline]
    fn position<P>(&self, predicate: P) -> Option<usize> where P: Fn(Self::RawItem) -> bool {
      self.iter().position(|b| predicate(*b))
    }
    #[inline]
    fn slice_index(&self, count:usize) -> Option<usize> {
      if self.len() >= count {
        Some(count)
      } else {
        None
      }
    }
}

impl InputTake for [u8] {
    #[inline]
    fn take<P>(&self, count: usize) -> Option<&Self> {
      if self.len() >= count {
        Some(&self[0..count])
      } else {
        None
      }
    }
    #[inline]
    fn take_split<P>(&self, count: usize) -> Option<(&Self,&Self)> {
      if self.len() >= count {
        Some((&self[count..],&self[..count]))
      } else {
        None
      }
    }
}

#[cfg(not(feature = "core"))]
impl<'a> InputIter for &'a str {
    type Item     = char;
    type RawItem  = char;
    type Iter     = CharIndices<'a>;
    type IterElem = Chars<'a>;
    #[inline]
    fn iter_indices(&self) -> CharIndices<'a> {
        self.char_indices()
    }
    #[inline]
    fn iter_elements(&self) -> Chars<'a> {
      self.chars()
    }
    fn position<P>(&self, predicate: P) -> Option<usize> where P: Fn(Self::RawItem) -> bool {
      for (o,c) in self.char_indices() {
        if predicate(c) {
          return Some(o)
        }
      }
      None
    }
    #[inline]
    fn slice_index(&self, count:usize) -> Option<usize> {
      let mut cnt    = 0;
      for (index, _) in self.char_indices() {
        if cnt == count {
          return Some(index)
        }
        cnt += 1;
      }
      if cnt == count {
        return Some(self.len())
      }
      None
    }
}

#[cfg(not(feature = "core"))]
impl InputTake for str {
    #[inline]
    fn take<P>(&self, count: usize) -> Option<&Self> {
      let mut cnt    = 0;
      for (index, _) in self.char_indices() {
        if cnt == count {
          return Some(&self[..index])
        }
        cnt += 1;
      }
      None
    }

    // return byte index
    #[inline]
    fn take_split<P>(&self, count: usize) -> Option<(&Self,&Self)> {
      let mut cnt    = 0;
      for (index, _) in self.char_indices() {
        if cnt == count {
          return Some((&self[index..],&self[..index]))
        }
        cnt += 1;
      }
      None
    }
}

#[derive(Debug,PartialEq)]
pub enum CompareResult {
  Ok,
  Incomplete,
  Error
}

pub trait Compare<T> {
  fn compare(&self, t:T)         -> CompareResult;
  fn compare_no_case(&self, t:T) -> CompareResult;
}

impl<'a,'b> Compare<&'b[u8]> for &'a [u8] {
  #[inline(always)]
  fn compare(&self, t: &'b[u8]) -> CompareResult {
    let len     = self.len();
    let blen    = t.len();
    let m       = if len < blen { len } else { blen };
    let reduced = &self[..m];
    let b       = &t[..m];

    if reduced != b {
      CompareResult::Error
    } else if m < blen {
      CompareResult::Incomplete
    } else {
      CompareResult::Ok
    }
  }

  #[inline(always)]
  fn compare_no_case(&self, t: &'b[u8]) -> CompareResult {
    let len     = self.len();
    let blen    = t.len();
    let m       = if len < blen { len } else { blen };
    let reduced = &self[..m];
    let other   = &t[..m];

    if !reduced.iter().zip(other).all(|(a, b)| {
      match (*a,*b) {
        (0...64, 0...64) | (91...96, 91...96) | (123...255, 123...255) => a == b,
        (65...90, 65...90) | (97...122, 97...122) | (65...90, 97...122 ) |(97...122, 65...90) => {
          *a & 0b01000000 == *b & 0b01000000
        }
        _ => false
      }
    }) {
      CompareResult::Error
    } else if m < blen {
      CompareResult::Incomplete
    } else {
      CompareResult::Ok
    }
  }
}

#[cfg(not(feature = "core"))]
impl<'a,'b> Compare<&'b str> for &'a [u8] {
  #[inline(always)]
  fn compare(&self, t: &'b str) -> CompareResult {
    self.compare(str::as_bytes(t))
  }
  #[inline(always)]
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    self.compare_no_case(str::as_bytes(t))
  }
}

#[cfg(not(feature = "core"))]
impl<'a,'b> Compare<&'b str> for &'a str {
  #[inline(always)]
  fn compare(&self, t: &'b str) -> CompareResult {
    let pos = self.chars().zip(t.chars()).position(|(a,b)| a != b);

    match pos {
      Some(_) => CompareResult::Error,
      None    => if self.len() >= t.len() {
        CompareResult::Ok
      } else {
        CompareResult::Incomplete
      }
    }
  }

  //FIXME: this version is too simple and does not use the current locale
  #[inline(always)]
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    let pos = self.to_lowercase().chars().zip(t.to_lowercase().chars()).position(|(a,b)| a != b);

    match pos {
      Some(_) => CompareResult::Error,
      None    => if self.len() >= t.len() {
        CompareResult::Ok
      } else {
        CompareResult::Incomplete
      }
    }
  }
}

pub trait FindToken<T> {
  fn find_token(&self, list: T) -> bool;
}

impl<'a> FindToken<&'a[u8]> for u8 {
  fn find_token(&self, list: &[u8]) -> bool {
    for &i in list.iter() {
      if *self == i { return true }
    }
    false
  }
}

#[cfg(not(feature = "core"))]
impl<'a> FindToken<&'a str> for u8 {
  fn find_token(&self, list: &str) -> bool {
    self.find_token(str::as_bytes(list))
  }
}

#[cfg(not(feature = "core"))]
impl<'a> FindToken<&'a str> for char {
  fn find_token(&self, list: &str) -> bool {
    for i in list.chars() {
      if *self == i { return true }
    }
    false
  }
}

pub trait FindSubstring<T> {
  fn find_substring(&self, substr: T) -> Option<usize>;
}

impl<'a,'b> FindSubstring<&'b [u8]> for &'a[u8] {
  fn find_substring(&self, substr: &'b[u8]) -> Option<usize> {
    for (index,win) in self.windows(substr.len()).enumerate() {
      if win == substr {
        return Some(index)
      }
    }
    None
  }
}

#[cfg(not(feature = "core"))]
impl<'a,'b> FindSubstring<&'b str> for &'a[u8] {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.find_substring(str::as_bytes(substr))
  }
}

#[cfg(not(feature = "core"))]
impl<'a,'b> FindSubstring<&'b str> for &'a str {
  //returns byte index
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.find(substr)
  }
}

pub trait Slice<R> {
  #[inline(always)]
  fn slice(&self, range: R) -> Self;
}

impl<'a,T> Slice<Range<usize>> for &'a [T] {
  fn slice(&self, range:Range<usize>) -> Self {
    &self[range]
  }
}

impl<'a,T> Slice<RangeTo<usize>> for &'a [T] {
  fn slice(&self, range:RangeTo<usize>) -> Self {
    &self[range]
  }
}

impl<'a,T> Slice<RangeFrom<usize>> for &'a [T] {
  fn slice(&self, range:RangeFrom<usize>) -> Self {
    &self[range]
  }
}

impl<'a,T> Slice<RangeFull> for &'a [T] {
  fn slice(&self, range:RangeFull) -> Self {
    &self[range]
  }
}

impl<'a> Slice<Range<usize>> for &'a str {
  fn slice(&self, range:Range<usize>) -> Self {
    &self[range]
  }
}

impl<'a> Slice<RangeTo<usize>> for &'a str {
  fn slice(&self, range:RangeTo<usize>) -> Self {
    &self[range]
  }
}

impl<'a> Slice<RangeFrom<usize>> for &'a str {
  fn slice(&self, range:RangeFrom<usize>) -> Self {
    &self[range]
  }
}

impl<'a> Slice<RangeFull> for &'a str {
  fn slice(&self, range:RangeFull) -> Self {
    &self[range]
  }
}

macro_rules! array_impls {
  ($($N:expr)+) => {
    $(
      impl InputLength for [u8; $N] {
        #[inline]
        fn input_len(&self) -> usize {
          self.len()
        }
      }

      impl<'a> InputLength for &'a [u8; $N] {
        #[inline]
        fn input_len(&self) -> usize {
          self.len()
        }
      }

      impl<'a> Compare<[u8; $N]> for &'a [u8] {
        #[inline(always)]
        fn compare(&self, t: [u8; $N]) -> CompareResult {
          self.compare(&t[..])
        }

        #[inline(always)]
        fn compare_no_case(&self, t: [u8;$N]) -> CompareResult {
          self.compare_no_case(&t[..])
        }
      }

      impl<'a,'b> Compare<&'b [u8; $N]> for &'a [u8] {
        #[inline(always)]
        fn compare(&self, t: &'b [u8; $N]) -> CompareResult {
          self.compare(&t[..])
        }

        #[inline(always)]
        fn compare_no_case(&self, t: &'b [u8;$N]) -> CompareResult {
          self.compare_no_case(&t[..])
        }
      }
    )+
  };
}


array_impls! {
     0  1  2  3  4  5  6  7  8  9
    10 11 12 13 14 15 16 17 18 19
    20 21 22 23 24 25 26 27 28 29
    30 31 32
}
