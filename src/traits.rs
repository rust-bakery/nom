//! Traits input types have to implement to work with nom combinators
//!
use std::ops::{Range,RangeTo,RangeFrom,RangeFull};
use std::iter::Enumerate;
use std::slice::Iter;

use std::str::Chars;
use std::str::CharIndices;
use std::str::FromStr;
use std::str::from_utf8;

use memchr;


/// abstract method to calculate the input length
pub trait InputLength {
  /// calculates the input length, as indicated by its name,
  /// and the name of the trait itself
  #[inline]
  fn input_len(&self) -> usize;
}

impl<'a, T> InputLength for &'a[T] {
  #[inline]
  fn input_len(&self) -> usize {
    self.len()
  }
}

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

/// transforms common types to a char for basic token parsing
pub trait AsChar {
    /// makes a char from self
    #[inline]
    fn as_char(self)      -> char;

    /// tests that self is an alphabetic character
    ///
    /// warning: for `&str` it recognizes alphabetic
    /// characters outside of the 52 ASCII letters
    #[inline]
    fn is_alpha(self)     -> bool;

    /// tests that self is an alphabetic character
    /// or a decimal digit
    #[inline]
    fn is_alphanum(self)  -> bool;
    /// tests that self is a decimal digit
    #[inline]
    fn is_dec_digit(self) -> bool;
    /// tests that self is an hex digit
    #[inline]
    fn is_hex_digit(self) -> bool;
    /// tests that self is an octal digit
    #[inline]
    fn is_oct_digit(self) -> bool;
    /// gets the len in bytes for self
    #[inline]
    fn len(self) -> usize;
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
    #[inline]
    fn len(self) -> usize {
      1
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
    #[inline]
    fn len(self) -> usize {
      1
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
    #[inline]
    fn len(self) -> usize { self.len_utf8() }
}

impl<'a> AsChar for &'a char {
    #[inline]
    fn as_char(self)      -> char { self.clone() }
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
    #[inline]
    fn len(self) -> usize { self.len_utf8() }
}

/// abstracts common iteration operations on the input type
///
/// it needs a distinction between `Item` and `RawItem` because
/// `&[T]` iterates on references
pub trait InputIter {
    type Item;
    type RawItem;
    type Iter     : Iterator<Item=(usize, Self::Item)>;
    type IterElem : Iterator<Item=Self::Item>;

    /// returns an iterator over the elements and their byte offsets
    fn iter_indices(&self)  -> Self::Iter;
    /// returns an iterator over the elements
    fn iter_elements(&self) -> Self::IterElem;
    /// finds the byte position of the element
    fn position<P>(&self, predicate: P) -> Option<usize> where P: Fn(Self::RawItem) -> bool;
    /// get the byte offset from the element's position in the stream
    fn slice_index(&self, count:usize) -> Option<usize>;
}

/// abstracts slicing operations
pub trait InputTake {
    /// returns a slice of `count` bytes
    fn take<P>(&self, count: usize)  -> Option<&Self>;
    /// split the stream at the `count` byte offset
    fn take_split<P>(&self, count: usize) -> Option<(&Self,&Self)>;
}

impl<'a> InputIter for &'a [u8] {
    type Item     = &'a u8;
    type RawItem  = u8;
    type Iter     = Enumerate<Iter<'a, Self::RawItem>>;
    type IterElem = Iter<'a, Self::RawItem>;

    #[inline]
    fn iter_indices(&self) -> Self::Iter {
        self.iter().enumerate()
    }
    #[inline]
    fn iter_elements(&self) -> Self::IterElem {
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

impl<'a> InputIter for &'a str {
    type Item     = char;
    type RawItem  = char;
    type Iter     = CharIndices<'a>;
    type IterElem = Chars<'a>;
    #[inline]
    fn iter_indices(&self) -> Self::Iter {
        self.char_indices()
    }
    #[inline]
    fn iter_elements(&self) -> Self::IterElem {
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

/// indicates wether a comparison was successful, an error, or
/// if more data was needed
#[derive(Debug,PartialEq)]
pub enum CompareResult {
  Ok,
  Incomplete,
  Error
}

/// abstracts comparison operations
pub trait Compare<T> {
  /// compares self to another value for equality
  fn compare(&self, t:T)         -> CompareResult;
  /// compares self to another value for equality
  /// independently of the case.
  ///
  /// warning: for `&str`, the comparison is done
  /// by lowercasing both strings and comparing
  /// the result. This is a temporary solution until
  /// a better one appears
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
          *a | 0b00100000 == *b | 0b00100000
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

/// look for self in the given input stream
pub trait FindToken<T> {
  fn find_token(&self, input: T) -> bool;
}

impl<'a> FindToken<&'a[u8]> for u8 {
  fn find_token(&self, input: &[u8]) -> bool {
    memchr::memchr(*self, input).is_some()
  }
}

impl<'a> FindToken<&'a str> for u8 {
  fn find_token(&self, input: &str) -> bool {
    self.find_token(str::as_bytes(input))
  }
}

impl<'a,'b> FindToken<&'a[u8]> for &'b u8 {
  fn find_token(&self, input: &[u8]) -> bool {
    memchr::memchr(**self, input).is_some()
  }
}

impl<'a,'b> FindToken<&'a str> for &'b u8 {
  fn find_token(&self, input: &str) -> bool {
    self.find_token(str::as_bytes(input))
  }
}

impl<'a> FindToken<&'a str> for char {
  fn find_token(&self, input: &str) -> bool {
    for i in input.chars() {
      if *self == i { return true }
    }
    false
  }
}

/// look for a substring in self
pub trait FindSubstring<T> {
  fn find_substring(&self, substr: T) -> Option<usize>;
}

impl<'a,'b> FindSubstring<&'b [u8]> for &'a[u8] {
  fn find_substring(&self, substr: &'b[u8]) -> Option<usize> {
    let substr_len = substr.len();

    if substr_len == 0 {
      None
    } else if substr_len == 1 {
      memchr::memchr(substr[0], self)
    } else {
      let max = self.len() - substr_len;
      let mut offset = 0;
      let mut haystack = &self[..];

      while let Some(position) = memchr::memchr(substr[0], haystack) {
        offset += position;

        if offset > max {
          return None
        }

        if &haystack[position..position + substr_len] == substr {
          return Some(offset)
        }

        haystack  = &haystack[position + 1..];
        offset   += 1;
      }

      None
    }
  }
}

impl<'a,'b> FindSubstring<&'b str> for &'a[u8] {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.find_substring(str::as_bytes(substr))
  }
}

impl<'a,'b> FindSubstring<&'b str> for &'a str {
  //returns byte index
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.find(substr)
  }
}

/// used to integrate str's parse() method
pub trait ParseTo<R> {
  fn parse_to(&self) -> Option<R>;
}

impl<'a,R: FromStr> ParseTo<R> for &'a[u8] {
  fn parse_to(&self) -> Option<R> {
    from_utf8(self).ok().and_then(|s| s.parse().ok())
  }
}

impl<'a,R:FromStr> ParseTo<R> for &'a str {
  fn parse_to(&self) -> Option<R> {
    self.parse().ok()
  }
}

/// slicing operations using ranges
///
/// this trait is loosely based on
/// `Index`, but can actually return
/// something else than a `&[T]` or `&str`
pub trait Slice<R> {
  #[inline(always)]
  fn slice(&self, range: R) -> Self;
}

macro_rules! impl_fn_slice {
    ( $ty:ty ) => {
        fn slice(&self, range:$ty) -> Self {
            &self[range]
        }
    }
}

macro_rules! slice_range_impl {
    ( [ $for_type:ident ], $ty:ty ) => {
        impl<'a, $for_type> Slice<$ty> for &'a [$for_type] {
            impl_fn_slice!( $ty );
        }
    };
    ( $for_type:ty, $ty:ty ) => {
        impl<'a> Slice<$ty> for &'a $for_type {
            impl_fn_slice!( $ty );
        }
    }
}

macro_rules! slice_ranges_impl {
    ( [ $for_type:ident ] ) => {
        slice_range_impl! {[$for_type], Range<usize>}
        slice_range_impl! {[$for_type], RangeTo<usize>}
        slice_range_impl! {[$for_type], RangeFrom<usize>}
        slice_range_impl! {[$for_type], RangeFull}
    };
    ( $for_type:ty ) => {
        slice_range_impl! {$for_type, Range<usize>}
        slice_range_impl! {$for_type, RangeTo<usize>}
        slice_range_impl! {$for_type, RangeFrom<usize>}
        slice_range_impl! {$for_type, RangeFull}
    }
}

slice_ranges_impl! {str}
slice_ranges_impl! {[T]}


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
