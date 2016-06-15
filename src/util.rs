use internal::{IResult,Err};

#[cfg(not(feature = "core"))]
use std::collections::HashMap;

#[cfg(feature = "core")]
use std::prelude::v1::*;
use std::vec::Vec;
use std::string::ToString;

/// useful functions to calculate the offset between slices and show a hexdump of a slice
#[cfg(not(feature = "core"))]
pub trait HexDisplay {
  /// offset between the first byte of self and the first byte of the argument
  fn offset(&self, second:&[u8]) -> usize;// OFFSET SHOULD GO TO ITS OWN TRAIT

  /// Converts the value of `self` to a hex dump, returning the owned
  /// string.
  fn to_hex(&self, chunk_size: usize) -> String;

  /// Converts the value of `self` to a hex dump beginning at `from` address, returning the owned
  /// string.
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String;
}

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
    fn as_char(self)     -> char;
    #[inline]
    fn is_alpha(self)    -> bool;
    #[inline]
    fn is_alphanum(self) -> bool;
    #[inline]
    fn is_0_to_9(self)   -> bool;
    #[inline]
    fn is_hex_digit(self) -> bool;
    #[inline]
    fn is_oct_digit(self) -> bool;
}

impl<'a> AsChar for &'a u8 {
    #[inline]
    fn as_char(self)     -> char { *self as char }
    #[inline]
    fn is_alpha(self)    -> bool {
      (*self >= 0x41 && *self <= 0x5A) || (*self >= 0x61 && *self <= 0x7A)
    }
    #[inline]
    fn is_alphanum(self) -> bool { self.is_alpha() || self.is_0_to_9() }
    #[inline]
    fn is_0_to_9(self)   -> bool {
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
    fn as_char(self)     -> char { self }
    #[inline]
    fn is_alpha(self)    -> bool { self.is_alphabetic() }
    #[inline]
    fn is_alphanum(self) -> bool { self.is_alpha() || self.is_0_to_9() }
    #[inline]
    fn is_0_to_9(self)   -> bool { self.is_digit(10) }
    #[inline]
    fn is_hex_digit(self) -> bool { self.is_digit(16) }
    #[inline]
    fn is_oct_digit(self) -> bool { self.is_digit(8) }
}

pub trait IterIndices {
    type Item: AsChar;
    type Iter : Iterator<Item=(usize, Self::Item)>;
    fn iter_indices(self) -> Self::Iter;
}

impl<'a> IterIndices for &'a [u8] {
    type Item = &'a u8;
    type Iter = Enumerate<::std::slice::Iter<'a, u8>>;
    #[inline]
    fn iter_indices(self) -> Enumerate<::std::slice::Iter<'a, u8>> {
        self.iter().enumerate()
    }
}

#[cfg(not(feature = "core"))]
impl<'a> IterIndices for &'a str {
    type Item = char;
    type Iter = CharIndices<'a>;
    #[inline]
    fn iter_indices(self) -> CharIndices<'a> {
        self.char_indices()
    }
}

static CHARS: &'static[u8] = b"0123456789abcdef";

#[cfg(not(feature = "core"))]
impl HexDisplay for [u8] {
  fn offset(&self, second:&[u8]) -> usize {
    let fst = self.as_ptr();
    let snd = second.as_ptr();

    snd as usize - fst as usize
  }

  #[allow(unused_variables)]
  fn to_hex(&self, chunk_size: usize) -> String {
    self.to_hex_from(chunk_size, 0)
  }

  #[allow(unused_variables)]
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
    let mut v = Vec::with_capacity(self.len() * 3);
    let mut i = from;
    for chunk in self.chunks(chunk_size) {
      let s = format!("{:08x}", i);
      for &ch in s.as_bytes().iter() {
        v.push(ch);
      }
      v.push('\t' as u8);

      i = i + chunk_size;

      for &byte in chunk {
        v.push(CHARS[(byte >> 4) as usize]);
        v.push(CHARS[(byte & 0xf) as usize]);
        v.push(' ' as u8);
      }
      if chunk_size > chunk.len() {
        for j in 0..(chunk_size - chunk.len()) {
          v.push(' ' as u8);
          v.push(' ' as u8);
          v.push(' ' as u8);
        }
      }
      v.push('\t' as u8);

      for &byte in chunk {
        if (byte >=32 && byte <= 126) || byte >= 128 {
          v.push(byte);
        } else {
          v.push('.' as u8);
        }
      }
      v.push('\n' as u8);
    }

    String::from_utf8_lossy(&v[..]).into_owned()
  }
}

/// Prints a message if the parser fails
///
/// The message prints the `Error` or `Incomplete`
/// and the parser's calling code
///
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///    named!(f, dbg!( tag!( "abcd" ) ) );
///
///    let a = &b"efgh"[..];
///
///    // Will print the following message:
///    // Error(Position(0, [101, 102, 103, 104])) at l.5 by ' tag ! ( "abcd" ) '
///    f(a);
/// # }
/// ```
#[macro_export]
macro_rules! dbg (
  ($i: expr, $submac:ident!( $($args:tt)* )) => (
    {
      let l = line!();
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(a) => {
          println!("Error({:?}) at l.{} by ' {} '", a, l, stringify!($submac!($($args)*)));
          $crate::IResult::Error(a)
        },
        $crate::IResult::Incomplete(a) => {
          println!("Incomplete({:?}) at {} by ' {} '", a, l, stringify!($submac!($($args)*)));
          $crate::IResult::Incomplete(a)
        },
        a => a
      }
    }
  );

  ($i:expr, $f:ident) => (
      dbg!($i, call!($f));
  );
);

/// Prints a message and the input if the parser fails
///
/// The message prints the `Error` or `Incomplete`
/// and the parser's calling code.
///
/// It also displays the input in hexdump format
///
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///    named!(f, dbg_dmp!( tag!( "abcd" ) ) );
///
///    let a = &b"efghijkl"[..];
///
///    // Will print the following message:
///    // Error(Position(0, [101, 102, 103, 104, 105, 106, 107, 108])) at l.5 by ' tag ! ( "abcd" ) '
///    // 00000000        65 66 67 68 69 6a 6b 6c         efghijkl
///    f(a);
/// # }
#[macro_export]
macro_rules! dbg_dmp (
  ($i: expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::HexDisplay;
      let l = line!();
      match $submac!($i, $($args)*) {
        $crate::IResult::Error(a) => {
          println!("Error({:?}) at l.{} by ' {} '\n{}", a, l, stringify!($submac!($($args)*)), $i.to_hex(8));
          $crate::IResult::Error(a)
        },
        $crate::IResult::Incomplete(a) => {
          println!("Incomplete({:?}) at {} by ' {} '\n{}", a, l, stringify!($submac!($($args)*)), $i.to_hex(8));
          $crate::IResult::Incomplete(a)
        },
        a => a
      }
    }
  );

  ($i:expr, $f:ident) => (
      dbg_dmp!($i, call!($f));
  );
);

pub fn error_to_list<P,E:Clone>(e:&Err<P,E>) -> Vec<ErrorKind<E>> {
  let mut v:Vec<ErrorKind<E>> = Vec::new();
  let mut err = e;
  loop {
    match *err {
      Err::Code(ref i) | Err::Position(ref i,_)                  => {
        v.push(i.clone());
        return v;
      },
      Err::Node(ref i, ref next) | Err::NodePosition(ref i, _, ref next) => {
        v.push(i.clone());
        err = &*next;
      }
    }
  }
}

pub fn compare_error_paths<P,E:Clone+PartialEq>(e1:&Err<P,E>, e2:&Err<P,E>) -> bool {
  error_to_list(e1) == error_to_list(e2)
}


#[cfg(not(feature = "core"))]
use std::hash::Hash;

#[cfg(not(feature = "core"))]
pub fn add_error_pattern<'a,I,O,E: Clone+Hash+Eq>(h: &mut HashMap<Vec<ErrorKind<E>>, &'a str>, res: IResult<I,O,E>, message: &'a str) -> bool {
  if let IResult::Error(e) = res {
    h.insert(error_to_list(&e), message);
    true
  } else {
    false
  }
}

pub fn slice_to_offsets(input: &[u8], s: &[u8]) -> (usize, usize) {
  let start = input.as_ptr();
  let off1  = s.as_ptr() as usize - start as usize;
  let off2  = off1 + s.len();
  (off1, off2)
}

#[cfg(not(feature = "core"))]
pub fn prepare_errors<O,E: Clone>(input: &[u8], res: IResult<&[u8],O,E>) -> Option<Vec<(ErrorKind<E>, usize, usize)> > {
  if let IResult::Error(e) = res {
    let mut v:Vec<(ErrorKind<E>, usize, usize)> = Vec::new();
    let mut err = e.clone();
    loop {
      match err {
        Err::Position(i,s)            => {
          let (o1, o2) = slice_to_offsets(input, s);
          v.push((i, o1, o2));
          //println!("v is: {:?}", v);
          break;
        },
        Err::NodePosition(i, s, next) => {
          let (o1, o2) = slice_to_offsets(input, s);
          v.push((i, o1, o2));
          err = *next;
        },
        Err::Node(_, next)            => {
          err = *next;
        },
        Err::Code(_)                  => {
          break;
        }
      }
    }
    v.sort_by(|a, b| a.1.cmp(&b.1));
    Some(v)
  } else {
    None
  }
}

#[cfg(not(feature = "core"))]
pub fn print_error<O,E:Clone>(input: &[u8], res: IResult<&[u8],O,E>) {
  if let Some(v) = prepare_errors(input, res) {
    let colors = generate_colors(&v);
    println!("parser codes: {}",   print_codes(colors, HashMap::new()));
    println!("{}",   print_offsets(input, 0, &v));

  } else {
    println!("not an error");
  }
}

#[cfg(not(feature = "core"))]
pub fn generate_colors<E>(v: &[(ErrorKind<E>, usize, usize)]) -> HashMap<u32, u8> {
  let mut h: HashMap<u32, u8> = HashMap::new();
  let mut color = 0;

  for &(ref c,_,_) in v.iter() {
    h.insert(error_to_u32(c), color + 31);
    color = color + 1 % 7;
  }

  h
}

pub fn code_from_offset<E>(v: &[(ErrorKind<E>, usize, usize)], offset: usize) -> Option<u32> {
  let mut acc: Option<(u32, usize, usize)> = None;
  for &(ref ek, s, e) in v.iter() {
    let c = error_to_u32(ek);
    if s <= offset && offset <=e {
      if let Some((_, start, end)) = acc {
        if start <= s && e <= end {
          acc = Some((c, s, e));
        }
      } else {
        acc = Some((c, s, e));
      }
    }
  }
  if let Some((code, _, _)) = acc {
    return Some(code);
  } else {
    return None;
  }
}

pub fn reset_color(v: &mut Vec<u8>) {
  v.push(0x1B);
  v.push('[' as u8);
  v.push(0);
  v.push('m' as u8);
}

pub fn write_color(v: &mut Vec<u8>, color: u8) {
  v.push(0x1B);
  v.push('[' as u8);
  v.push(1);
  v.push(';' as u8);
  let s = color.to_string();
  let bytes = s.as_bytes();
  v.extend(bytes.iter().cloned());
  v.push('m' as u8);
}

#[cfg(not(feature = "core"))]
pub fn print_codes(colors: HashMap<u32, u8>, names: HashMap<u32, &str>) -> String {
  let mut v = Vec::new();
  for (code, &color) in &colors {
    if let Some(&s) = names.get(&code) {
      let bytes = s.as_bytes();
      write_color(&mut v, color);
      v.extend(bytes.iter().cloned());
    } else {
      let s = code.to_string();
      let bytes = s.as_bytes();
      write_color(&mut v, color);
      v.extend(bytes.iter().cloned());
    }
    reset_color(&mut v);
    v.push(' ' as u8);
  }
  reset_color(&mut v);

  String::from_utf8_lossy(&v[..]).into_owned()
}

#[cfg(not(feature = "core"))]
pub fn print_offsets<E>(input: &[u8], from: usize, offsets: &[(ErrorKind<E>, usize, usize)]) -> String {
  let mut v = Vec::with_capacity(input.len() * 3);
  let mut i = from;
  let chunk_size = 8;
  let mut current_code:  Option<u32> = None;
  let mut current_code2: Option<u32> = None;

  let colors = generate_colors(&offsets);

  for chunk in input.chunks(chunk_size) {
    let s = format!("{:08x}", i);
    for &ch in s.as_bytes().iter() {
      v.push(ch);
    }
    v.push('\t' as u8);

    let mut k = i;
    let mut l = i;
    for &byte in chunk {
      if let Some(code) = code_from_offset(&offsets, k) {
        if let Some(current) = current_code {
          if current != code {
            reset_color(&mut v);
            current_code = Some(code);
            if let Some(&color) = colors.get(&code) {
              write_color(&mut v, color);
            }
          }
        } else {
          current_code = Some(code);
          if let Some(&color) = colors.get(&code) {
            write_color(&mut v, color);
          }
        }
      }
      v.push(CHARS[(byte >> 4) as usize]);
      v.push(CHARS[(byte & 0xf) as usize]);
      v.push(' ' as u8);
      k = k + 1;
    }

    reset_color(&mut v);

    if chunk_size > chunk.len() {
      for _ in 0..(chunk_size - chunk.len()) {
        v.push(' ' as u8);
        v.push(' ' as u8);
        v.push(' ' as u8);
      }
    }
    v.push('\t' as u8);

    for &byte in chunk {
      if let Some(code) = code_from_offset(&offsets, l) {
        if let Some(current) = current_code2 {
          if current != code {
            reset_color(&mut v);
            current_code2 = Some(code);
            if let Some(&color) = colors.get(&code) {
              write_color(&mut v, color);
            }
          }
        } else {
          current_code2 = Some(code);
          if let Some(&color) = colors.get(&code) {
            write_color(&mut v, color);
          }
        }
      }
      if (byte >=32 && byte <= 126) || byte >= 128 {
        v.push(byte);
      } else {
        v.push('.' as u8);
      }
      l = l + 1;
    }
    reset_color(&mut v);

    v.push('\n' as u8);
    i = i + chunk_size;
  }

  String::from_utf8_lossy(&v[..]).into_owned()
}

pub trait AsBytes {
  fn as_bytes(&self) -> &[u8];
}

impl<'a> AsBytes for &'a str {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    str::as_bytes(self)
  }
}

impl AsBytes for str {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    str::as_bytes(self)
  }
}

impl<'a> AsBytes for &'a [u8] {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    *self
  }
}

impl AsBytes for [u8] {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    self
  }
}

macro_rules! array_impls {
  ($($N:expr)+) => {
    $(
      impl<'a> AsBytes for &'a [u8; $N] {
        #[inline(always)]
        fn as_bytes(&self) -> &[u8] {
          *self
        }
      }

      impl AsBytes for [u8; $N] {
        #[inline(always)]
        fn as_bytes(&self) -> &[u8] {
          self
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

/// indicates which parser returned an error
#[derive(Debug,PartialEq,Eq,Hash,Clone)]
pub enum ErrorKind<E=u32> {
  Custom(E),
  Tag,
  MapRes,
  MapOpt,
  Alt,
  IsNot,
  IsA,
  SeparatedList,
  SeparatedNonEmptyList,
  Many0,
  Many1,
  Count,
  TakeUntilAndConsume,
  TakeUntil,
  TakeUntilEitherAndConsume,
  TakeUntilEither,
  LengthValue,
  TagClosure,
  Alpha,
  Digit,
  HexDigit,
  OctDigit,
  AlphaNumeric,
  Space,
  MultiSpace,
  LengthValueFn,
  Eof,
  ExprOpt,
  ExprRes,
  CondReduce,
  Switch,
  TagBits,
  OneOf,
  NoneOf,
  Char,
  CrLf,
  RegexpMatch,
  RegexpMatches,
  RegexpFind,
  RegexpCapture,
  RegexpCaptures,
  TakeWhile1,
  Complete,
  Fix,
  Escaped,
  EscapedTransform,
  TagStr,
  IsNotStr,
  IsAStr,
  TakeWhile1Str,
  NonEmpty,
  ManyMN,
  TakeUntilAndConsumeStr,
  TakeUntilStr,
  Not
}

pub fn error_to_u32<E>(e: &ErrorKind<E>) -> u32 {
  match *e {
    ErrorKind::Custom(_)                 => 0,
    ErrorKind::Tag                       => 1,
    ErrorKind::MapRes                    => 2,
    ErrorKind::MapOpt                    => 3,
    ErrorKind::Alt                       => 4,
    ErrorKind::IsNot                     => 5,
    ErrorKind::IsA                       => 6,
    ErrorKind::SeparatedList             => 7,
    ErrorKind::SeparatedNonEmptyList     => 8,
    ErrorKind::Many1                     => 9,
    ErrorKind::Count                     => 10,
    ErrorKind::TakeUntilAndConsume       => 11,
    ErrorKind::TakeUntil                 => 12,
    ErrorKind::TakeUntilEitherAndConsume => 13,
    ErrorKind::TakeUntilEither           => 14,
    ErrorKind::LengthValue               => 15,
    ErrorKind::TagClosure                => 16,
    ErrorKind::Alpha                     => 17,
    ErrorKind::Digit                     => 18,
    ErrorKind::AlphaNumeric              => 19,
    ErrorKind::Space                     => 20,
    ErrorKind::MultiSpace                => 21,
    ErrorKind::LengthValueFn             => 22,
    ErrorKind::Eof                       => 23,
    ErrorKind::ExprOpt                   => 24,
    ErrorKind::ExprRes                   => 25,
    ErrorKind::CondReduce                => 26,
    ErrorKind::Switch                    => 27,
    ErrorKind::TagBits                   => 28,
    ErrorKind::OneOf                     => 29,
    ErrorKind::NoneOf                    => 30,
    ErrorKind::Char                      => 40,
    ErrorKind::CrLf                      => 41,
    ErrorKind::RegexpMatch               => 42,
    ErrorKind::RegexpMatches             => 43,
    ErrorKind::RegexpFind                => 44,
    ErrorKind::RegexpCapture             => 45,
    ErrorKind::RegexpCaptures            => 46,
    ErrorKind::TakeWhile1                => 47,
    ErrorKind::Complete                  => 48,
    ErrorKind::Fix                       => 49,
    ErrorKind::Escaped                   => 50,
    ErrorKind::EscapedTransform          => 51,
    ErrorKind::TagStr                    => 52,
    ErrorKind::IsNotStr                  => 53,
    ErrorKind::IsAStr                    => 54,
    ErrorKind::TakeWhile1Str             => 55,
    ErrorKind::NonEmpty                  => 56,
    ErrorKind::ManyMN                    => 57,
    ErrorKind::TakeUntilAndConsumeStr    => 58,
    ErrorKind::HexDigit                  => 59,
    ErrorKind::TakeUntilStr              => 60,
    ErrorKind::OctDigit                  => 61,
    ErrorKind::Many0                     => 62,
    ErrorKind::Not                       => 63,
  }
}

  impl<E> ErrorKind<E> {
    pub fn description(&self) -> &str {
      match *self {
        ErrorKind::Custom(_)                 => "Custom error",
        ErrorKind::Tag                       => "Tag",
        ErrorKind::MapRes                    => "Map on Result",
        ErrorKind::MapOpt                    => "Map on Option",
        ErrorKind::Alt                       => "Alternative",
        ErrorKind::IsNot                     => "IsNot",
        ErrorKind::IsA                       => "IsA",
        ErrorKind::SeparatedList             => "Separated list",
        ErrorKind::SeparatedNonEmptyList     => "Separated non empty list",
        ErrorKind::Many0                     => "Many0",
        ErrorKind::Many1                     => "Many1",
        ErrorKind::Count                     => "Count",
        ErrorKind::TakeUntilAndConsume       => "Take until and consume",
        ErrorKind::TakeUntil                 => "Take until",
        ErrorKind::TakeUntilEitherAndConsume => "Take until either and consume",
        ErrorKind::TakeUntilEither           => "Take until either",
        ErrorKind::LengthValue               => "Length followed by value",
        ErrorKind::TagClosure                => "Tag closure",
        ErrorKind::Alpha                     => "Alphabetic",
        ErrorKind::Digit                     => "Digit",
        ErrorKind::AlphaNumeric              => "AlphaNumeric",
        ErrorKind::Space                     => "Space",
        ErrorKind::MultiSpace                => "Multiple spaces",
        ErrorKind::LengthValueFn             => "LengthValueFn",
        ErrorKind::Eof                       => "End of file",
        ErrorKind::ExprOpt                   => "Evaluate Option",
        ErrorKind::ExprRes                   => "Evaluate Result",
        ErrorKind::CondReduce                => "Condition reduce",
        ErrorKind::Switch                    => "Switch",
        ErrorKind::TagBits                   => "Tag on bitstream",
        ErrorKind::OneOf                     => "OneOf",
        ErrorKind::NoneOf                    => "NoneOf",
        ErrorKind::Char                      => "Char",
        ErrorKind::CrLf                      => "CrLf",
        ErrorKind::RegexpMatch               => "RegexpMatch",
        ErrorKind::RegexpMatches             => "RegexpMatches",
        ErrorKind::RegexpFind                => "RegexpFind",
        ErrorKind::RegexpCapture             => "RegexpCapture",
        ErrorKind::RegexpCaptures            => "RegexpCaptures",
        ErrorKind::TakeWhile1                => "TakeWhile1",
        ErrorKind::Complete                  => "Complete",
        ErrorKind::Fix                       => "Fix",
        ErrorKind::Escaped                   => "Escaped",
        ErrorKind::EscapedTransform          => "EscapedTransform",
        ErrorKind::TagStr                    => "Tag on strings",
        ErrorKind::IsNotStr                  => "IsNot on strings",
        ErrorKind::IsAStr                    => "IsA on strings",
        ErrorKind::TakeWhile1Str             => "TakeWhile1 on strings",
        ErrorKind::NonEmpty                  => "NonEmpty",
        ErrorKind::ManyMN                    => "Many(m, n)",
        ErrorKind::TakeUntilAndConsumeStr    => "Take until and consume on strings",
        ErrorKind::HexDigit                  => "Hexadecimal Digit",
        ErrorKind::TakeUntilStr              => "Take until on strings",
        ErrorKind::OctDigit                  => "Octal digit",
        ErrorKind::Not                       => "Negation",
      }

    }
  }
