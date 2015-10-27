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

pub fn error_to_list<P>(e:&Err<P>) -> Vec<ErrorKind> {
  let mut v:Vec<ErrorKind> = Vec::new();
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

pub fn compare_error_paths<P>(e1:&Err<P>, e2:&Err<P>) -> bool {
  error_to_list(e1) == error_to_list(e2)
}

#[cfg(not(feature = "core"))]
pub fn add_error_pattern<'a,I,O>(h: &mut HashMap<Vec<ErrorKind>, &'a str>, res: IResult<I,O>, message: &'a str) -> bool {
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
pub fn prepare_errors<O>(input: &[u8], res: IResult<&[u8],O>) -> Option<Vec<(ErrorKind, usize, usize)> > {
  if let IResult::Error(e) = res {
    let mut v:Vec<(ErrorKind, usize, usize)> = Vec::new();
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
pub fn print_error<O>(input: &[u8], res: IResult<&[u8],O>) {
  if let Some(v) = prepare_errors(input, res) {
    let colors = generate_colors(&v);
    println!("parser codes: {}",   print_codes(colors, HashMap::new()));
    println!("{}",   print_offsets(input, 0, &v));

  } else {
    println!("not an error");
  }
}

#[cfg(not(feature = "core"))]
pub fn generate_colors(v: &[(ErrorKind, usize, usize)]) -> HashMap<u32, u8> {
  let mut h: HashMap<u32, u8> = HashMap::new();
  let mut color = 0;

  for &(ref c,_,_) in v.iter() {
    h.insert(error_to_u32(c), color + 31);
    color = color + 1 % 7;
  }

  h
}

pub fn code_from_offset(v: &[(ErrorKind, usize, usize)], offset: usize) -> Option<u32> {
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
pub fn print_offsets(input: &[u8], from: usize, offsets: &[(ErrorKind, usize, usize)]) -> String {
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
  Tag,
  MapRes,
  MapOpt,
  Alt,
  IsNot,
  IsA,
  Filter,
  SeparatedList,
  SeparatedNonEmptyList,
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
  Custom(E)
}

pub fn error_to_u32(e: &ErrorKind) -> u32 {
  match *e {
    ErrorKind::Tag                       => 0,
    ErrorKind::MapRes                    => 1,
    ErrorKind::MapOpt                    => 2,
    ErrorKind::Alt                       => 3,
    ErrorKind::IsNot                     => 4,
    ErrorKind::IsA                       => 5,
    ErrorKind::Filter                    => 6,
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
    ErrorKind::Custom(_)                 => 48
  }
}
