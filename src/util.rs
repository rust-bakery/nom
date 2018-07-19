#[cfg(feature = "verbose-errors")]
#[cfg(feature = "std")]
use internal::{Err, IResult};
#[cfg(feature = "verbose-errors")]
use verbose_errors::Context;

#[cfg(feature = "std")]
use std::collections::HashMap;

#[cfg(feature = "alloc")]
use lib::std::string::ToString;
#[cfg(feature = "alloc")]
use lib::std::vec::Vec;

#[cfg(feature = "std")]
pub trait HexDisplay {
  /// Converts the value of `self` to a hex dump, returning the owned
  /// string.
  fn to_hex(&self, chunk_size: usize) -> String;

  /// Converts the value of `self` to a hex dump beginning at `from` address, returning the owned
  /// string.
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String;
}

#[cfg(feature = "std")]
static CHARS: &'static [u8] = b"0123456789abcdef";

#[cfg(feature = "std")]
impl HexDisplay for [u8] {
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
      v.push(b'\t');

      i += chunk_size;

      for &byte in chunk {
        v.push(CHARS[(byte >> 4) as usize]);
        v.push(CHARS[(byte & 0xf) as usize]);
        v.push(b' ');
      }
      if chunk_size > chunk.len() {
        for j in 0..(chunk_size - chunk.len()) {
          v.push(b' ');
          v.push(b' ');
          v.push(b' ');
        }
      }
      v.push(b'\t');

      for &byte in chunk {
        if (byte >= 32 && byte <= 126) || byte >= 128 {
          v.push(byte);
        } else {
          v.push(b'.');
        }
      }
      v.push(b'\n');
    }

    String::from_utf8_lossy(&v[..]).into_owned()
  }
}

#[cfg(feature = "std")]
impl HexDisplay for str {
  #[allow(unused_variables)]
  fn to_hex(&self, chunk_size: usize) -> String {
    self.to_hex_from(chunk_size, 0)
  }

  #[allow(unused_variables)]
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
    self.as_bytes().to_hex_from(chunk_size, from)
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
      use $crate::lib::std::result::Result::*;
      let l = line!();
      match $submac!($i, $($args)*) {
        Err(e) => {
          println!("Err({:?}) at l.{} by ' {} '", e, l, stringify!($submac!($($args)*)));
          Err(e)
        },
        a => a,
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
/// ```ignore
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
        Err(e) => {
          println!("Error({:?}) at l.{} by ' {} '\n{}", e, l, stringify!($submac!($($args)*)), $i.to_hex(8));
          Err(e)
        },
        a => a,
      }
    }
  );

  ($i:expr, $f:ident) => (
      dbg_dmp!($i, call!($f));
  );
);

#[cfg(feature = "verbose-errors")]
pub fn error_to_list<P: Clone, E: Clone>(e: &Context<P, E>) -> Vec<(P, ErrorKind<E>)> {
  match e {
    &Context::Code(ref i, ref err) => {
      let mut v = Vec::new();
      v.push((i.clone(), err.clone()));
      return v;
    }
    &Context::List(ref v) => {
      let mut v2 = v.clone();
      v2.reverse();
      v2
    }
  }
}

#[cfg(feature = "verbose-errors")]
pub fn compare_error_paths<P: Clone + PartialEq, E: Clone + PartialEq>(e1: &Context<P, E>, e2: &Context<P, E>) -> bool {
  error_to_list(e1) == error_to_list(e2)
}

#[cfg(feature = "std")]
#[cfg(feature = "verbose-errors")]
use lib::std::hash::Hash;

#[cfg(feature = "std")]
#[cfg(feature = "verbose-errors")]
pub fn add_error_pattern<'a, I: Clone + Hash + Eq, O, E: Clone + Hash + Eq>(
  h: &mut HashMap<Vec<(I, ErrorKind<E>)>, &'a str>,
  res: IResult<I, O, E>,
  message: &'a str,
) -> bool {
  match res {
    Err(Err::Error(e)) | Err(Err::Failure(e)) => {
      h.insert(error_to_list(&e), message);
      true
    }
    _ => false,
  }
}

pub fn slice_to_offsets(input: &[u8], s: &[u8]) -> (usize, usize) {
  let start = input.as_ptr();
  let off1 = s.as_ptr() as usize - start as usize;
  let off2 = off1 + s.len();
  (off1, off2)
}

#[cfg(feature = "std")]
#[cfg(feature = "verbose-errors")]
pub fn prepare_errors<O, E: Clone>(input: &[u8], res: IResult<&[u8], O, E>) -> Option<Vec<(ErrorKind<E>, usize, usize)>> {
  if let Err(Err::Error(e)) = res {
    let mut v: Vec<(ErrorKind<E>, usize, usize)> = Vec::new();

    match e {
      Context::Code(p, kind) => {
        let (o1, o2) = slice_to_offsets(input, p);
        v.push((kind, o1, o2));
      }
      Context::List(mut l) => {
        for (p, kind) in l.drain(..) {
          let (o1, o2) = slice_to_offsets(input, p);
          v.push((kind, o1, o2));
        }

        v.reverse()
      }
    }

    v.sort_by(|a, b| a.1.cmp(&b.1));
    Some(v)
  } else {
    None
  }
}

#[cfg(feature = "std")]
#[cfg(feature = "verbose-errors")]
pub fn print_error<O, E: Clone>(input: &[u8], res: IResult<&[u8], O, E>) {
  if let Some(v) = prepare_errors(input, res) {
    let colors = generate_colors(&v);
    println!("parser codes: {}", print_codes(&colors, &HashMap::new()));
    println!("{}", print_offsets(input, 0, &v));
  } else {
    println!("not an error");
  }
}

#[cfg(feature = "std")]
#[cfg(feature = "verbose-errors")]
pub fn generate_colors<E>(v: &[(ErrorKind<E>, usize, usize)]) -> HashMap<u32, u8> {
  let mut h: HashMap<u32, u8> = HashMap::new();
  let mut color = 0;

  for &(ref c, _, _) in v.iter() {
    h.insert(error_to_u32(c), color + 31);
    color = color + 1 % 7;
  }

  h
}

pub fn code_from_offset<E>(v: &[(ErrorKind<E>, usize, usize)], offset: usize) -> Option<u32> {
  let mut acc: Option<(u32, usize, usize)> = None;
  for &(ref ek, s, e) in v.iter() {
    let c = error_to_u32(ek);
    if s <= offset && offset <= e {
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

#[cfg(feature = "alloc")]
pub fn reset_color(v: &mut Vec<u8>) {
  v.push(0x1B);
  v.push(b'[');
  v.push(0);
  v.push(b'm');
}

#[cfg(feature = "alloc")]
pub fn write_color(v: &mut Vec<u8>, color: u8) {
  v.push(0x1B);
  v.push(b'[');
  v.push(1);
  v.push(b';');
  let s = color.to_string();
  let bytes = s.as_bytes();
  v.extend(bytes.iter().cloned());
  v.push(b'm');
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "cargo-clippy", allow(implicit_hasher))]
pub fn print_codes(colors: &HashMap<u32, u8>, names: &HashMap<u32, &str>) -> String {
  let mut v = Vec::new();
  for (code, &color) in colors {
    if let Some(&s) = names.get(code) {
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
    v.push(b' ');
  }
  reset_color(&mut v);

  String::from_utf8_lossy(&v[..]).into_owned()
}

#[cfg(feature = "std")]
#[cfg(feature = "verbose-errors")]
pub fn print_offsets<E>(input: &[u8], from: usize, offsets: &[(ErrorKind<E>, usize, usize)]) -> String {
  let mut v = Vec::with_capacity(input.len() * 3);
  let mut i = from;
  let chunk_size = 8;
  let mut current_code: Option<u32> = None;
  let mut current_code2: Option<u32> = None;

  let colors = generate_colors(&offsets);

  for chunk in input.chunks(chunk_size) {
    let s = format!("{:08x}", i);
    for &ch in s.as_bytes().iter() {
      v.push(ch);
    }
    v.push(b'\t');

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
      v.push(b' ');
      k = k + 1;
    }

    reset_color(&mut v);

    if chunk_size > chunk.len() {
      for _ in 0..(chunk_size - chunk.len()) {
        v.push(b' ');
        v.push(b' ');
        v.push(b' ');
      }
    }
    v.push(b'\t');

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
      if (byte >= 32 && byte <= 126) || byte >= 128 {
        v.push(byte);
      } else {
        v.push(b'.');
      }
      l = l + 1;
    }
    reset_color(&mut v);

    v.push(b'\n');
    i = i + chunk_size;
  }

  String::from_utf8_lossy(&v[..]).into_owned()
}

/// indicates which parser returned an error
#[cfg_attr(rustfmt, rustfmt_skip)]
#[derive(Debug,PartialEq,Eq,Hash,Clone)]
#[allow(deprecated)]
pub enum ErrorKind<E = u32> {
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
  ManyTill,
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
  #[deprecated(since = "4.0.0", note = "Please use `Tag` instead")]
  TagStr,
  #[deprecated(since = "4.0.0", note = "Please use `IsNot` instead")]
  IsNotStr,
  #[deprecated(since = "4.0.0", note = "Please use `IsA` instead")]
  IsAStr,
  #[deprecated(since = "4.0.0", note = "Please use `TakeWhile1` instead")]
  TakeWhile1Str,
  NonEmpty,
  ManyMN,
  #[deprecated(since = "4.0.0", note = "Please use `TakeUntilAndConsume` instead")]
  TakeUntilAndConsumeStr,
  #[deprecated(since = "4.0.0", note = "Please use `TakeUntil` instead")]
  TakeUntilStr,
  Not,
  Permutation,
  Verify,
  TakeTill1,
  TakeUntilAndConsume1,
  TakeWhileMN,
  ParseTo,
}

#[cfg_attr(rustfmt, rustfmt_skip)]
#[allow(deprecated)]
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
    ErrorKind::Permutation               => 64,
    ErrorKind::ManyTill                  => 65,
    ErrorKind::Verify                    => 66,
    ErrorKind::TakeTill1                 => 67,
    ErrorKind::TakeUntilAndConsume1      => 68,
    ErrorKind::TakeWhileMN               => 69,
    ErrorKind::ParseTo                   => 70,
  }
}

impl<E> ErrorKind<E> {
  #[cfg_attr(rustfmt, rustfmt_skip)]
  #[allow(deprecated)]
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
      ErrorKind::Permutation               => "Permutation",
      ErrorKind::ManyTill                  => "ManyTill",
      ErrorKind::Verify                    => "predicate verification",
      ErrorKind::TakeTill1                 => "TakeTill1",
      ErrorKind::TakeUntilAndConsume1      => "Take at least 1 until and consume",
      ErrorKind::TakeWhileMN               => "TakeWhileMN",
      ErrorKind::ParseTo                   => "Parse string to the specified type",
    }
  }

  /// Convert Err into an ErrorKind.
  ///
  /// This allows application code to use ErrorKind and stay independent from the `verbose-errors` features activation.
  pub fn into_error_kind(self) -> ErrorKind<E> {
    self
  }
}

pub trait Convert<T> {
  fn convert(T) -> Self;
}

impl<F, E: From<F>> Convert<ErrorKind<F>> for ErrorKind<E> {
  #[cfg_attr(rustfmt, rustfmt_skip)]
  #[allow(deprecated)]
  fn convert(e: ErrorKind<F>) -> Self {
    match e {
      ErrorKind::Custom(c)                 => ErrorKind::Custom(E::from(c)),
      ErrorKind::Tag                       => ErrorKind::Tag,
      ErrorKind::MapRes                    => ErrorKind::MapRes,
      ErrorKind::MapOpt                    => ErrorKind::MapOpt,
      ErrorKind::Alt                       => ErrorKind::Alt,
      ErrorKind::IsNot                     => ErrorKind::IsNot,
      ErrorKind::IsA                       => ErrorKind::IsA,
      ErrorKind::SeparatedList             => ErrorKind::SeparatedList,
      ErrorKind::SeparatedNonEmptyList     => ErrorKind::SeparatedNonEmptyList,
      ErrorKind::Many1                     => ErrorKind::Many1,
      ErrorKind::Count                     => ErrorKind::Count,
      ErrorKind::TakeUntilAndConsume       => ErrorKind::TakeUntilAndConsume,
      ErrorKind::TakeUntil                 => ErrorKind::TakeUntil,
      ErrorKind::TakeUntilEitherAndConsume => ErrorKind::TakeUntilEitherAndConsume,
      ErrorKind::TakeUntilEither           => ErrorKind::TakeUntilEither,
      ErrorKind::LengthValue               => ErrorKind::LengthValue,
      ErrorKind::TagClosure                => ErrorKind::TagClosure,
      ErrorKind::Alpha                     => ErrorKind::Alpha,
      ErrorKind::Digit                     => ErrorKind::Digit,
      ErrorKind::AlphaNumeric              => ErrorKind::AlphaNumeric,
      ErrorKind::Space                     => ErrorKind::Space,
      ErrorKind::MultiSpace                => ErrorKind::MultiSpace,
      ErrorKind::LengthValueFn             => ErrorKind::LengthValueFn,
      ErrorKind::Eof                       => ErrorKind::Eof,
      ErrorKind::ExprOpt                   => ErrorKind::ExprOpt,
      ErrorKind::ExprRes                   => ErrorKind::ExprRes,
      ErrorKind::CondReduce                => ErrorKind::CondReduce,
      ErrorKind::Switch                    => ErrorKind::Switch,
      ErrorKind::TagBits                   => ErrorKind::TagBits,
      ErrorKind::OneOf                     => ErrorKind::OneOf,
      ErrorKind::NoneOf                    => ErrorKind::NoneOf,
      ErrorKind::Char                      => ErrorKind::Char,
      ErrorKind::CrLf                      => ErrorKind::CrLf,
      ErrorKind::RegexpMatch               => ErrorKind::RegexpMatch,
      ErrorKind::RegexpMatches             => ErrorKind::RegexpMatches,
      ErrorKind::RegexpFind                => ErrorKind::RegexpFind,
      ErrorKind::RegexpCapture             => ErrorKind::RegexpCapture,
      ErrorKind::RegexpCaptures            => ErrorKind::RegexpCaptures,
      ErrorKind::TakeWhile1                => ErrorKind::TakeWhile1,
      ErrorKind::Complete                  => ErrorKind::Complete,
      ErrorKind::Fix                       => ErrorKind::Fix,
      ErrorKind::Escaped                   => ErrorKind::Escaped,
      ErrorKind::EscapedTransform          => ErrorKind::EscapedTransform,
      ErrorKind::TagStr                    => ErrorKind::TagStr,
      ErrorKind::IsNotStr                  => ErrorKind::IsNotStr,
      ErrorKind::IsAStr                    => ErrorKind::IsAStr,
      ErrorKind::TakeWhile1Str             => ErrorKind::TakeWhile1Str,
      ErrorKind::NonEmpty                  => ErrorKind::NonEmpty,
      ErrorKind::ManyMN                    => ErrorKind::ManyMN,
      ErrorKind::TakeUntilAndConsumeStr    => ErrorKind::TakeUntilAndConsumeStr,
      ErrorKind::HexDigit                  => ErrorKind::HexDigit,
      ErrorKind::TakeUntilStr              => ErrorKind::TakeUntilStr,
      ErrorKind::OctDigit                  => ErrorKind::OctDigit,
      ErrorKind::Many0                     => ErrorKind::Many0,
      ErrorKind::Not                       => ErrorKind::Not,
      ErrorKind::Permutation               => ErrorKind::Permutation,
      ErrorKind::ManyTill                  => ErrorKind::ManyTill,
      ErrorKind::Verify                    => ErrorKind::Verify,
      ErrorKind::TakeTill1                 => ErrorKind::TakeTill1,
      ErrorKind::TakeUntilAndConsume1      => ErrorKind::TakeUntilAndConsume1,
      ErrorKind::TakeWhileMN               => ErrorKind::TakeWhileMN,
      ErrorKind::ParseTo                   => ErrorKind::ParseTo,
    }
  }
}
