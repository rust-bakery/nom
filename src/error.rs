//! Error management
//!
//! Parsers are generic over their error type, requiring that it implements
//! the `error::ParseContext<Input>` trait.

use crate::internal::Parser;
use crate::lib::std::fmt;

/// This trait must be implemented by the error type of a nom parser.
///
/// There are already implementations of it for `(Input, ParserKind)`
/// and `VerboseContext<Input>`.
///
/// It provides methods to create an error from some combinators,
/// and combine existing errors in combinators like `alt`.
pub trait ParseContext<I>: Sized {
  /// Creates an error from the input position and an [ParserKind]
  fn from_parser_kind(input: I, kind: ParserKind) -> Self;

  /// Combines an existing error with a new one created from the input
  /// position and an [ParserKind]. This is useful when backtracking
  /// through a parse tree, accumulating error context on the way
  fn append(input: I, kind: ParserKind, other: Self) -> Self;

  /// Creates an error from an input position and an expected character
  fn from_char(input: I, _: char) -> Self {
    Self::from_parser_kind(input, ParserKind::Char)
  }

  /// Combines two existing errors. This function is used to compare errors
  /// generated in various branches of `alt`.
  fn or(self, other: Self) -> Self {
    other
  }
}

/// This trait is required by the `context` combinator to add a static string
/// to an existing error
pub trait ContextError<I>: Sized {
  /// Creates a new error from an input position, a static string and an existing error.
  /// This is used mainly in the [context] combinator, to add user friendly information
  /// to errors when backtracking through a parse tree
  fn add_context(_input: I, _ctx: &'static str, other: Self) -> Self {
    other
  }
}

/// This trait is required by the `map_res` combinator to integrate
/// error types from external functions, like [std::str::FromStr]
pub trait FromExternalError<I, E> {
  /// Creates a new error from an input position, an [ParserKind] indicating the
  /// wrapping parser, and an external error
  fn from_external_error(input: I, kind: ParserKind, e: E) -> Self;
}

/// default error type, only contains the error' location and code
#[derive(Debug, PartialEq)]
pub struct Context<I> {
  /// position of the error in the input data
  pub input: I,
  /// nom error code
  pub code: ParserKind,
}

impl<I> Context<I> {
  /// creates a new basic error
  pub fn new(input: I, code: ParserKind) -> Context<I> {
    Context { input, code }
  }
}

impl<I> ParseContext<I> for Context<I> {
  fn from_parser_kind(input: I, kind: ParserKind) -> Self {
    Context { input, code: kind }
  }

  fn append(_: I, _: ParserKind, other: Self) -> Self {
    other
  }
}

impl<I> ContextError<I> for Context<I> {}

impl<I, E> FromExternalError<I, E> for Context<I> {
  /// Create a new error from an input position and an external error
  fn from_external_error(input: I, kind: ParserKind, _e: E) -> Self {
    Context { input, code: kind }
  }
}

/// The Display implementation allows the std::error::Error implementation
impl<I: fmt::Display> fmt::Display for Context<I> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "error {:?} at: {}", self.code, self.input)
  }
}

#[cfg(feature = "std")]
impl<I: fmt::Debug + fmt::Display> std::error::Error for Context<I> {}

// for backward compatibility, keep those trait implementations
// for the previously used error type
impl<I> ParseContext<I> for (I, ParserKind) {
  fn from_parser_kind(input: I, kind: ParserKind) -> Self {
    (input, kind)
  }

  fn append(_: I, _: ParserKind, other: Self) -> Self {
    other
  }
}

impl<I> ContextError<I> for (I, ParserKind) {}

impl<I, E> FromExternalError<I, E> for (I, ParserKind) {
  fn from_external_error(input: I, kind: ParserKind, _e: E) -> Self {
    (input, kind)
  }
}

impl<I> ParseContext<I> for () {
  fn from_parser_kind(_: I, _: ParserKind) -> Self {}

  fn append(_: I, _: ParserKind, _: Self) -> Self {}
}

impl<I> ContextError<I> for () {}

impl<I, E> FromExternalError<I, E> for () {
  fn from_external_error(_input: I, _kind: ParserKind, _e: E) -> Self {}
}

/// Creates an error from the input position and an [ParserKind]
pub fn make_error<I, E: ParseContext<I>>(input: I, kind: ParserKind) -> E {
  E::from_parser_kind(input, kind)
}

/// Combines an existing error with a new one created from the input
/// position and an [ParserKind]. This is useful when backtracking
/// through a parse tree, accumulating error context on the way
pub fn append_error<I, E: ParseContext<I>>(input: I, kind: ParserKind, other: E) -> E {
  E::append(input, kind, other)
}

/// This error type accumulates errors and their position when backtracking
/// through a parse tree. With some post processing (cf `examples/json.rs`),
/// it can be used to display user friendly error messages
#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
#[derive(Clone, Debug, PartialEq)]
pub struct VerboseContext<I> {
  /// List of errors accumulated by `VerboseContext`, containing the affected
  /// part of input data, and some context
  pub errors: crate::lib::std::vec::Vec<(I, VerboseParserKind)>,
}

#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
#[derive(Clone, Debug, PartialEq)]
/// Error context for `VerboseContext`
pub enum VerboseParserKind {
  /// Static string added by the `context` function
  Context(&'static str),
  /// Indicates which character was expected by the `char` function
  Char(char),
  /// Error kind given by various nom parsers
  Nom(ParserKind),
}

#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
impl<I> ParseContext<I> for VerboseContext<I> {
  fn from_parser_kind(input: I, kind: ParserKind) -> Self {
    VerboseContext {
      errors: vec![(input, VerboseParserKind::Nom(kind))],
    }
  }

  fn append(input: I, kind: ParserKind, mut other: Self) -> Self {
    other.errors.push((input, VerboseParserKind::Nom(kind)));
    other
  }

  fn from_char(input: I, c: char) -> Self {
    VerboseContext {
      errors: vec![(input, VerboseParserKind::Char(c))],
    }
  }
}

#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
impl<I> ContextError<I> for VerboseContext<I> {
  fn add_context(input: I, ctx: &'static str, mut other: Self) -> Self {
    other.errors.push((input, VerboseParserKind::Context(ctx)));
    other
  }
}

#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
impl<I, E> FromExternalError<I, E> for VerboseContext<I> {
  /// Create a new error from an input position and an external error
  fn from_external_error(input: I, kind: ParserKind, _e: E) -> Self {
    Self::from_parser_kind(input, kind)
  }
}

#[cfg(feature = "alloc")]
impl<I: fmt::Display> fmt::Display for VerboseContext<I> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    writeln!(f, "Parse error:")?;
    for (input, error) in &self.errors {
      match error {
        VerboseParserKind::Nom(e) => writeln!(f, "{:?} at: {}", e, input)?,
        VerboseParserKind::Char(c) => writeln!(f, "expected '{}' at: {}", c, input)?,
        VerboseParserKind::Context(s) => writeln!(f, "in section '{}', at: {}", s, input)?,
      }
    }

    Ok(())
  }
}

#[cfg(feature = "std")]
impl<I: fmt::Debug + fmt::Display> std::error::Error for VerboseContext<I> {}

use crate::internal::{Outcome, ParseResult};

/// Create a new error from an input position, a static string and an existing error.
/// This is used mainly in the [context] combinator, to add user friendly information
/// to errors when backtracking through a parse tree
pub fn context<I: Clone, E: ContextError<I>, F, O>(
  context: &'static str,
  mut f: F,
) -> impl FnMut(I) -> ParseResult<I, O, E>
where
  F: Parser<I, O, E>,
{
  move |i: I| match f.parse(i.clone()) {
    Ok(o) => Ok(o),
    Err(Outcome::Incomplete(i)) => Err(Outcome::Incomplete(i)),
    Err(Outcome::Failure(e)) => Err(Outcome::Failure(E::add_context(i, context, e))),
    Err(Outcome::Invalid(e)) => Err(Outcome::Invalid(E::add_context(i, context, e))),
  }
}

/// Transforms a `VerboseContext` into a trace with input position information
#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
pub fn convert_error<I: core::ops::Deref<Target = str>>(
  input: I,
  e: VerboseContext<I>,
) -> crate::lib::std::string::String {
  use crate::lib::std::fmt::Write;
  use crate::traits::Offset;

  let mut result = crate::lib::std::string::String::new();

  for (i, (substring, kind)) in e.errors.iter().enumerate() {
    let offset = input.offset(substring);

    if input.is_empty() {
      match kind {
        VerboseParserKind::Char(c) => {
          write!(&mut result, "{}: expected '{}', got empty input\n\n", i, c)
        }
        VerboseParserKind::Context(s) => {
          write!(&mut result, "{}: in {}, got empty input\n\n", i, s)
        }
        VerboseParserKind::Nom(e) => write!(&mut result, "{}: in {:?}, got empty input\n\n", i, e),
      }
    } else {
      let prefix = &input.as_bytes()[..offset];

      // Count the number of newlines in the first `offset` bytes of input
      let line_number = prefix.iter().filter(|&&b| b == b'\n').count() + 1;

      // Find the line that includes the subslice:
      // Find the *last* newline before the substring starts
      let line_begin = prefix
        .iter()
        .rev()
        .position(|&b| b == b'\n')
        .map(|pos| offset - pos)
        .unwrap_or(0);

      // Find the full line after that newline
      let line = input[line_begin..]
        .lines()
        .next()
        .unwrap_or(&input[line_begin..])
        .trim_end();

      // The (1-indexed) column number is the offset of our substring into that line
      let column_number = line.offset(substring) + 1;

      match kind {
        VerboseParserKind::Char(c) => {
          if let Some(actual) = substring.chars().next() {
            write!(
              &mut result,
              "{i}: at line {line_number}:\n\
               {line}\n\
               {caret:>column$}\n\
               expected '{expected}', found {actual}\n\n",
              i = i,
              line_number = line_number,
              line = line,
              caret = '^',
              column = column_number,
              expected = c,
              actual = actual,
            )
          } else {
            write!(
              &mut result,
              "{i}: at line {line_number}:\n\
               {line}\n\
               {caret:>column$}\n\
               expected '{expected}', got end of input\n\n",
              i = i,
              line_number = line_number,
              line = line,
              caret = '^',
              column = column_number,
              expected = c,
            )
          }
        }
        VerboseParserKind::Context(s) => write!(
          &mut result,
          "{i}: at line {line_number}, in {context}:\n\
             {line}\n\
             {caret:>column$}\n\n",
          i = i,
          line_number = line_number,
          context = s,
          line = line,
          caret = '^',
          column = column_number,
        ),
        VerboseParserKind::Nom(e) => write!(
          &mut result,
          "{i}: at line {line_number}, in {nom_err:?}:\n\
             {line}\n\
             {caret:>column$}\n\n",
          i = i,
          line_number = line_number,
          nom_err = e,
          line = line,
          caret = '^',
          column = column_number,
        ),
      }
    }
    // Because `write!` to a `String` is infallible, this `unwrap` is fine.
    .unwrap();
  }

  result
}

/// Indicates which parser returned an error
#[rustfmt::skip]
#[derive(Debug,PartialEq,Eq,Hash,Clone,Copy)]
#[allow(deprecated,missing_docs)]
pub enum ParserKind {
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
  TakeUntil,
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
  NonEmpty,
  ManyMN,
  Not,
  Permutation,
  Verify,
  TakeTill1,
  TakeWhileMN,
  TooLarge,
  Many0Count,
  Many1Count,
  Float,
  Satisfy,
  Fail,
}

#[rustfmt::skip]
#[allow(deprecated)]
/// Converts an ParserKind to a number
pub fn error_to_u32(e: &ParserKind) -> u32 {
  match *e {
    ParserKind::Tag                       => 1,
    ParserKind::MapRes                    => 2,
    ParserKind::MapOpt                    => 3,
    ParserKind::Alt                       => 4,
    ParserKind::IsNot                     => 5,
    ParserKind::IsA                       => 6,
    ParserKind::SeparatedList             => 7,
    ParserKind::SeparatedNonEmptyList     => 8,
    ParserKind::Many1                     => 9,
    ParserKind::Count                     => 10,
    ParserKind::TakeUntil                 => 12,
    ParserKind::LengthValue               => 15,
    ParserKind::TagClosure                => 16,
    ParserKind::Alpha                     => 17,
    ParserKind::Digit                     => 18,
    ParserKind::AlphaNumeric              => 19,
    ParserKind::Space                     => 20,
    ParserKind::MultiSpace                => 21,
    ParserKind::LengthValueFn             => 22,
    ParserKind::Eof                       => 23,
    ParserKind::Switch                    => 27,
    ParserKind::TagBits                   => 28,
    ParserKind::OneOf                     => 29,
    ParserKind::NoneOf                    => 30,
    ParserKind::Char                      => 40,
    ParserKind::CrLf                      => 41,
    ParserKind::RegexpMatch               => 42,
    ParserKind::RegexpMatches             => 43,
    ParserKind::RegexpFind                => 44,
    ParserKind::RegexpCapture             => 45,
    ParserKind::RegexpCaptures            => 46,
    ParserKind::TakeWhile1                => 47,
    ParserKind::Complete                  => 48,
    ParserKind::Fix                       => 49,
    ParserKind::Escaped                   => 50,
    ParserKind::EscapedTransform          => 51,
    ParserKind::NonEmpty                  => 56,
    ParserKind::ManyMN                    => 57,
    ParserKind::HexDigit                  => 59,
    ParserKind::OctDigit                  => 61,
    ParserKind::Many0                     => 62,
    ParserKind::Not                       => 63,
    ParserKind::Permutation               => 64,
    ParserKind::ManyTill                  => 65,
    ParserKind::Verify                    => 66,
    ParserKind::TakeTill1                 => 67,
    ParserKind::TakeWhileMN               => 69,
    ParserKind::TooLarge                  => 70,
    ParserKind::Many0Count                => 71,
    ParserKind::Many1Count                => 72,
    ParserKind::Float                     => 73,
    ParserKind::Satisfy                   => 74,
    ParserKind::Fail                      => 75,
  }
}

impl ParserKind {
  #[rustfmt::skip]
  #[allow(deprecated)]
  /// Converts an ParserKind to a text description
  pub fn description(&self) -> &str {
    match *self {
      ParserKind::Tag                       => "Tag",
      ParserKind::MapRes                    => "Map on Result",
      ParserKind::MapOpt                    => "Map on Option",
      ParserKind::Alt                       => "Alternative",
      ParserKind::IsNot                     => "IsNot",
      ParserKind::IsA                       => "IsA",
      ParserKind::SeparatedList             => "Separated list",
      ParserKind::SeparatedNonEmptyList     => "Separated non empty list",
      ParserKind::Many0                     => "Many0",
      ParserKind::Many1                     => "Many1",
      ParserKind::Count                     => "Count",
      ParserKind::TakeUntil                 => "Take until",
      ParserKind::LengthValue               => "Length followed by value",
      ParserKind::TagClosure                => "Tag closure",
      ParserKind::Alpha                     => "Alphabetic",
      ParserKind::Digit                     => "Digit",
      ParserKind::AlphaNumeric              => "AlphaNumeric",
      ParserKind::Space                     => "Space",
      ParserKind::MultiSpace                => "Multiple spaces",
      ParserKind::LengthValueFn             => "LengthValueFn",
      ParserKind::Eof                       => "End of file",
      ParserKind::Switch                    => "Switch",
      ParserKind::TagBits                   => "Tag on bitstream",
      ParserKind::OneOf                     => "OneOf",
      ParserKind::NoneOf                    => "NoneOf",
      ParserKind::Char                      => "Char",
      ParserKind::CrLf                      => "CrLf",
      ParserKind::RegexpMatch               => "RegexpMatch",
      ParserKind::RegexpMatches             => "RegexpMatches",
      ParserKind::RegexpFind                => "RegexpFind",
      ParserKind::RegexpCapture             => "RegexpCapture",
      ParserKind::RegexpCaptures            => "RegexpCaptures",
      ParserKind::TakeWhile1                => "TakeWhile1",
      ParserKind::Complete                  => "Complete",
      ParserKind::Fix                       => "Fix",
      ParserKind::Escaped                   => "Escaped",
      ParserKind::EscapedTransform          => "EscapedTransform",
      ParserKind::NonEmpty                  => "NonEmpty",
      ParserKind::ManyMN                    => "Many(m, n)",
      ParserKind::HexDigit                  => "Hexadecimal Digit",
      ParserKind::OctDigit                  => "Octal digit",
      ParserKind::Not                       => "Negation",
      ParserKind::Permutation               => "Permutation",
      ParserKind::ManyTill                  => "ManyTill",
      ParserKind::Verify                    => "predicate verification",
      ParserKind::TakeTill1                 => "TakeTill1",
      ParserKind::TakeWhileMN               => "TakeWhileMN",
      ParserKind::TooLarge                  => "Needed data size is too large",
      ParserKind::Many0Count                => "Count occurrence of >=0 patterns",
      ParserKind::Many1Count                => "Count occurrence of >=1 patterns",
      ParserKind::Float                     => "Float",
      ParserKind::Satisfy                   => "Satisfy",
      ParserKind::Fail                      => "Fail",
    }
  }
}

/// Creates a parse error from a `nom::ParserKind`
/// and the position in the input
#[allow(unused_variables)]
#[macro_export(local_inner_macros)]
macro_rules! error_position(
  ($input:expr, $code:expr) => ({
    $crate::error::make_error($input, $code)
  });
);

/// Creates a parse error from a `nom::ParserKind`,
/// the position in the input and the next error in
/// the parsing tree
#[allow(unused_variables)]
#[macro_export(local_inner_macros)]
macro_rules! error_node_position(
  ($input:expr, $code:expr, $next:expr) => ({
    $crate::error::append_error($input, $code, $next)
  });
);

/// Prints a message and the input if the parser fails.
///
/// The message prints the `Error` or `Incomplete`
/// and the parser's calling code.
///
/// It also displays the input in hexdump format
///
/// ```rust
/// use nom::{ParseResult, error::dbg_dmp, bytes::complete::tag};
///
/// fn f(i: &[u8]) -> ParseResult<&[u8], &[u8]> {
///   dbg_dmp(tag("abcd"), "tag")(i)
/// }
///
///   let a = &b"efghijkl"[..];
///
/// // Will print the following message:
/// // Error(Position(0, [101, 102, 103, 104, 105, 106, 107, 108])) at l.5 by ' tag ! ( "abcd" ) '
/// // 00000000        65 66 67 68 69 6a 6b 6c         efghijkl
/// f(a);
/// ```
#[cfg(feature = "std")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "std")))]
pub fn dbg_dmp<'a, F, O, E: std::fmt::Debug>(
  f: F,
  context: &'static str,
) -> impl Fn(&'a [u8]) -> ParseResult<&'a [u8], O, E>
where
  F: Fn(&'a [u8]) -> ParseResult<&'a [u8], O, E>,
{
  use crate::HexDisplay;
  move |i: &'a [u8]| match f(i) {
    Err(e) => {
      println!("{}: Error({:?}) at:\n{}", context, e, i.to_hex(8));
      Err(e)
    }
    a => a,
  }
}

#[cfg(test)]
#[cfg(feature = "alloc")]
mod tests {
  use super::*;
  use crate::character::complete::char;

  #[test]
  fn convert_error_panic() {
    let input = "";

    let _result: ParseResult<_, _, VerboseContext<&str>> = char('x')(input);
  }
}

/*
#[cfg(feature = "alloc")]
use lib::std::{vec::Vec, collections::HashMap};

#[cfg(feature = "std")]
use lib::std::hash::Hash;

#[cfg(feature = "std")]
pub fn add_error_pattern<'a, I: Clone + Hash + Eq, O, E: Clone + Hash + Eq>(
  h: &mut HashMap<VerboseContext<I>, &'a str>,
  e: VerboseContext<I>,
  message: &'a str,
) -> bool {
  h.insert(e, message);
  true
}

pub fn slice_to_offsets(input: &[u8], s: &[u8]) -> (usize, usize) {
  let start = input.as_ptr();
  let off1 = s.as_ptr() as usize - start as usize;
  let off2 = off1 + s.len();
  (off1, off2)
}

#[cfg(feature = "std")]
pub fn prepare_errors<O, E: Clone>(input: &[u8], e: VerboseContext<&[u8]>) -> Option<Vec<(ParserKind, usize, usize)>> {
  let mut v: Vec<(ParserKind, usize, usize)> = Vec::new();

  for (p, kind) in e.errors.drain(..) {
    let (o1, o2) = slice_to_offsets(input, p);
    v.push((kind, o1, o2));
  }

  v.reverse();
  Some(v)
}

#[cfg(feature = "std")]
pub fn print_error<O, E: Clone>(input: &[u8], res: VerboseContext<&[u8]>) {
  if let Some(v) = prepare_errors(input, res) {
    let colors = generate_colors(&v);
    println!("parser codes: {}", print_codes(&colors, &HashMap::new()));
    println!("{}", print_offsets(input, 0, &v));
  } else {
    println!("not an error");
  }
}

#[cfg(feature = "std")]
pub fn generate_colors<E>(v: &[(ParserKind, usize, usize)]) -> HashMap<u32, u8> {
  let mut h: HashMap<u32, u8> = HashMap::new();
  let mut color = 0;

  for &(ref c, _, _) in v.iter() {
    h.insert(error_to_u32(c), color + 31);
    color = color + 1 % 7;
  }

  h
}

pub fn code_from_offset(v: &[(ParserKind, usize, usize)], offset: usize) -> Option<u32> {
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
pub fn print_offsets(input: &[u8], from: usize, offsets: &[(ParserKind, usize, usize)]) -> String {
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
*/
