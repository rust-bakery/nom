use std::fmt;

use nom::{
  error::{ContextError, ErrorKind, FromExternalError, ParseError},
  ErrorConvert,
};

/// This error type accumulates errors and their position when backtracking
/// through a parse tree. With some post processing,
/// it can be used to display user friendly error messages
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerboseError<I> {
  /// List of errors accumulated by `VerboseError`, containing the affected
  /// part of input data, and some context
  pub errors: Vec<(I, VerboseErrorKind)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// Error context for `VerboseError`
pub enum VerboseErrorKind {
  /// Static string added by the `context` function
  Context(&'static str),
  /// Indicates which character was expected by the `char` function
  Char(char),
  /// Error kind given by various nom parsers
  Nom(ErrorKind),
}

impl<I> ParseError<I> for VerboseError<I> {
  fn from_error_kind(input: I, kind: ErrorKind) -> Self {
    VerboseError {
      errors: vec![(input, VerboseErrorKind::Nom(kind))],
    }
  }

  fn append(input: I, kind: ErrorKind, mut other: Self) -> Self {
    other.errors.push((input, VerboseErrorKind::Nom(kind)));
    other
  }

  fn from_char(input: I, c: char) -> Self {
    VerboseError {
      errors: vec![(input, VerboseErrorKind::Char(c))],
    }
  }
}

impl<I> ContextError<I> for VerboseError<I> {
  fn add_context(input: I, ctx: &'static str, mut other: Self) -> Self {
    other.errors.push((input, VerboseErrorKind::Context(ctx)));
    other
  }
}

impl<I, E> FromExternalError<I, E> for VerboseError<I> {
  /// Create a new error from an input position and an external error
  fn from_external_error(input: I, kind: ErrorKind, _e: E) -> Self {
    Self::from_error_kind(input, kind)
  }
}

impl<I: fmt::Display> fmt::Display for VerboseError<I> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    writeln!(f, "Parse error:")?;
    for (input, error) in &self.errors {
      match error {
        VerboseErrorKind::Nom(e) => writeln!(f, "{:?} at: {}", e, input)?,
        VerboseErrorKind::Char(c) => writeln!(f, "expected '{}' at: {}", c, input)?,
        VerboseErrorKind::Context(s) => writeln!(f, "in section '{}', at: {}", s, input)?,
      }
    }

    Ok(())
  }
}

impl<I: fmt::Debug + fmt::Display> std::error::Error for VerboseError<I> {}

impl From<VerboseError<&[u8]>> for VerboseError<Vec<u8>> {
  fn from(value: VerboseError<&[u8]>) -> Self {
    VerboseError {
      errors: value
        .errors
        .into_iter()
        .map(|(i, e)| (i.to_owned(), e))
        .collect(),
    }
  }
}

impl From<VerboseError<&str>> for VerboseError<String> {
  fn from(value: VerboseError<&str>) -> Self {
    VerboseError {
      errors: value
        .errors
        .into_iter()
        .map(|(i, e)| (i.to_owned(), e))
        .collect(),
    }
  }
}

impl<I> ErrorConvert<VerboseError<I>> for VerboseError<(I, usize)> {
  fn convert(self) -> VerboseError<I> {
    VerboseError {
      errors: self.errors.into_iter().map(|(i, e)| (i.0, e)).collect(),
    }
  }
}

impl<I> ErrorConvert<VerboseError<(I, usize)>> for VerboseError<I> {
  fn convert(self) -> VerboseError<(I, usize)> {
    VerboseError {
      errors: self.errors.into_iter().map(|(i, e)| ((i, 0), e)).collect(),
    }
  }
}

/// Transforms a `VerboseError` into a trace with input position information
///
/// The errors contain references to input data that must come from `input`,
/// because nom calculates byte offsets between them
pub fn convert_error<I: core::ops::Deref<Target = str>>(input: I, e: VerboseError<I>) -> String {
  use nom::Offset;
  use std::fmt::Write;

  let mut result = String::new();

  for (i, (substring, kind)) in e.errors.iter().enumerate() {
    let offset = input.offset(substring);

    if input.is_empty() {
      match kind {
        VerboseErrorKind::Char(c) => {
          write!(&mut result, "{}: expected '{}', got empty input\n\n", i, c)
        }
        VerboseErrorKind::Context(s) => write!(&mut result, "{}: in {}, got empty input\n\n", i, s),
        VerboseErrorKind::Nom(e) => write!(&mut result, "{}: in {:?}, got empty input\n\n", i, e),
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
        VerboseErrorKind::Char(c) => {
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
        VerboseErrorKind::Context(s) => write!(
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
        VerboseErrorKind::Nom(e) => write!(
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

#[test]
fn convert_error_panic() {
  use nom::character::complete::char;
  use nom::IResult;

  let input = "";

  let _result: IResult<_, _, VerboseError<&str>> = char('x')(input);
}

#[test]
fn issue_1027_convert_error_panic_nonempty() {
  use nom::character::complete::char;
  use nom::sequence::pair;
  use nom::Err;
  use nom::IResult;
  use nom::Parser;

  let input = "a";

  let result: IResult<_, _, VerboseError<&str>> = pair(char('a'), char('b')).parse(input);
  let err = match result.unwrap_err() {
    Err::Error(e) => e,
    _ => unreachable!(),
  };

  let msg = convert_error(input, err);
  assert_eq!(
    msg,
    "0: at line 1:\na\n ^\nexpected \'b\', got end of input\n\n"
  );
}
