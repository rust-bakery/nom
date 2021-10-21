use crate::error::ErrorKind;
use crate::error::ParseError;
use crate::internal::{Err, IResult, Parser};
use crate::traits::{InputLength, NomRangeBounds};

use core::ops::Bound;

/// Applies a parser and accumulates the results using a given
/// function and initial value.
/// Fails if the amount of time the embedded parser is run is not
/// within the specified range.
///
/// # Arguments
/// * `range` Constrains the number of iterations.
///   * A range without an upper bound `a..` allows the parser to run until it fails.
///   * A single `usize` value is equivalent to `value..=value`.
///   * An empty range is invalid.
/// * `parse` The parser to apply.
/// * `init` A function returning the initial value.
/// * `fold` The function that combines a result of `f` with
///       the current accumulator.
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, error::ErrorKind, Needed, IResult};
/// use nom::multi::fold;
/// use nom::bytes::complete::tag;
///
/// fn parser(s: &str) -> IResult<&str, Vec<&str>> {
///   fold(
///     ..2,
///     tag("abc"),
///     Vec::new,
///     |mut acc: Vec<_>, item| {
///       acc.push(item);
///       acc
///     }
///   )(s)
/// }
///
/// assert_eq!(parser("abcabc"), Ok(("", vec!["abc", "abc"])));
/// assert_eq!(parser("abc123"), Ok(("123", vec!["abc"])));
/// assert_eq!(parser("123123"), Ok(("123123", vec![])));
/// assert_eq!(parser(""), Ok(("", vec![])));
/// assert_eq!(parser("abcabcabc"), Ok(("abc", vec!["abc", "abc"])));
/// ```
pub fn try_fold<Range, Input, Output, Error, P, Acc, Init, F>(
  range: Range,
  mut parser: P,
  mut init: Init,
  mut fold: F,
) -> impl FnMut(Input) -> IResult<Input, Acc, Error>
where
  Range: NomRangeBounds<usize>,
  Input: Clone + InputLength,
  Error: ParseError<Input>,
  P: Parser<Input, Output, Error>,
  Init: FnMut() -> Acc,
  F: FnMut(Acc, Output) -> Result<Acc, Err<Error>>,
{
  move |input: Input| match (range.start_bound(), range.end_bound()) {
    (Bound::Included(&min), Bound::Included(&max)) => {
      if min > max {
        Err(Err::Failure(Error::from_error_kind(
          input,
          ErrorKind::TryFold,
        )))
      } else {
        try_fold_min(
          |count| count < min,
          0..=max,
          input,
          &mut parser,
          &mut init,
          &mut fold,
        )
      }
    }
    (Bound::Included(&min), Bound::Excluded(&max)) => {
      if min > max {
        Err(Err::Failure(Error::from_error_kind(
          input,
          ErrorKind::TryFold,
        )))
      } else {
        try_fold_min(
          |count| count < min,
          0..max,
          input,
          &mut parser,
          &mut init,
          &mut fold,
        )
      }
    }
    (Bound::Included(&min), Bound::Unbounded) => {
      let (input, acc) = try_fold_exact(0..min, input, &mut parser, &mut init, &mut fold)?;
      try_fold_infinite(input, &mut parser, acc, &mut fold)
    }
    (Bound::Excluded(&min), Bound::Included(&max)) => {
      // can't handle min == usize::MAX
      if min > max || min == usize::MAX {
        Err(Err::Failure(Error::from_error_kind(
          input,
          ErrorKind::TryFold,
        )))
      } else {
        try_fold_min(
          |count| count <= min,
          0..=max,
          input,
          &mut parser,
          &mut init,
          &mut fold,
        )
      }
    }
    (Bound::Excluded(&min), Bound::Excluded(&max)) => {
      // both excluded so can't be equal, can't handle min == usize::MAX
      if min >= max || min == usize::MAX {
        Err(Err::Failure(Error::from_error_kind(
          input,
          ErrorKind::TryFold,
        )))
      } else {
        try_fold_min(
          |count| count <= min,
          0..max,
          input,
          &mut parser,
          &mut init,
          &mut fold,
        )
      }
    }
    (Bound::Excluded(&min), Bound::Unbounded) => {
      let (input, acc) = try_fold_exact(0..=min, input, &mut parser, &mut init, &mut fold)?;
      try_fold_infinite(input, &mut parser, acc, &mut fold)
    }
    (Bound::Unbounded, Bound::Included(&max)) => {
      try_fold_no_min(0..=max, input, &mut parser, &mut init, &mut fold)
    }
    (Bound::Unbounded, Bound::Excluded(&max)) => {
      try_fold_no_min(0..max, input, &mut parser, &mut init, &mut fold)
    }
    (Bound::Unbounded, Bound::Unbounded) => {
      try_fold_infinite(input, &mut parser, init(), &mut fold)
    }
  }
}

fn try_fold_exact<Iter, Input, Output, Error, P, Acc, Init, F>(
  iter: Iter,
  mut input: Input,
  parser: &mut P,
  init: &mut Init,
  try_fold: &mut F,
) -> IResult<Input, Acc, Error>
where
  Iter: Iterator<Item = usize>,
  Input: Clone + InputLength,
  Error: ParseError<Input>,
  P: Parser<Input, Output, Error>,
  Init: FnMut() -> Acc,
  F: FnMut(Acc, Output) -> Result<Acc, Err<Error>>,
{
  let mut acc = init();

  for _ in iter {
    let len = input.input_len();
    match parser.parse(input.clone()) {
      Ok((tail, value)) => {
        // infinite loop check: the parser must always consume
        if tail.input_len() == len {
          return Err(Err::Error(Error::from_error_kind(tail, ErrorKind::TryFold)));
        }

        acc = try_fold(acc, value)?;
        input = tail;
      }
      Err(e) => return Err(e),
    }
  }

  Ok((input, acc))
}

fn try_fold_no_min<Iter, Input, Output, Error, P, Acc, Init, F>(
  iter: Iter,
  mut input: Input,
  parser: &mut P,
  init: &mut Init,
  try_fold: &mut F,
) -> IResult<Input, Acc, Error>
where
  Iter: Iterator<Item = usize>,
  Input: Clone + InputLength,
  Error: ParseError<Input>,
  P: Parser<Input, Output, Error>,
  Init: FnMut() -> Acc,
  F: FnMut(Acc, Output) -> Result<Acc, Err<Error>>,
{
  let mut acc = init();

  for _ in iter {
    let len = input.input_len();
    match parser.parse(input.clone()) {
      Ok((tail, value)) => {
        // infinite loop check: the parser must always consume
        if tail.input_len() == len {
          return Err(Err::Error(Error::from_error_kind(tail, ErrorKind::TryFold)));
        }

        acc = try_fold(acc, value)?;
        input = tail;
      }
      //FInputXMError: handle failure properly
      Err(Err::Error(_)) => {
        break;
      }
      Err(e) => return Err(e),
    }
  }

  Ok((input, acc))
}

fn try_fold_min<V, Iter, Input, Output, Error, P, Acc, Init, F>(
  verify: V,
  iter: Iter,
  mut input: Input,
  parser: &mut P,
  init: &mut Init,
  try_fold: &mut F,
) -> IResult<Input, Acc, Error>
where
  V: Fn(usize) -> bool,
  Iter: Iterator<Item = usize>,
  Input: Clone + InputLength,
  Error: ParseError<Input>,
  P: Parser<Input, Output, Error>,
  Init: FnMut() -> Acc,
  F: FnMut(Acc, Output) -> Result<Acc, Err<Error>>,
{
  let mut acc = init();

  for count in iter {
    let len = input.input_len();
    match parser.parse(input.clone()) {
      Ok((tail, value)) => {
        // infinite loop check: the parser must always consume
        if tail.input_len() == len {
          return Err(Err::Error(Error::from_error_kind(tail, ErrorKind::TryFold)));
        }

        acc = try_fold(acc, value)?;
        input = tail;
      }
      //FInputXMError: handle failure properly
      Err(Err::Error(err)) => {
        if verify(count) {
          return Err(Err::Error(Error::append(input, ErrorKind::TryFold, err)));
        } else {
          break;
        }
      }
      Err(e) => return Err(e),
    }
  }

  Ok((input, acc))
}

fn try_fold_infinite<Input, Output, Error, P, Acc, F>(
  mut input: Input,
  parser: &mut P,
  mut acc: Acc,
  try_fold: &mut F,
) -> IResult<Input, Acc, Error>
where
  Input: Clone + InputLength,
  Error: ParseError<Input>,
  P: Parser<Input, Output, Error>,
  F: FnMut(Acc, Output) -> Result<Acc, Err<Error>>,
{
  loop {
    let len = input.input_len();
    match parser.parse(input.clone()) {
      Ok((tail, value)) => {
        // infinite loop check: the parser must always consume
        if tail.input_len() == len {
          break Err(Err::Error(Error::from_error_kind(tail, ErrorKind::TryFold)));
        }

        acc = try_fold(acc, value)?;
        input = tail;
      }
      //FInputXMError: handle failure properly
      Err(Err::Error(_)) => {
        break Ok((input, acc));
      }
      Err(e) => break Err(e),
    }
  }
}

#[test]
fn try_fold_test() {
  use super::try_fold;
  use crate::{character::complete::anychar, error::Error};

  let input = "it's my life";
  let result = try_fold(.., anychar, usize::default, |_, _| {
    Err(Err::Error(Error::from_error_kind(
      input,
      ErrorKind::TryFold,
    )))
  })(input);
  assert_eq!(
    result,
    Err(Err::Error(Error::from_error_kind(
      input,
      ErrorKind::TryFold,
    )))
  );
}
