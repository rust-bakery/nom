use crate::error::ErrorKind;
use crate::error::ParseError;
use crate::internal::{Err, IResult, Parser};
use crate::traits::{InputLength, NomBounds};
use crate::Break;
use crate::IntoNomBounds;

use core::ops::ControlFlow;

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
pub fn try_fold<Bounds, IntoBounds, Input, Output, Error, P, Acc, Init, F>(
  bounds: IntoBounds,
  mut parser: P,
  mut init: Init,
  mut try_fold: F,
) -> impl FnMut(Input) -> IResult<Input, Acc, Error>
where
  Bounds: NomBounds,
  for<'a> &'a IntoBounds: IntoNomBounds<NomBounds = Bounds>,
  Input: Clone + InputLength,
  Error: ParseError<Input>,
  P: Parser<Input, Output, Error>,
  Init: FnMut() -> Acc,
  F: FnMut(Acc, Output) -> Result<Acc, Err<Error>>,
{
  move |mut input: Input| {
    let mut bounds = bounds.into_nom_bounds();
    if bounds.is_broken() {
      return Err(Err::Failure(Error::from_error_kind(
        input,
        ErrorKind::TryFold,
      )));
    }

    let mut acc = init();

    loop {
      match bounds.next() {
        ControlFlow::Continue(c) => match parser.parse(input.clone()) {
          Ok((tail, value)) => {
            if tail.input_len() == input.input_len() {
              break Err(Err::Error(Error::from_error_kind(tail, ErrorKind::TryFold)));
            }

            acc = try_fold(acc, value)?;
            input = tail;
          }
          Err(Err::Error(e)) => {
            break if bounds.is_min_reach(c) {
              Ok((input, acc))
            } else {
              Err(Err::Error(e))
            }
          }
          Err(e) => break Err(e),
        },

        ControlFlow::Break(Break::Infinite) => {
          break loop {
            match parser.parse(input.clone()) {
              Ok((tail, value)) => {
                if tail.input_len() == input.input_len() {
                  break Err(Err::Error(Error::from_error_kind(tail, ErrorKind::TryFold)));
                }

                acc = try_fold(acc, value)?;
                input = tail;
              }
              Err(Err::Error(_)) => break Ok((input, acc)),
              Err(e) => break Err(e),
            }
          };
        }
        ControlFlow::Break(Break::Finish) => break Ok((input, acc)),
      }
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
