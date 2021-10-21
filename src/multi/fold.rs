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
pub fn fold<Range, Input, Output, Error, P, Acc, Init, F>(
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
  F: FnMut(Acc, Output) -> Acc,
{
  move |input: Input| match (range.start_bound(), range.end_bound()) {
    (Bound::Included(&min), Bound::Included(&max)) => {
      if min > max {
        Err(Err::Failure(Error::from_error_kind(input, ErrorKind::Fold)))
      } else {
        fold_min(
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
        Err(Err::Failure(Error::from_error_kind(input, ErrorKind::Fold)))
      } else {
        fold_min(
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
      let (input, acc) = fold_exact(0..min, input, &mut parser, &mut init, &mut fold)?;
      fold_infinite(input, &mut parser, acc, &mut fold)
    }
    (Bound::Excluded(&min), Bound::Included(&max)) => {
      // can't handle min == usize::MAX
      if min > max || min == usize::MAX {
        Err(Err::Failure(Error::from_error_kind(input, ErrorKind::Fold)))
      } else {
        fold_min(
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
        Err(Err::Failure(Error::from_error_kind(input, ErrorKind::Fold)))
      } else {
        fold_min(
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
      let (input, acc) = fold_exact(0..=min, input, &mut parser, &mut init, &mut fold)?;
      fold_infinite(input, &mut parser, acc, &mut fold)
    }
    (Bound::Unbounded, Bound::Included(&max)) => {
      fold_no_min(0..=max, input, &mut parser, &mut init, &mut fold)
    }
    (Bound::Unbounded, Bound::Excluded(&max)) => {
      fold_no_min(0..max, input, &mut parser, &mut init, &mut fold)
    }
    (Bound::Unbounded, Bound::Unbounded) => fold_infinite(input, &mut parser, init(), &mut fold),
  }
}

fn fold_exact<Iter, Input, Output, Error, P, Acc, Init, F>(
  iter: Iter,
  mut input: Input,
  parser: &mut P,
  init: &mut Init,
  fold: &mut F,
) -> IResult<Input, Acc, Error>
where
  Iter: Iterator<Item = usize>,
  Input: Clone + InputLength,
  Error: ParseError<Input>,
  P: Parser<Input, Output, Error>,
  Init: FnMut() -> Acc,
  F: FnMut(Acc, Output) -> Acc,
{
  let mut acc = init();

  for _ in iter {
    let len = input.input_len();
    match parser.parse(input.clone()) {
      Ok((tail, value)) => {
        // infinite loop check: the parser must always consume
        if tail.input_len() == len {
          return Err(Err::Error(Error::from_error_kind(tail, ErrorKind::Fold)));
        }

        acc = fold(acc, value);
        input = tail;
      }
      Err(e) => return Err(e),
    }
  }

  Ok((input, acc))
}

fn fold_no_min<Iter, Input, Output, Error, P, Acc, Init, F>(
  iter: Iter,
  mut input: Input,
  parser: &mut P,
  init: &mut Init,
  fold: &mut F,
) -> IResult<Input, Acc, Error>
where
  Iter: Iterator<Item = usize>,
  Input: Clone + InputLength,
  Error: ParseError<Input>,
  P: Parser<Input, Output, Error>,
  Init: FnMut() -> Acc,
  F: FnMut(Acc, Output) -> Acc,
{
  let mut acc = init();

  for _ in iter {
    let len = input.input_len();
    match parser.parse(input.clone()) {
      Ok((tail, value)) => {
        // infinite loop check: the parser must always consume
        if tail.input_len() == len {
          return Err(Err::Error(Error::from_error_kind(tail, ErrorKind::Fold)));
        }

        acc = fold(acc, value);
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

fn fold_min<V, Iter, Input, Output, Error, P, Acc, Init, F>(
  verify: V,
  iter: Iter,
  mut input: Input,
  parser: &mut P,
  init: &mut Init,
  fold: &mut F,
) -> IResult<Input, Acc, Error>
where
  V: Fn(usize) -> bool,
  Iter: Iterator<Item = usize>,
  Input: Clone + InputLength,
  Error: ParseError<Input>,
  P: Parser<Input, Output, Error>,
  Init: FnMut() -> Acc,
  F: FnMut(Acc, Output) -> Acc,
{
  let mut acc = init();

  for count in iter {
    let len = input.input_len();
    match parser.parse(input.clone()) {
      Ok((tail, value)) => {
        // infinite loop check: the parser must always consume
        if tail.input_len() == len {
          return Err(Err::Error(Error::from_error_kind(tail, ErrorKind::Fold)));
        }

        acc = fold(acc, value);
        input = tail;
      }
      //FInputXMError: handle failure properly
      Err(Err::Error(err)) => {
        if verify(count) {
          return Err(Err::Error(Error::append(input, ErrorKind::Fold, err)));
        } else {
          break;
        }
      }
      Err(e) => return Err(e),
    }
  }

  Ok((input, acc))
}

fn fold_infinite<Input, Output, Error, P, Acc, F>(
  mut input: Input,
  parser: &mut P,
  mut acc: Acc,
  fold: &mut F,
) -> IResult<Input, Acc, Error>
where
  Input: Clone + InputLength,
  Error: ParseError<Input>,
  P: Parser<Input, Output, Error>,
  F: FnMut(Acc, Output) -> Acc,
{
  loop {
    let len = input.input_len();
    match parser.parse(input.clone()) {
      Ok((tail, value)) => {
        // infinite loop check: the parser must always consume
        if tail.input_len() == len {
          break Err(Err::Error(Error::from_error_kind(tail, ErrorKind::Fold)));
        }

        acc = fold(acc, value);
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
#[cfg(feature = "alloc")]
fn fold_test() {
  use crate::{bytes::streaming::tag, lib::std::vec::Vec, Needed};
  fn fold_into_vec<T>(mut acc: Vec<T>, item: T) -> Vec<T> {
    acc.push(item);
    acc
  }

  // should not go into an infinite loop
  fn fold_error_0(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fn tst(input: &[u8]) -> IResult<&[u8], &[u8]> {
      Err(Err::Error(error_position!(input, ErrorKind::Tag)))
    }
    fold(0.., tst, Vec::new, fold_into_vec)(i)
  }

  let a = &b"abcdef"[..];
  assert_eq!(fold_error_0(a), Ok((a, Vec::new())));

  fn fold_error_1(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fn tst(input: &[u8]) -> IResult<&[u8], &[u8]> {
      Err(Err::Error(error_position!(input, ErrorKind::Tag)))
    }
    fold(1.., tst, Vec::new, fold_into_vec)(i)
  }

  let a = &b"abcdef"[..];
  assert_eq!(
    fold_error_1(a),
    Err(Err::Error(error_position!(a, ErrorKind::Tag)))
  );

  fn fold_error(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fold(0.., tag(""), Vec::new, fold_into_vec)(i)
  }

  let a = &b"abcdef"[..];
  assert_eq!(
    fold_error(a),
    Err(Err::Error(error_position!(a, ErrorKind::Fold)))
  );

  fn fold_invalid(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fold(2..=1, tag("a"), Vec::new, fold_into_vec)(i)
  }

  let a = &b"a"[..];
  let b = &b"b"[..];
  assert_eq!(
    fold_invalid(a),
    Err(Err::Failure(error_position!(a, ErrorKind::Fold)))
  );
  assert_eq!(
    fold_invalid(b),
    Err(Err::Failure(error_position!(b, ErrorKind::Fold)))
  );

  fn fold_any(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fold(0.., tag("abcd"), Vec::new, fold_into_vec)(i)
  }

  let a = &b"abcdef"[..];
  let b = &b"abcdabcdefgh"[..];
  let c = &b"azerty"[..];
  let d = &b"abcdab"[..];
  let e = &b"abcd"[..];
  let f = &b""[..];
  assert_eq!(fold_any(a), Ok((&b"ef"[..], vec![&b"abcd"[..]])));
  assert_eq!(
    fold_any(b),
    Ok((&b"efgh"[..], vec![&b"abcd"[..], &b"abcd"[..]]))
  );
  assert_eq!(fold_any(c), Ok((c, Vec::new())));
  assert_eq!(fold_any(d), Err(Err::Incomplete(Needed::new(2))));
  assert_eq!(fold_any(e), Err(Err::Incomplete(Needed::new(4))));
  assert_eq!(fold_any(f), Err(Err::Incomplete(Needed::new(4))));

  fn fold_1(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fold(1.., tag("abcd"), Vec::new, fold_into_vec)(i)
  }

  let a = &b"abcdef"[..];
  let b = &b"abcdabcdefgh"[..];
  let c = &b"azerty"[..];
  let d = &b"abcdab"[..];
  let res1 = vec![&b"abcd"[..]];
  assert_eq!(fold_1(a), Ok((&b"ef"[..], res1)));
  let res2 = vec![&b"abcd"[..], &b"abcd"[..]];
  assert_eq!(fold_1(b), Ok((&b"efgh"[..], res2)));
  assert_eq!(
    fold_1(c),
    Err(Err::Error(error_position!(c, ErrorKind::Tag)))
  );
  assert_eq!(fold_1(d), Err(Err::Incomplete(Needed::new(2))));

  fn fold_m_n(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fold(2..=3, tag("Abcd"), Vec::new, fold_into_vec)(i)
  }

  let a = &b"Abcdef"[..];
  let b = &b"AbcdAbcdefgh"[..];
  let c = &b"AbcdAbcdAbcdAbcdefgh"[..];
  let d = &b"AbcdAbcdAbcdAbcdAbcdefgh"[..];
  let e = &b"AbcdAb"[..];
  assert_eq!(
    fold_m_n(a),
    Err(Err::Error(error_position!(&b"ef"[..], ErrorKind::Tag)))
  );
  let res1 = vec![&b"Abcd"[..], &b"Abcd"[..]];
  assert_eq!(fold_m_n(b), Ok((&b"efgh"[..], res1)));
  let res2 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
  assert_eq!(fold_m_n(c), Ok((&b"efgh"[..], res2)));
  let res3 = vec![&b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..], &b"Abcd"[..]];
  assert_eq!(fold_m_n(d), Ok((&b"Abcdefgh"[..], res3)));
  assert_eq!(fold_m_n(e), Err(Err::Incomplete(Needed::new(2))));

  fn fold_fixed(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fold(2..2, tag("Abcd"), Vec::new, fold_into_vec)(i)
  }

  let a = &b"Abcdef"[..];
  let b = &b"AbcdAbcdefgh"[..];
  let c = &b"AbcdAbcdAbcdAbcdefgh"[..];
  let d = &b"AbcdAb"[..];
  assert_eq!(
    fold_fixed(a),
    Err(Err::Error(error_position!(&b"ef"[..], ErrorKind::Tag)))
  );
  let res1 = vec![&b"Abcd"[..], &b"Abcd"[..]];
  assert_eq!(fold_fixed(b), Ok((&b"efgh"[..], res1)));
  let res2 = vec![&b"Abcd"[..], &b"Abcd"[..]];
  assert_eq!(fold_fixed(c), Ok((&b"AbcdAbcdefgh"[..], res2)));
  assert_eq!(fold_fixed(d), Err(Err::Incomplete(Needed::new(2))));

  fn fold_exclusive(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fold(0..1, tag("Abcd"), Vec::new, fold_into_vec)(i)
  }

  let a = &b"AbcdAbcdAbcd"[..];
  let b = &b"AAA"[..];
  let res1 = vec![&b"Abcd"[..]];
  assert_eq!(fold_exclusive(a), Ok((&b"AbcdAbcd"[..], res1)));
  let res2 = vec![];
  assert_eq!(fold_exclusive(b), Ok((&b"AAA"[..], res2)));

  fn fold_never(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fold(0..=0, tag("A"), Vec::new, fold_into_vec)(i)
  }

  let a = &b"AAA"[..];
  let b = &b"B"[..];
  let res1 = vec![&b"A"[..]];
  assert_eq!(fold_never(a), Ok((&b"AA"[..], res1)));
  assert_eq!(fold_never(b), Ok((&b"B"[..], Vec::new())));

  fn fold_usize(i: &[u8]) -> IResult<&[u8], Vec<&[u8]>> {
    fold(1, tag("A"), Vec::new, fold_into_vec)(i)
  }

  let a = &b"AAA"[..];
  let res1 = vec![&b"A"[..], &b"A"[..]];
  assert_eq!(fold_usize(a), Ok((&b"A"[..], res1)));
}
