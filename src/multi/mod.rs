//! combinators applying their child parser multiple times

#[macro_use]
mod macros;

use internal::{Err, IResult, Needed};
use error::ParseError;
use traits::{InputLength, InputTake};
#[cfg(feature = "alloc")]
use ::lib::std::vec::Vec;
use error::ErrorKind;

/// Repeats the embedded parser until it fails
/// and returns the results in a `Vec`.
/// # Arguments
/// * `f` The parser to apply.
//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn many0<I, O, E, F>(f: F) -> impl Fn(I) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let mut acc = ::lib::std::vec::Vec::with_capacity(4);
    let mut i = i.clone();
    loop {
      match f(i.clone()) {
        Err(Err::Error(_)) => return Ok((i, acc)),
        Err(e) => return Err(e),
        Ok((i1, o)) => {
          if i1 == i {
            return Err(Err::Error(E::from_error_kind(i, ErrorKind::Many0)));
          }

          i = i1;
          acc.push(o);
        }
      }
    }
  }
}
//FIXME: streaming
// this implementation is used for type inference issues in macros
#[doc(hidden)]
#[cfg(feature = "alloc")]
pub fn many0c<I, O, E, F>(input: I, f: F) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  many0(f)(input)
}

/// Runs the embedded parser until it fails and
/// returns the results in a `Vec`. Fails if
/// the embedded parser does not produce at least
/// one result.
/// # Arguments
/// * `f` The parser to apply.
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::multi::many1;
/// use nom::bytes::complete::tag;
/// # fn main() {
/// let embedded_parser = |s: &'static str| {
///   tag::<_, _, (_, ErrorKind)>("abc")(s)
/// };
/// let parser = |s: &'static str| {
///   many1::<_, _, (_, ErrorKind), _>(embedded_parser)(s)
/// };
///
/// assert_eq!(parser("abcabc"), Ok(("", vec!["abc", "abc"])));
/// assert_eq!(parser("abc123"), Ok(("123", vec!["abc"])));
/// assert_eq!(parser("123123"), Err(Err::Error(("123123", ErrorKind::Tag))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// # }
/// ```
//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn many1<I, O, E, F>(f: F) -> impl Fn(I) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let mut i = i.clone();
    match f(i.clone()) {
      Err(Err::Error(err)) => return Err(Err::Error(E::append(i, ErrorKind::Many1, err))),
      Err(e) => return Err(e),
      Ok((i1, o)) => {
        let mut acc = ::lib::std::vec::Vec::with_capacity(4);
        acc.push(o);
        i = i1;

        loop {
          match f(i.clone()) {
            Err(Err::Error(_)) => return Ok((i, acc)),
            Err(e) => return Err(e),
            Ok((i1, o)) => {
              if i1 == i {
                return Err(Err::Error(E::from_error_kind(i, ErrorKind::Many1)));
              }

              i = i1;
              acc.push(o);
            }
          }
        }
      }
    }
  }
}

//FIXME: streaming
// this implementation is used for type inference issues in macros
#[doc(hidden)]
#[cfg(feature = "alloc")]
pub fn many1c<I, O, E, F>(input: I, f: F) -> IResult<I, Vec<O>, E>
where
  I: Clone + Copy + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  many1(f)(input)
}

/// Applies the parser `f` until the parser `g` produces
/// a result. Returns a pair consisting of the results of
/// `f` in a `Vec` and the result of `g`.
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::multi::many_till;
/// use nom::bytes::complete::tag;
/// # fn main() {
/// let condition_parser = |s: &'static str| {
///   tag::<_, _, (_, ErrorKind)>("end")(s)
/// };
/// let embedded_parser = |s: &'static str| {
///   tag::<_, _, (_, ErrorKind)>("abc")(s)
/// };
/// let parser = |s: &'static str| {
///   many_till::<_, _, _, (_, ErrorKind), _, _>(embedded_parser, condition_parser)(s)
/// };
///
/// assert_eq!(parser("abcabcend"), Ok(("", (vec!["abc", "abc"], "end"))));
/// assert_eq!(parser("abc123end"), Err(Err::Error(("123end", ErrorKind::Tag))));
/// assert_eq!(parser("123123end"), Err(Err::Error(("123123end", ErrorKind::Tag))));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("abcendefg"), Ok(("efg", (vec!["abc"], "end"))));
/// # }
/// ```
//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn many_till<I, O, P, E, F, G>(f: F, g: G) -> impl Fn(I) -> IResult<I, (Vec<O>, P), E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(I) -> IResult<I, P, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let mut res = ::lib::std::vec::Vec::new();
    let mut i = i.clone();
    loop {
      match g(i.clone()) {
        Ok((i1, o)) => return Ok((i1, (res, o))),
        Err(Err::Error(_)) => {
          match f(i.clone()) {
            Err(Err::Error(err)) =>
              return Err(Err::Error(E::append(i, ErrorKind::ManyTill, err))),
            Err(e) => return Err(e),
            Ok((i1, o)) => {
              // loop trip must always consume (otherwise infinite loops)
              if i1 == i {
                return Err(Err::Error(E::from_error_kind(i1, ErrorKind::ManyTill)));
              }

              res.push(o);
              i = i1;
            }
          }
        },
        Err(e) => return Err(e),
      }
    }
  }
}

//FIXME: streaming
// this implementation is used for type inference issues in macros
#[doc(hidden)]
#[cfg(feature = "alloc")]
pub fn many_tillc<I, O, P, E, F, G>(i: I, f: F, g: G) -> IResult<I, (Vec<O>, P), E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(I) -> IResult<I, P, E>,
  E: ParseError<I>,
{
  many_till(f, g)(i)
}

/// Alternates between two parsers to produce
/// a list of elements.
/// # Arguments
/// * `f` Parses the elements of the list.
/// * `sep` Parses the separator between list elements.
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::multi::separated_list;
/// use nom::bytes::complete::tag;
/// # fn main() {
/// let separator_parser = |s: &'static str| {
///   tag::<_, _, (_, ErrorKind)>("|")(s)
/// };
/// let embedded_parser = |s: &'static str| {
///   tag::<_, _, (_, ErrorKind)>("abc")(s)
/// };
/// let parser = |s: &'static str| {
///   separated_list::<_, _, _, (_, ErrorKind), _, _>(separator_parser, embedded_parser)(s)
/// };
///
/// assert_eq!(parser("abc|abc|abc"), Ok(("", vec!["abc", "abc", "abc"])));
/// assert_eq!(parser("abc123abc"), Ok(("123abc", vec!["abc"])));
/// assert_eq!(parser("abc|def"), Ok(("|def", vec!["abc"])));
/// assert_eq!(parser(""), Ok(("", vec![])));
/// assert_eq!(parser("def|abc"), Ok(("def|abc", vec![])));
/// # }
/// ```
//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn separated_list<I, O, O2, E, F, G>(sep: G, f: F) -> impl Fn(I) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let mut res = Vec::new();
    let mut i = i.clone();

    match f(i.clone()) {
      Err(Err::Error(_)) => return Ok((i, res)),
      Err(e) => return Err(e),
      Ok((i1, o)) => {
        if i1 == i {
          return Err(Err::Error(E::from_error_kind(i1, ErrorKind::SeparatedList)));
        }

        res.push(o);
        i = i1;
      }
    }

    loop {
      match sep(i.clone()) {
        Err(Err::Error(_)) => return Ok((i, res)),
        Err(e) => return Err(e),
        Ok((i1, _)) => {
          if i1 == i {
            return Err(Err::Error(E::from_error_kind(i1, ErrorKind::SeparatedList)));
          }

          match f(i1.clone()) {
            Err(Err::Error(_)) => return Ok((i, res)),
            Err(e) => return Err(e),
            Ok((i2, o)) => {
              if i2 == i {
                return Err(Err::Error(E::from_error_kind(i2, ErrorKind::SeparatedList)));
              }

              res.push(o);
              i = i2;
            }
          }
        }
      }
    }
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
#[cfg(feature = "alloc")]
pub fn separated_listc<I, O, O2, E, F, G>(i: I, sep: G, f: F) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  E: ParseError<I>,
{
  separated_list(sep, f)(i)
}

/// Alternates between two parsers to produce
/// a list of elements. Fails if the element
/// parser does not produce at least one element.
/// # Arguments
/// * `f` Parses the elements of the list.
/// * `sep` Parses the separator between list elements.
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, error::ErrorKind, Needed};
/// use nom::multi::separated_nonempty_list;
/// use nom::bytes::complete::tag;
/// # fn main() {
/// let separator_parser = |s: &'static str| {
///   tag::<_, _, (_, ErrorKind)>("|")(s)
/// };
/// let embedded_parser = |s: &'static str| {
///   tag::<_, _, (_, ErrorKind)>("abc")(s)
/// };
/// let parser = |s: &'static str| {
///   separated_nonempty_list::<_, _, _, (_, ErrorKind), _, _>(separator_parser, embedded_parser)(s)
/// };
///
/// assert_eq!(parser("abc|abc|abc"), Ok(("", vec!["abc", "abc", "abc"])));
/// assert_eq!(parser("abc123abc"), Ok(("123abc", vec!["abc"])));
/// assert_eq!(parser("abc|def"), Ok(("|def", vec!["abc"])));
/// assert_eq!(parser(""), Err(Err::Error(("", ErrorKind::Tag))));
/// assert_eq!(parser("def|abc"), Err(Err::Error(("def|abc", ErrorKind::Tag))));
/// # }
/// ```
//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn separated_nonempty_list<I, O, O2, E, F, G>(sep: G, f: F) -> impl Fn(I) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let mut res = Vec::new();
    let mut i = i.clone();

    // Parse the first element
    match f(i.clone()) {
      Err(e)=> return Err(e),
      Ok((i1, o)) => {
        if i1 == i {
          return Err(Err::Error(E::from_error_kind(i1, ErrorKind::SeparatedList)));
        }

        res.push(o);
        i = i1;
      }
    }

    loop {
      match sep(i.clone()) {
        Err(Err::Error(_)) => return Ok((i, res)),
        Err(e) => return Err(e),
        Ok((i1, _)) => {
          if i1 == i {
            return Err(Err::Error(E::from_error_kind(i1, ErrorKind::SeparatedList)));
          }

          match f(i1.clone()) {
            Err(Err::Error(_)) => return Ok((i, res)),
            Err(e) => return Err(e),
            Ok((i2, o)) => {
              if i2 == i {
                return Err(Err::Error(E::from_error_kind(i2, ErrorKind::SeparatedList)));
              }

              res.push(o);
              i = i2;
            }
          }
        }  
      }
    }
  }
}

//FIXME: streaming
// this implementation is used for type inference issues in macros
#[doc(hidden)]
#[cfg(feature = "alloc")]
pub fn separated_nonempty_listc<I, O, O2, E, F, G>(i: I, sep: G, f: F) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  E: ParseError<I>,
{
  separated_nonempty_list(sep, f)(i)
}

/// Repeats the embedded parser `n` times or until it fails
/// and returns the results in a `Vec`. Fails if the
/// embedded parser does not succeed at least `m` times.
/// # Arguments
/// * `m` The minimum number of iterations.
/// * `n` The maximum number of iterations.
/// * `f` The parser to apply.
//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn many_m_n<I, O, E, F>(m: usize, n: usize, f: F) -> impl Fn(I) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let mut res = ::lib::std::vec::Vec::with_capacity(m);
    let mut input = i.clone();
    let mut count: usize = 0;

    loop {
      let _i = input.clone();
      match f(_i) {
        Ok((i, o)) => {
          // do not allow parsers that do not consume input (causes infinite loops)
          if i == input {
            return Err(Err::Error(E::from_error_kind(input, ErrorKind::ManyMN)));
          }

          res.push(o);
          input = i;
          count += 1;

          if count == n {
            return Ok((input, res));
          }
        }
        Err(Err::Error(e)) => {
          if count < m {
            return Err(Err::Error(E::append(input, ErrorKind::ManyMN, e)));
          } else {
            return Ok((input, res));
          }
        }
        Err(e) => {
          return Err(e);
        }
      }
    }
  }
}

//FIXME: streaming
// this implementation is used for type inference issues in macros
#[doc(hidden)]
#[cfg(feature = "alloc")]
pub fn many_m_nc<I, O, E, F>(i: I, m: usize, n: usize, f: F) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  many_m_n(m, n, f)(i)
}

/// Repeats the embedded parser until it fails
/// and returns the number of successful iterations.
/// # Arguments
/// * `f` The parser to apply.
//FIXME: streaming
pub fn many0_count<I, O, E, F>(f: F) -> impl Fn(I) -> IResult<I, usize, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let mut input = i.clone();
    let mut count = 0;

    loop {
      let input_ = input.clone();
      match f(input_) {
        Ok((i, _)) => {
          //  loop trip must always consume (otherwise infinite loops)
          if i == input {
            return Err(Err::Error(E::from_error_kind(input, ErrorKind::Many0Count)));
          }

          input = i;
          count += 1;
        }

        Err(Err::Error(_)) => return Ok((input, count)),

        Err(e) => return Err(e),
      }
    }
  }
}

#[doc(hidden)]
pub fn many0_countc<I, O, E, F>(i: I, f: F) -> IResult<I, usize, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  many0_count(f)(i)
}

/// Repeats the embedded parser until it fails
/// and returns the number of successful iterations.
/// Fails if the embedded parser does not succeed
/// at least once.
/// # Arguments
/// * `f` The parser to apply.
//FIXME: streaming
pub fn many1_count<I, O, E, F>(f: F) -> impl Fn(I) -> IResult<I, usize, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let i_ = i.clone();
    match f(i_) {
      Err(Err::Error(_)) => Err(Err::Error(E::from_error_kind(i, ErrorKind::Many1Count))),
      Err(i) => Err(i),
      Ok((i1, _)) => {
        let mut count = 1;
        let mut input = i1;

        loop {
          let input_ = input.clone();
          match f(input_) {
            Err(Err::Error(_)) => return Ok((input, count)),
            Err(e) => return Err(e),
            Ok((i, _)) => {
              if i == input {
                return Err(Err::Error(E::from_error_kind(i, ErrorKind::Many1Count)));
              }

              count += 1;
              input = i;
            }
          }
        }
      }
    }
  }
}

#[doc(hidden)]
pub fn many1_countc<I, O, E, F>(i: I, f: F) -> IResult<I, usize, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  many1_count(f)(i)
}

/// Runs the embedded parser a specified number
/// of times. Returns the results in a `Vec`.
/// # Arguments
/// * `f` The parser to apply.
/// * `count` How often to apply the parser.
#[cfg(feature = "alloc")]
pub fn count<I, O, E, F>(f: F, count: usize) -> impl Fn(I) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  move |i: I | {
    let mut input = i.clone();
    let mut res = ::lib::std::vec::Vec::new();

    for _ in 0..count {
      let input_ = input.clone();
      match f(input_) {
        Ok((i, o)) => {
          res.push(o);
          input = i;
        }
        Err(Err::Error(e)) => {
          return Err(Err::Error(E::append(i, ErrorKind::Count, e)));
        }
        Err(e) => {
          return Err(e);
        }
      }
    }

    Ok((input, res))
  }
}

/// Applies a parser until it fails and accumulates
/// the results using a given function and initial value.
/// # Arguments
/// * `f` The parser to apply.
/// * `init` The initial value.
/// * `g` The function that combines a result of `f` with
///       the current accumulator.
//FIXME: streaming
pub fn fold_many0<I, O, E, F, G, R>(f: F, init: R, g: G) -> impl Fn(I) -> IResult<I, R, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(R, O) -> R,
  E: ParseError<I>,
  R: Clone,
{
  move |i: I| {
    let mut res = init.clone();
    let mut input = i.clone();

    loop {
      let i_ = input.clone();
      match f(i_) {
        Ok((i, o)) => {
          // loop trip must always consume (otherwise infinite loops)
          if i == input {
            return Err(Err::Error(E::from_error_kind(input, ErrorKind::Many0)));
          }

          res = g(res, o);
          input = i;
        }
        Err(Err::Error(_)) => {
          return Ok((input, res));
        }
        Err(e) => {
          return Err(e);
        }
      }
    }
  }
}

#[doc(hidden)]
pub fn fold_many0c<I, O, E, F, G, R>(i: I, f: F, init: R, g: G) -> IResult<I, R, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(R, O) -> R,
  E: ParseError<I>,
  R: Clone,
{
  fold_many0(f, init, g)(i)
}

/// Applies a parser until it fails and accumulates
/// the results using a given function and initial value.
/// Fails if the embedded parser does not succeed at least
/// once.
/// # Arguments
/// * `f` The parser to apply.
/// * `init` The initial value.
/// * `g` The function that combines a result of `f` with
///       the current accumulator.
//FIXME: streaming
pub fn fold_many1<I, O, E, F, G, R>(f: F, init: R, g: G) -> impl Fn(I) -> IResult<I, R, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(R, O) -> R,
  E: ParseError<I>,
  R: Clone,
{
  move |i: I| {
    let _i = i.clone();
    let init = init.clone();
    match f(_i) {
      Err(Err::Error(_)) => Err(Err::Error(E::from_error_kind(i, ErrorKind::Many1))),
      Err(e) => return Err(e),
      Ok((i1, o1)) => {
        let mut acc = g(init, o1);
        let mut input = i1;

        loop {
          let _input = input.clone();
          match f(_input) {
            Err(Err::Error(_)) => {
              break;
            }
            Err(e) => return Err(e),
            Ok((i, o)) => {
              if i == input {
                return Err(Err::Failure(E::from_error_kind(i, ErrorKind::Many1)));
              }

              acc = g(acc, o);
              input = i;
            }
          }
        }

        Ok((input, acc))
      }
    }
  }
}

#[doc(hidden)]
pub fn fold_many1c<I, O, E, F, G, R>(i: I, f: F, init: R, g: G) -> IResult<I, R, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(R, O) -> R,
  E: ParseError<I>,
  R: Clone,
{
  fold_many1(f, init, g)(i)
}

/// Applies a parser `n` times or until it fails and accumulates
/// the results using a given function and initial value.
/// Fails if the embedded parser does not succeed at least `m`
/// times.
/// # Arguments
/// * `m` The minimum number of iterations.
/// * `n` The maximum number of iterations.
/// * `f` The parser to apply.
/// * `init` The initial value.
/// * `g` The function that combines a result of `f` with
///       the current accumulator.
//FIXME: streaming
pub fn fold_many_m_n<I, O, E, F, G, R>(m: usize, n: usize, f: F, init: R, g: G) -> impl Fn(I) ->IResult<I, R, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(R, O) -> R,
  E: ParseError<I>,
  R: Clone,
{
  move |i: I| {
    let mut acc = init.clone();
    let mut input = i.clone();
    for count in 0..n {
      let _input = input.clone();
      match f(_input) {
        Ok((i, o)) => {
          // do not allow parsers that do not consume input (causes infinite loops)
          if i == input {
            return Err(Err::Error(E::from_error_kind(i, ErrorKind::ManyMN)));
          }

          acc = g(acc, o);
          input = i;
        }
        //FInputXMError: handle failure properly
        Err(Err::Error(_)) => if count < m {
          return Err(Err::Error(E::from_error_kind(i, ErrorKind::ManyMN)));
        } else {
          break;
        }
        Err(e) => return Err(e),
      }
    }

    Ok((input, acc))
  }
}

#[doc(hidden)]
pub fn fold_many_m_nc<I, O, E, F, G, R>(i: I, m: usize, n: usize, f: F, init: R, g: G) -> IResult<I, R, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(R, O) -> R,
  E: ParseError<I>,
  R: Clone,
{
  fold_many_m_n(m, n, f, init, g)(i)
}

pub fn length_value<I, O, N, E, F, G>(f: F, g: G) -> impl Fn(I) -> IResult<I, O, E>
where
  I: Clone + InputLength + InputTake,
  N: Copy + Into<usize>,
  F: Fn(I) -> IResult<I, N, E>,
  G: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let (i, length) = f(i)?;

    let length: usize = length.into();

    if i.input_len() < length {
      Err(Err::Incomplete(Needed::Size(length)))
    } else {
      let (rest, i) = i.take_split(length);
      match g(i.clone()) {
        Err(Err::Incomplete(_)) =>
          Err(Err::Error(E::from_error_kind(i, ErrorKind::Complete))),
        Err(e) => Err(e),
        Ok((_, o)) => Ok((rest,o)),
      }
    }
  }
}

#[doc(hidden)]
pub fn length_valuec<I, O, N, E, F, G>(i: I, f: F, g: G) -> IResult<I, O, E>
where
  I: Clone + InputLength + InputTake,
  N: Copy + Into<usize>,
  F: Fn(I) -> IResult<I, N, E>,
  G: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  length_value(f, g)(i)
}
