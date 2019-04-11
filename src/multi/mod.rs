#[macro_use]
mod macros;

use internal::{Err, IResult, Needed, ParseError};
use traits::{need_more, AtEof, InputLength, InputTake};
#[cfg(feature = "alloc")]
use ::lib::std::vec::Vec;
use util::ErrorKind;

//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn many0<Input, Output, Error: ParseError<Input>, F>(f: F) -> impl Fn(Input) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + PartialEq + AtEof,
  F: Fn(Input) -> IResult<Input, Output, Error>,
{
  move |mut input: Input| {
    let mut acc = ::lib::std::vec::Vec::with_capacity(4);

    loop {
      let input_ = input.clone();
      match f(input_) {
        Err(Err::Error(_)) => return Ok((input, acc)),
        Err(Err::Failure(e)) => return Err(Err::Failure(e)),
        Err(Err::Incomplete(n)) => {
          if input.at_eof() {
            return Ok((input, acc));
          } else {
            return Err(Err::Incomplete(n));
          }
        }
        Ok((i, o)) => {
          if i == input {
            return Err(Err::Error(Error::from_error_kind(i, ErrorKind::Many0)));
          }

          input = i;
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
pub fn many0c<Input, Output, Error: ParseError<Input>, F>(input: Input, f: F) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + PartialEq + AtEof,
  F: Fn(Input) -> IResult<Input, Output, Error>,
{
  many0(f)(input)
}

//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn many1<Input, Output, Error: ParseError<Input>, F>(f: F) -> impl Fn(Input) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + Copy + AtEof + PartialEq,
  F: Fn(Input) -> IResult<Input, Output, Error>,
{
  move |input: Input| {
    let input_ = input.clone();
    match f(input_) {
      Err(_) => return Err(Err::Error(Error::from_error_kind(input, ErrorKind::Many1))),
      Ok((i2, o)) => {
        let mut acc = ::lib::std::vec::Vec::with_capacity(4);
        acc.push(o);
        let mut input = i2;

        loop {
          let input_ = input.clone();
          match f(input_) {
            Err(Err::Error(_)) => return Ok((input, acc)),
            Err(Err::Failure(e)) => return Err(Err::Failure(e)),
            Err(Err::Incomplete(n)) => {
              if input.at_eof() {
                return Ok((input, acc));
              } else {
                return Err(Err::Incomplete(n));
              }
            }
            Ok((i, o)) => {
              if i == input {
                return Err(Err::Error(Error::from_error_kind(i, ErrorKind::Many1)));
              }

              input = i;
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
pub fn many1c<Input, Output, Error: ParseError<Input>, F>(input: Input, f: F) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + Copy + AtEof + PartialEq,
  F: Fn(Input) -> IResult<Input, Output, Error>,
{
  many1(f)(input)
}

//FIXME: streaming
/// `many_till!(Input -> IResult<Input,Output>, Input -> IResult<Input,P>) => Input -> IResult<Input, (Vec<Output>, P)>`
#[cfg(feature = "alloc")]
pub fn many_till<Input, Output, P, Error: ParseError<Input>, F, G>(f: F, g: G) -> impl Fn(Input) -> IResult<Input, (Vec<Output>, P), Error>
where
  Input: Clone + PartialEq + InputLength + AtEof,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(Input) -> IResult<Input, P, Error>,
{
  move |i: Input| {
    let ret;
    let mut res = ::lib::std::vec::Vec::new();
    let mut input = i.clone();

    loop {
      let _input = input.clone();
      let _input2 = input.clone();

      match g(_input) {
        Ok((i, o)) => {
          ret = Ok((i, (res, o)));
          break;
        }
        Err(_) => {
          match f(_input2) {
            Err(Err::Error(err)) => {
              //fn unify_types<T>(_: &T, _: &T) {}
              let e = Err::Error(Error::append(input, ErrorKind::ManyTill, err));
              //unify_types(&e1, &e);

              ret = Err(e);
              break;
            }
            Err(e) => {
              ret = Err(e);
              break;
            }
            Ok((i, o)) => {
              // loop trip must always consume (otherwise infinite loops)
              if i == input {
                ret = Err(Err::Error(Error::from_error_kind(input, ErrorKind::ManyTill)));
                break;
              }

              res.push(o);
              input = i;
            }
          }
        }
      }
    }

    ret
  }
}

//FIXME: streaming
// this implementation is used for type inference issues in macros
#[doc(hidden)]
#[cfg(feature = "alloc")]
pub fn many_tillc<Input, Output, P, Error: ParseError<Input>, F, G>(i: Input, f: F, g: G) -> IResult<Input, (Vec<Output>, P), Error>
where
  Input: Clone + PartialEq + InputLength + AtEof,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(Input) -> IResult<Input, P, Error>,
{
  many_till(f, g)(i)
}

//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn separated_list<Input, Output, Output2, Error: ParseError<Input>, F, G>(sep: G, f: F) -> impl Fn(Input) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + InputLength,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(Input) -> IResult<Input, Output2, Error>,
{
  move |i: Input| {
    let mut res = ::lib::std::vec::Vec::new();
    let mut input = i.clone();

    // get the first element
    let input_ = input.clone();
    match f(input_) {
      Err(Err::Error(_)) => Ok((input, res)),
      Err(e) => Err(e),
      Ok((i, o)) => {
        if i.input_len() == input.input_len() {
          Err(Err::Error(Error::from_error_kind(input, ErrorKind::SeparatedList)))
        } else {
          res.push(o);
          input = i;

          let ret;

          loop {
            // get the separator first
            let input_ = input.clone();
            match sep(input_) {
              Err(Err::Error(_)) => {
                ret = Ok((input, res));
                break;
              }
              Err(e) => {
                ret = Err(e);
                break;
              }
              Ok((i2, _)) => {
                let i2_len = i2.input_len();
                if i2_len == input.input_len() {
                  ret = Ok((input, res));
                  break;
                }

                // get the element next
                match f(i2) {
                  Err(Err::Error(_)) => {
                    ret = Ok((input, res));
                    break;
                  }
                  Err(e) => {
                    ret = Err(e);
                    break;
                  }
                  Ok((i3, o3)) => {
                    if i3.input_len() == i2_len {
                      ret = Ok((input, res));
                      break;
                    }
                    res.push(o3);
                    input = i3;
                  }
                }
              }
            }
          }

          ret
        }
      }
    }
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
#[cfg(feature = "alloc")]
pub fn separated_listc<Input, Output, Output2, Error: ParseError<Input>, F, G>(i: Input, sep: G, f: F) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + InputLength,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(Input) -> IResult<Input, Output2, Error>,
{
  separated_list(sep, f)(i)
}

//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn separated_non_empty_list<Input, Output, Output2, Error: ParseError<Input>, F, G>(sep: G, f: F) -> impl Fn(Input) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + InputLength,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(Input) -> IResult<Input, Output2, Error>,
{
  move |i: Input| {
    let mut res = ::lib::std::vec::Vec::new();
    let mut input = i.clone();

    // get the first element
    let input_ = input.clone();
    match f(input_) {
      Err(e) => Err(e),
      Ok((i, o)) => {
        if i.input_len() == input.input_len() {
          let e = ErrorKind::SeparatedNonEmptyList;
          Err(Err::Error(Error::from_error_kind(input, e)))
        } else {
          res.push(o);
          input = i;

          let ret;

          loop {
            // get the separator first
            let input_ = input.clone();
            match sep(input_) {
              Err(Err::Error(_)) => {
                ret = Ok((input, res));
                break;
              }
              Err(e) => {
                ret = Err(e);
                break;
              }
              Ok((i2, _)) => {
                let i2_len = i2.input_len();
                if i2_len == input.input_len() {
                  ret = Ok((input, res));
                  break;
                }

                // get the element next
                match f(i2) {
                  Err(Err::Error(_)) => {
                    ret = Ok((input, res));
                    break;
                  }
                  Err(e) => {
                    ret = Err(e);
                    break;
                  }
                  Ok((i3, o3)) => {
                    if i3.input_len() == i2_len {
                      ret = Ok((input, res));
                      break;
                    }
                    res.push(o3);
                    input = i3;
                  }
                }
              }
            }
          }

          ret
        }
      }
    }
  }
}

//FIXME: streaming
// this implementation is used for type inference issues in macros
#[doc(hidden)]
#[cfg(feature = "alloc")]
pub fn separated_non_empty_listc<Input, Output, Output2, Error: ParseError<Input>, F, G>(i: Input, sep: G, f: F) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + InputLength,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(Input) -> IResult<Input, Output2, Error>,
{
  separated_non_empty_list(sep, f)(i)
}

//FIXME: streaming
#[cfg(feature = "alloc")]
pub fn many_m_n<Input, Output, Error: ParseError<Input>, F>(m: usize, n: usize, f: F) -> impl Fn(Input) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + InputLength + AtEof,
  F: Fn(Input) -> IResult<Input, Output, Error>,
{
  move |i: Input| {
    let mut res = ::lib::std::vec::Vec::with_capacity(m);
    let mut input = i.clone();
    let mut count: usize = 0;
    let mut err = false;
    let mut incomplete: Option<Needed> = None;
    let mut failure: Option<Error> = None;

    loop {
      if count == n {
        break;
      }
      let _i = input.clone();
      match f(_i) {
        Ok((i, o)) => {
          // do not allow parsers that do not consume input (causes infinite loops)
          if i.input_len() == input.input_len() {
            break;
          }
          res.push(o);
          input = i;
          count += 1;
        }
        Err(Err::Error(_)) => {
          err = true;
          break;
        }
        Err(Err::Incomplete(i)) => {
          incomplete = Some(i);
          break;
        }
        Err(Err::Failure(e)) => {
          failure = Some(e);
          break;
        }
      }
    }

    if count < m {
      if err {
        Err(Err::Error(Error::from_error_kind(i, ErrorKind::ManyMN)))
      } else {
        match failure {
          Some(i2) => Err(Err::Failure(i2)),
          None => match incomplete {
            Some(i2) => need_more(i, i2),
            None => need_more(i, Needed::Unknown),
          },
        }
      }
    } else {
      match failure {
        Some(i) => Err(Err::Failure(i)),
        None => match incomplete {
          Some(i2) => need_more(i, i2),
          None => Ok((input, res)),
        },
      }
    }
  }
}

//FIXME: streaming
// this implementation is used for type inference issues in macros
#[doc(hidden)]
#[cfg(feature = "alloc")]
pub fn many_m_nc<Input, Output, Error: ParseError<Input>, F>(i: Input, m: usize, n: usize, f: F) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + InputLength + AtEof,
  F: Fn(Input) -> IResult<Input, Output, Error>,
{
  many_m_n(m, n, f)(i)
}

//FIXME: streaming
pub fn many0_count<Input, Output, Error: ParseError<Input>, F>(i: Input, f: F) -> IResult<Input, usize, Error>
where
  Input: Clone + InputLength + AtEof + PartialEq,
  F: Fn(Input) -> IResult<Input, Output, Error>,
{
  let ret;
  let mut count: usize = 0;
  let mut input = i.clone();

  loop {
    let input_ = input.clone();
    match f(input_) {
      Ok((i, _)) => {
        //  loop trip must always consume (otherwise infinite loops)
        if i == input {
          if i.at_eof() {
            ret = Ok((input, count));
          } else {
            ret = Err(Err::Error(Error::from_error_kind(input, ErrorKind::Many0Count)));
          }
          break;
        }
        count += 1;
        input = i;
      }

      Err(Err::Error(_)) => {
        ret = Ok((input, count));
        break;
      }

      Err(e) => {
        ret = Err(e);
        break;
      }
    }
  }

  ret
}

//FIXME: streaming
pub fn many1_count<Input, Output, Error: ParseError<Input>, F>(i: Input, f: F) -> IResult<Input, usize, Error>
where
  Input: Clone + InputLength + AtEof + PartialEq,
  F: Fn(Input) -> IResult<Input, Output, Error>,
{
  let i_ = i.clone();
  match f(i_) {
    Err(Err::Error(_)) => Err(Err::Error(Error::from_error_kind(i, ErrorKind::Many1Count))),
    Err(Err::Failure(_)) => Err(Err::Failure(Error::from_error_kind(i, ErrorKind::Many1Count))),
    Err(i) => Err(i),
    Ok((i1, _)) => {
      let mut count: usize = 1;
      let mut input = i1;
      let mut error = None;

      loop {
        let input_ = input.clone();
        match f(input_) {
          Err(Err::Error(_)) => {
            break;
          }

          Err(e) => {
            error = Some(e);
            break;
          }

          Ok((i, _)) => {
            if i.input_len() == input.input_len() {
              break;
            }
            count += 1;
            input = i;
          }
        }
      }

      match error {
        Some(e) => Err(e),
        None => Ok((input, count)),
      }
    }
  }
}

#[cfg(feature = "alloc")]
pub fn count<Input, Output, Error: ParseError<Input>, F>(f: F, count: usize) -> impl Fn(Input) -> IResult<Input, Vec<Output>, Error>
where
  Input: Clone + InputLength + AtEof + PartialEq,
  F: Fn(Input) -> IResult<Input, Output, Error>,
{
  move |i: Input | {
    let mut input = i.clone();
    let mut res = ::lib::std::vec::Vec::with_capacity(count);

    for _ in 0..count {
      let input_ = input.clone();
      match f(input_) {
        Ok((i, o)) => {
          res.push(o);
          input = i;
        }
        Err(Err::Error(e)) => {
          fn unify_types<T>(_: &T, _: &T) {}
          let e2 = Error::from_error_kind(i, ErrorKind::Count);
          unify_types(&e, &e2);

          return Err(Err::Error(e2));
        }
        Err(e) => {
          return Err(e);
        }
      }
    }

    Ok((input, res))
  }
}
//FIXME: streaming
pub fn fold_many0<Input, Output, Error: ParseError<Input>, F, G, R: Clone>(f: F, init: R, g: G) -> impl Fn(Input) -> IResult<Input, R, Error>
where
  Input: Clone + InputLength + AtEof + PartialEq,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(R, Output) -> R,
{
  move |i: Input| {
    let mut res = init.clone();
    let mut input = i.clone();

    loop {
      let i_ = input.clone();
      match f(i_) {
        Ok((i, o)) => {
          // loop trip must always consume (otherwise infinite loops)
          if i == input {
            return if i.at_eof() {
              Ok((input, res))
            } else {
              Err(Err::Error(Error::from_error_kind(input, ErrorKind::Many0)))
            }
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

//FIXME: streaming
pub fn fold_many1<Input, Output, Error: ParseError<Input>, F, G, R: Clone>(f: F, init: R, g: G) -> impl Fn(Input) -> IResult<Input, R, Error>
where
  Input: Clone + InputLength + AtEof + PartialEq,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(R, Output) -> R,
{
  move |i: Input| {
    let _i = i.clone();
    match f(_i) {
      Err(Err::Error(_)) => Err(Err::Error(Error::from_error_kind(i, ErrorKind::Many1))),
      Err(Err::Failure(_)) => Err(Err::Failure(Error::from_error_kind(i, ErrorKind::Many1))),
      Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
      Ok((i1, o1)) => {
        let mut acc = g(init.clone(), o1);
        let mut input = i1;
        loop {
          let _input = input.clone();
          match f(_input) {
            Err(Err::Error(_)) => {
              break;
            }
            Err(Err::Incomplete(i2)) => {
              return need_more(i,i2);
            }
            Err(Err::Failure(e)) => {
              return Err(Err::Failure(e));
            }
            Ok((i, o)) => {
              if i.input_len() == input.input_len() {
                if !i.at_eof() {
                  return Err(Err::Failure(Error::from_error_kind(i, ErrorKind::Many1)));
                }
                break;
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
pub fn fold_many1c<Input, Output, Error: ParseError<Input>, F, G, R: Clone>(i: Input, f: F, init: R, g: G) -> IResult<Input, R, Error>
where
  Input: Clone + InputLength + AtEof + PartialEq,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(R, Output) -> R,
{
  fold_many1(f, init, g)(i)
}

//FIXME: streaming
pub fn fold_many_m_n<Input, Output, Error: ParseError<Input>, F, G, R: Clone>(m: usize, n: usize, f: F, init: R, g: G) -> impl Fn(Input) ->IResult<Input, R, Error>
where
  Input: Clone + InputLength + AtEof + PartialEq,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(R, Output) -> R,
{
  move |i: Input| {
    let mut acc = init.clone();
    let mut input = i.clone();
    for count in 0..n {
      let _input = input.clone();
      match f(_input) {
        Ok((i, o)) => {
          // do not allow parsers that do not consume input (causes infinite loops)
          if i.input_len() == input.input_len() {
            if count < m {
              return Err(Err::Incomplete(Needed::Unknown));
            } else {
              break;
            }
          }
          acc = g(acc, o);
          input = i;
        }
        //FInputXMError: handle failure properly
        Err(Err::Error(_)) | Err(Err::Failure(_)) => if count < m {
          return Err(Err::Error(Error::from_error_kind(i, ErrorKind::ManyMN)));
        } else {
          break;
        }

        Err(Err::Incomplete(i)) => {
          return Err(Err::Incomplete(i));
        }
      }
    }

    Ok((input, acc))
  }
}

#[doc(hidden)]
pub fn fold_many_m_nc<Input, Output, Error: ParseError<Input>, F, G, R: Clone>(i: Input, m: usize, n: usize, f: F, init: R, g: G) -> IResult<Input, R, Error>
where
  Input: Clone + InputLength + AtEof + PartialEq,
  F: Fn(Input) -> IResult<Input, Output, Error>,
  G: Fn(R, Output) -> R,
{
  fold_many_m_n(m, n, f, init, g)(i)
}

pub fn length_value<Input, Output, N, Error: ParseError<Input>, F, G>(mut f: F, mut g: G) -> impl FnOnce(Input) -> IResult<Input, Output, Error>
where
  Input: Clone + InputLength + InputTake,
  N: Copy + Into<usize>,
  F: FnMut(Input) -> IResult<Input, N, Error>,
  G: FnMut(Input) -> IResult<Input, Output, Error>,
{
  move |i: Input| {
    let (i, length) = f(i)?;
    if i.input_len() < length.into() {
      Err(Err::Incomplete(Needed::Size(length.into())))
    } else {
      let (rest, i) = i.take_split(length.into());
      match g(i.clone()) {
        Err(Err::Incomplete(_)) =>
          Err(Err::Error(Error::from_error_kind(i, ErrorKind::Complete))),
        Err(e) => Err(e),
        Ok((_, o)) => Ok((rest,o)),
      }
    }
  }
}

#[doc(hidden)]
pub fn length_valuec<Input, Output, N, Error: ParseError<Input>, F, G>(i: Input, mut f: F, mut g: G) -> IResult<Input, Output, Error>
where
  Input: Clone + InputLength + InputTake,
  N: Copy + Into<usize>,
  F: FnMut(Input) -> IResult<Input, N, Error>,
  G: FnMut(Input) -> IResult<Input, Output, Error>,
{
  length_value(f, g)(i)
}
