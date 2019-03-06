#[macro_use]
mod macros;

use internal::{Err,IResult};
use util::ErrorKind;
use traits::{AtEof,InputLength};

pub fn many0c<I: Clone+InputLength+AtEof, O, F>(mut input: I, mut f: F) -> IResult<I, Vec<O>>
  where F: FnMut(I) -> IResult<I, O> {

  let mut acc = Vec::with_capacity(4);

  loop {
    let input_ = input.clone();
    match f(input_) {
      Err(Err::Error(_)) => return Ok((input, acc)),
      Err(Err::Failure(e)) => return  Err(Err::Failure(e)),
      Err(Err::Incomplete(n)) => {
        if input.at_eof() {
          return Ok((input, acc));
        } else {
          return Err(Err::Incomplete(n));
        }
      }
      Ok((i, o)) => {
        if input.input_len() == i.input_len() {
          return Err(Err::Error(error_position!(i, ErrorKind::Many0)))
        }

        input = i;
        acc.push(o);
      }
    }
  }
}

use std::fmt::Debug;
pub fn many1c<I: Clone+Copy+AtEof+InputLength+Debug, O:Debug, F>(input: I, f: F) -> IResult<I, Vec<O>>
  where F: Fn(I) -> IResult<I, O> {
  let input_ = input.clone();
  match f(input_) {
    Err(_) => {
      return Err(Err::Error(error_position!(input, ErrorKind::Many1)))
    },
    Ok((i2, o)) => {
      let mut acc = Vec::with_capacity(4);
      acc.push(o);
      let mut input = i2;

      loop {
        let input_ = input.clone();
        match f(input_) {
          Err(Err::Error(_)) => return Ok((input, acc)),
          Err(Err::Failure(e)) => return  Err(Err::Failure(e)),
          Err(Err::Incomplete(n)) => {
            if input.at_eof() {
              return Ok((input, acc));
            } else {
              return Err(Err::Incomplete(n));
            }
          }
          Ok((i, o)) => {
            if input.input_len() == i.input_len() {
              return Err(Err::Error(error_position!(i, ErrorKind::Many1)))
            }

            input = i;
            acc.push(o);
          }
        }
      }
    }
  }
}

pub fn separated_list<I: Clone+InputLength, O, O2, F, G>(input: I, mut sep: G, mut f: F) -> IResult<I, Vec<O>>
  where F: FnMut(I) -> IResult<I, O>,
        G: FnMut(I) -> IResult<I, O2> {
  let mut acc = Vec::new();
  let (input, o) = f(input)?;
  acc.push(o);

  let mut i = input;

  loop {
    if i.input_len() == 0 {
      return Ok((i, acc));
    }

    let i_ = i.clone();
    match sep(i_) {
      Err(_) => return Ok((i, acc)),
      Ok((i2, _)) => {
        if i.input_len() == i2.input_len() {
          return Err(Err::Error(error_position!(i, ErrorKind::Many0)))
        }

        let i2_ = i2.clone();
        match f(i2_) {
          Err(_) => return Ok((i, acc)),
          Ok((i3, o)) => {
            if i2.input_len() == i3.input_len() {
              return Err(Err::Error(error_position!(i, ErrorKind::Many0)))
            }

            i = i3;
            acc.push(o);
          }
        }
      }
    }
  }
}
