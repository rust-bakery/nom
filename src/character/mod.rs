#[macro_use]
mod macros;

pub use self::macros::anychar;

use crate::Context;
use internal::{Err, IResult, Needed};
use std::ops::RangeFrom;
use traits::{need_more, AsChar, AtEof, FindToken, InputIter, InputLength, Slice};
use util::ErrorKind;

pub fn char<I>(c: char) -> impl Fn(I) -> IResult<I, char>
where
  I: Slice<RangeFrom<usize>> + InputIter + AtEof,
  <I as InputIter>::Item: AsChar,
{
  move |i: I| match (i).iter_elements().next().map(|t| {
    let b = t.as_char() == c;
    (&c, b)
  }) {
    None => need_more(i, Needed::Size(1)),
    Some((_, false)) => {
      let e: ErrorKind<u32> = ErrorKind::Char;
      Err(Err::Error(Context::Code(i, e)))
    }
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
  }
}


pub fn one_of<I, T>(list: T) -> impl Fn(I) -> IResult<I, char>
where
  I: Slice<RangeFrom<usize>> + InputIter + AtEof,
  <I as InputIter>::Item: AsChar + Copy,
  T: FindToken<<I as InputIter>::Item>,
{
  move |i: I| match (i).iter_elements().next().map(|c| (c, list.find_token(c))) {
    None => need_more(i, Needed::Size(1)),
    Some((_, false)) => Err(Err::Error(error_position!(i, ErrorKind::OneOf::<u32>))),
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
  }
}

pub fn none_of<I, T>(list: T) -> impl Fn(I) -> IResult<I, char>
where
  I: Slice<RangeFrom<usize>> + InputIter + AtEof,
  <I as InputIter>::Item: AsChar + Copy,
  T: FindToken<<I as InputIter>::Item>,
{
  move |i: I| match (i).iter_elements().next().map(|c| (c, !list.find_token(c))) {
    None => need_more(i, Needed::Size(1)),
    Some((_, false)) => Err(Err::Error(error_position!(i, ErrorKind::NoneOf::<u32>))),
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
  }
}

