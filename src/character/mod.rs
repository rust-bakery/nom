#[macro_use]
mod macros;

pub use self::macros::anychar;

use internal::{Err,IResult,Needed};
use util::ErrorKind;
use traits::{AtEof,Slice,AsChar,InputIter,InputLength,FindToken,need_more};
use crate::Context;
use std::ops::RangeFrom;

pub fn char<I>(c: char) -> impl Fn(I) -> IResult<I, char>
  where I: Slice<RangeFrom<usize>>+InputIter+AtEof,
        <I as InputIter>::Item: AsChar {

  move |i:I| {
    match (i).iter_elements().next().map(|t| {
      let b = t.as_char() == c;
      (&c, b)
    }) {
      None        => need_more(i, Needed::Size(1)),
      Some((_, false)) => {
        let e: ErrorKind<u32> = ErrorKind::Char;
        Err(Err::Error(Context::Code(i, e)))
      },
      Some((c, true))  => Ok(( i.slice(c.len()..), c.as_char() ))
    }
  }
}

pub fn charc<I>(input: I, c: char) -> IResult<I, char>
  where I: Slice<RangeFrom<usize>>+InputIter+AtEof,
        <I as InputIter>::Item: AsChar {

  char(c)(input)
}

pub fn one_of<I,T>(list: T) -> impl Fn(I) -> IResult<I, char>
  where I: Slice<RangeFrom<usize>>+InputIter+AtEof,
        <I as InputIter>::Item: AsChar+Copy,
        T: FindToken<<I as InputIter>::Item> {

  move |i:I| {
    match (i).iter_elements().next().map(|c| {
      (c, list.find_token(c))
    }) {
      None             => need_more(i, Needed::Size(1)),
      Some((_, false)) => Err(Err::Error(error_position!(i, ErrorKind::OneOf::<u32>))),
      Some((c, true))  => Ok(( i.slice(c.len()..), c.as_char() ))
    }
  }
}

pub fn one_ofc<I,T>(input: I, list: T) -> IResult<I, char>
  where I: Slice<RangeFrom<usize>>+InputIter+AtEof,
        <I as InputIter>::Item: AsChar+Copy,
        T: FindToken<<I as InputIter>::Item> {

  one_of(list)(input)
}

pub fn none_of<I,T>(list: T) -> impl Fn(I) -> IResult<I, char>
  where I: Slice<RangeFrom<usize>>+InputIter+AtEof,
        <I as InputIter>::Item: AsChar+Copy,
        T: FindToken<<I as InputIter>::Item> {

  move |i:I| {
    match (i).iter_elements().next().map(|c| {
      (c, !list.find_token(c))
    }) {
      None             => need_more(i, Needed::Size(1)),
      Some((_, false)) => Err(Err::Error(error_position!(i, ErrorKind::NoneOf::<u32>))),
      Some((c, true))  => Ok(( i.slice(c.len()..), c.as_char() ))
    }
  }
}

pub fn none_ofc<I,T>(input: I, list: T) -> IResult<I, char>
  where I: Slice<RangeFrom<usize>>+InputIter+AtEof,
        <I as InputIter>::Item: AsChar+Copy,
        T: FindToken<<I as InputIter>::Item> {

  none_of(list)(input)
}
