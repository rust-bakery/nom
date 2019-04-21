//! parsers recognizing bytes streams, streaming version

use lib::std::result::Result::*;
use ::lib::std::ops::RangeFrom;
use traits::{
  Compare, CompareResult, FindSubstring, FindToken, InputIter, InputLength, InputTake,
  InputTakeAtPosition, Slice, ToUsize,
};
use internal::{Err, IResult, Needed};
use error::ErrorKind;
use error::ParseError;

pub fn tag<'a, T: 'a, Input:'a, Error: ParseError<Input>>(tag: T) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + Compare<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let tag_len = tag.input_len();
    let t = tag.clone();

    let res: IResult<_, _, Error> = match i.compare(t) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      CompareResult::Incomplete => Err(Err::Incomplete(Needed::Size(tag_len))),
      CompareResult::Error => {
        let e: ErrorKind = ErrorKind::Tag;
        Err(Err::Error(Error::from_error_kind(i, e)))
      }
    };
    res
  }
}

pub fn tag_no_case<T, Input, Error: ParseError<Input>>(tag: T) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + Compare<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let tag_len = tag.input_len();
    let t = tag.clone();

    let res: IResult<_, _, Error> = match (i).compare_no_case(t) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      CompareResult::Incomplete => Err(Err::Incomplete(Needed::Size(tag_len))),
      CompareResult::Error => {
        let e: ErrorKind = ErrorKind::Tag;
        Err(Err::Error(Error::from_error_kind(i, e)))
      }
    };
    res
  }
}

pub fn is_not<T, Input, Error: ParseError<Input>>(arr: T) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  T: InputLength + FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::IsNot;
    i.split_at_position1(|c| arr.find_token(c), e)
  }
}

pub fn is_a<T, Input, Error: ParseError<Input>>(arr: T) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  T: InputLength + FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::IsA;
    i.split_at_position1(|c| !arr.find_token(c), e)
  }
}

pub fn take_while<F, Input, Error: ParseError<Input>>(cond: F) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position(|c| !cond(c))
}

pub fn take_while1<F, Input, Error: ParseError<Input>>(cond: F) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::TakeWhile1;
    i.split_at_position1(|c| !cond(c), e)
  }
}

pub fn take_while_m_n<F, Input, Error: ParseError<Input>>(m: usize, n: usize, cond: F) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + InputIter + InputLength + Slice<RangeFrom<usize>>,
  F: Fn(<Input as InputIter>::RawItem) -> bool,
{
  move |i: Input| {
    let input = i;

    match input.position(|c| !cond(c)) {
      Some(idx) => {
        if idx >= m {
          if idx <= n {
            let res: IResult<_, _, Error> = Ok(input.take_split(idx));
            res
          } else {
            let res: IResult<_, _, Error> = Ok(input.take_split(n));
            res
          }
        } else {
          let e = ErrorKind::TakeWhileMN;
          Err(Err::Error(Error::from_error_kind(input, e)))
        }
      }
      None => {
        let len = input.input_len();
        if len >= n {
          let res: IResult<_, _, Error> = Ok(input.take_split(n));
          res
        } else {
          let needed = if m > len { m - len } else { 1 };
          Err(Err::Incomplete(Needed::Size(needed)))
        }
      }
    }
  }
}

pub fn take_till<F, Input, Error: ParseError<Input>>(cond: F) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position(|c| cond(c))
}

pub fn take_till1<F, Input, Error: ParseError<Input>>(cond: F) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::TakeTill1;
    i.split_at_position1(|c| cond(c), e)
  }
}

pub fn take<C, Input, Error: ParseError<Input>>(count: C) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputIter + InputTake,
  C: ToUsize,
{
  let c = count.to_usize();
  move |i: Input| match i.slice_index(c) {
    None => Err(Err::Incomplete(Needed::Size(c))),
    Some(index) => Ok(i.take_split(index)),
  }
}

pub fn take_until<T, Input, Error: ParseError<Input>>(tag: T) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + FindSubstring<T>,
  T: InputLength+Clone,
{
  move |i: Input| {
    let len = tag.input_len();
    let t = tag.clone();

    let res: IResult<_, _, Error> = match i.find_substring(t) {
      None => Err(Err::Incomplete(Needed::Size(len))),
      Some(index) => Ok(i.take_split(index)),
    };
    res
  }
}
