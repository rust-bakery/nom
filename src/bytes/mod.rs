#[macro_use]
mod macros;

use lib::std::result::Result::*;
use ::lib::std::ops::RangeFrom;
use traits::{
  need_more, need_more_err, AtEof, Compare, CompareResult, FindSubstring, FindToken, InputIter, InputLength, InputTake,
  InputTakeAtPosition, Slice, ToUsize,
};
use {Context, Err, ErrorKind, IResult, Needed};

//FIXME: streaming
pub fn tag<T, Input, Error>(tag: T) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + Compare<T> + AtEof,
  T: InputLength,
{
  move |i: Input| {
    let tag_len = tag.input_len();
    let res: IResult<_, _, Error> = match i.compare(tag) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      CompareResult::Incomplete => need_more(i, Needed::Size(tag_len)),
      CompareResult::Error => {
        let e: ErrorKind<Error> = ErrorKind::Tag;
        Err(Err::Error(Context::Code(i, e)))
      }
    };
    res
  }
}

//FIXME: streaming
pub fn tag_no_case<T, Input, Error>(tag: T) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + Compare<T> + AtEof,
  T: InputLength,
{
  move |i: Input| {
    let tag_len = tag.input_len();

    let res: IResult<_, _, Error> = match (i).compare_no_case(tag) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      CompareResult::Incomplete => need_more(i, Needed::Size(tag_len)),
      CompareResult::Error => {
        let e: ErrorKind<Error> = ErrorKind::Tag;
        Err(Err::Error(Context::Code(i, e)))
      }
    };
    res
  }
}

//FIXME: streaming
pub fn is_not<T, Input, Error>(arr: T) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  T: InputLength + FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ErrorKind<Error> = ErrorKind::IsNot;
    i.split_at_position1(|c| arr.find_token(c), e)
  }
}

//FIXME: streaming
pub fn is_a<T, Input, Error>(arr: T) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  T: InputLength + FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ErrorKind<Error> = ErrorKind::IsA;
    i.split_at_position1(|c| !arr.find_token(c), e)
  }
}

//FIXME: streaming
pub fn take_while<F, Input, Error>(cond: F) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position(|c| !cond(c))
}

//FIXME: streaming
pub fn take_while1<F, Input, Error>(cond: F) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ErrorKind<Error> = ErrorKind::TakeWhile1;
    i.split_at_position1(|c| !cond(c), e)
  }
}

//FIXME: streaming
pub fn take_while_m_n<F, Input, Error>(m: usize, n: usize, cond: F) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + AtEof + InputIter + InputLength + Slice<RangeFrom<usize>>,
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
          let e = ErrorKind::TakeWhileMN::<Error>;
          Err(Err::Error(error_position!(input, e)))
        }
      }
      None => {
        let len = input.input_len();
        if len >= n {
          let res: IResult<_, _, Error> = Ok(input.take_split(n));
          res
        } else {
          if input.at_eof() {
            if len >= m && len <= n {
              let res: IResult<_, _, Error> = Ok((input.slice(len..), input));
              res
            } else {
              let e = ErrorKind::TakeWhileMN::<Error>;
              Err(Err::Error(error_position!(input, e)))
            }
          } else {
            let needed = if m > len { m - len } else { 1 };
            Err(Err::Incomplete(Needed::Size(needed)))
          }
        }
      }
    }
  }
}

//FIXME: streaming
pub fn take_till<F, Input, Error>(cond: F) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position(cond)
}

//FIXME: streaming
pub fn take_till1<F, Input, Error>(cond: F) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ErrorKind<Error> = ErrorKind::TakeTill1;
    i.split_at_position1(cond, e)
  }
}

//FIXME: streaming
pub fn take<C, Input, Error>(count: C) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputIter + InputTake + AtEof,
  C: ToUsize,
{
  let c = count.to_usize();
  move |i: Input| match i.slice_index(c) {
    None => need_more(i, Needed::Size(c)),
    Some(index) => Ok(i.take_split(index)),
  }
}

//FIXME: streaming
pub fn take_until<T, Input, Error>(tag: T) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + FindSubstring<T> + AtEof,
  T: InputLength,
{
  move |i: Input| {
    let len = tag.input_len();

    let res: IResult<_, _, Error> = match i.find_substring(tag) {
      None => need_more_err(i, Needed::Size(len), ErrorKind::TakeUntil),
      Some(index) => Ok(i.take_split(index)),
    };
    res
  }
}
