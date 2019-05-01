//! parsers recognizing bytes streams, complete input version

use error::ErrorKind;
use error::ParseError;
use internal::{Err, IResult};
use lib::std::ops::RangeFrom;
use lib::std::result::Result::*;
use traits::{Compare, CompareResult, FindSubstring, FindToken, InputIter, InputLength, InputTake, InputTakeAtPosition, Slice, ToUsize};

pub fn tag<'a, T: 'a, Input: 'a, Error: ParseError<Input>>(tag: T) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + Compare<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let tag_len = tag.input_len();
    let t = tag.clone();
    let res: IResult<_, _, Error> = match i.compare(t) {
      CompareResult::Ok => Ok(i.take_split(tag_len)),
      _ => {
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
      _ => {
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
    i.split_at_position1_complete(|c| arr.find_token(c), e)
  }
}

pub fn is_a<T, Input, Error: ParseError<Input>>(arr: T) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  T: InputLength + FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::IsA;
    i.split_at_position1_complete(|c| !arr.find_token(c), e)
  }
}

pub fn take_while<F, Input, Error: ParseError<Input>>(cond: F) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position_complete(|c| !cond(c))
}

pub fn take_while1<F, Input, Error: ParseError<Input>>(cond: F) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::TakeWhile1;
    i.split_at_position1_complete(|c| !cond(c), e)
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
            let res: IResult<_, _, Error> = if let Some(index) = input.slice_index(idx) {
              Ok(input.take_split(index))
            } else {
              Err(Err::Error(Error::from_error_kind(input, ErrorKind::TakeWhileMN)))
            };
            res
          } else {
            let res: IResult<_, _, Error> = if let Some(index) = input.slice_index(n) {
              Ok(input.take_split(index))
            } else {
              Err(Err::Error(Error::from_error_kind(input, ErrorKind::TakeWhileMN)))
            };
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
          if len >= m && len <= n {
            let res: IResult<_, _, Error> = Ok((input.slice(len..), input));
            res
          } else {
            let e = ErrorKind::TakeWhileMN;
            Err(Err::Error(Error::from_error_kind(input, e)))
          }
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
  move |i: Input| i.split_at_position_complete(|c| cond(c))
}

pub fn take_till1<F, Input, Error: ParseError<Input>>(cond: F) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::TakeTill1;
    i.split_at_position1_complete(|c| cond(c), e)
  }
}

pub fn take<C, Input, Error: ParseError<Input>>(count: C) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputIter + InputTake,
  C: ToUsize,
{
  let c = count.to_usize();
  move |i: Input| match i.slice_index(c) {
    None => Err(Err::Error(Error::from_error_kind(i, ErrorKind::Eof))),
    Some(index) => Ok(i.take_split(index)),
  }
}

pub fn take_until<T, Input, Error: ParseError<Input>>(tag: T) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: InputTake + FindSubstring<T>,
  T: InputLength + Clone,
{
  move |i: Input| {
    let t = tag.clone();
    let res: IResult<_, _, Error> = match i.find_substring(t) {
      None => Err(Err::Error(Error::from_error_kind(i, ErrorKind::TakeUntil))),
      Some(index) => Ok(i.take_split(index)),
    };
    res
  }
}

pub fn escaped<Input, Error, F, G, O1, O2>(normal: F, control_char: char, escapable: G) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
  Input: Clone + ::traits::Offset + InputLength + InputTake + InputTakeAtPosition + Slice<RangeFrom<usize>> + InputIter,
  <Input as InputIter>::Item: ::traits::AsChar,
  F: Fn(Input) -> IResult<Input, O1, Error>,
  G: Fn(Input) -> IResult<Input, O2, Error>,
  Error: ParseError<Input>,
{
  use traits::AsChar;

  move |input: Input| {
    let mut i = input.clone();

    while i.input_len() > 0 {
      match normal(i.clone()) {
        Ok((i2, _)) => {
          if i2.input_len() == 0 {
            return Ok((input.slice(input.input_len()..), input));
          } else {
            i = i2;
          }
        }
        Err(Err::Error(_)) => {
          // unwrap() should be safe here since index < $i.input_len()
          if i.iter_elements().next().unwrap().as_char() == control_char {
            let next = control_char.len_utf8();
            if next >= i.input_len() {
              return Err(Err::Error(Error::from_error_kind(input, ErrorKind::Escaped)));
            } else {
              match escapable(i.slice(next..)) {
                Ok((i2, _)) => {
                  if i2.input_len() == 0 {
                    return Ok((input.slice(input.input_len()..), input));
                  } else {
                    i = i2;
                  }
                }
                Err(e) => return Err(e),
              }
            }
          } else {
            let index = input.offset(&i);
            return Ok(input.take_split(index));
          }
        }
        Err(e) => {
          return Err(e);
        }
      }
    }

    Ok((input.slice(input.input_len()..), input))
  }
}

#[doc(hidden)]
pub fn escapedc<Input, Error, F, G, O1, O2>(i: Input, normal: F, control_char: char, escapable: G) -> IResult<Input, Input, Error>
where
  Input: Clone + ::traits::Offset + InputLength + InputTake + InputTakeAtPosition + Slice<RangeFrom<usize>> + InputIter,
  <Input as InputIter>::Item: ::traits::AsChar,
  F: Fn(Input) -> IResult<Input, O1, Error>,
  G: Fn(Input) -> IResult<Input, O2, Error>,
  Error: ParseError<Input>,
{
  escaped(normal, control_char, escapable)(i)
}

pub fn escaped_transform<Input, Error, F, G, O1, O2, ExtendItem, Output>(
  normal: F,
  control_char: char,
  transform: G,
) -> impl Fn(Input) -> IResult<Input, Output, Error>
where
  Input: Clone + ::traits::Offset + InputLength + InputTake + InputTakeAtPosition + Slice<RangeFrom<usize>> + InputIter,
  Input: ::traits::ExtendInto<Item = ExtendItem, Extender = Output>,
  O1: ::traits::ExtendInto<Item = ExtendItem, Extender = Output>,
  O2: ::traits::ExtendInto<Item = ExtendItem, Extender = Output>,
  Output: core::iter::Extend<<Input as ::traits::ExtendInto>::Item>,
  Output: core::iter::Extend<<O1 as ::traits::ExtendInto>::Item>,
  Output: core::iter::Extend<<O2 as ::traits::ExtendInto>::Item>,
  <Input as InputIter>::Item: ::traits::AsChar,
  F: Fn(Input) -> IResult<Input, O1, Error>,
  G: Fn(Input) -> IResult<Input, O2, Error>,
  Error: ParseError<Input>,
{
  use traits::AsChar;

  move |input: Input| {
    let mut index = 0;
    let mut res = input.new_builder();

    let i = input.clone();

    while index < i.input_len() {
      let remainder = i.slice(index..);
      match normal(remainder.clone()) {
        Ok((i2, o)) => {
          o.extend_into(&mut res);
          if i2.input_len() == 0 {
            return Ok((i.slice(i.input_len()..), res));
          } else {
            index = input.offset(&i2);
          }
        }
        Err(Err::Error(_)) => {
          // unwrap() should be safe here since index < $i.input_len()
          if remainder.iter_elements().next().unwrap().as_char() == control_char {
            let next = index + control_char.len_utf8();
            let input_len = input.input_len();

            if next >= input_len {
              return Err(Err::Error(Error::from_error_kind(remainder, ErrorKind::EscapedTransform)));
            } else {
              match transform(i.slice(next..)) {
                Ok((i2, o)) => {
                  o.extend_into(&mut res);
                  if i2.input_len() == 0 {
                    return Ok((i.slice(i.input_len()..), res));
                  } else {
                    index = input.offset(&i2);
                  }
                }
                Err(e) => return Err(e),
              }
            }
          } else {
            return Ok((remainder, res));
          }
        }
        Err(e) => return Err(e),
      }
    }
    Ok((input.slice(index..), res))
  }
}

#[doc(hidden)]
pub fn escaped_transformc<Input, Error, F, G, O1, O2, ExtendItem, Output>(
  i: Input,
  normal: F,
  control_char: char,
  transform: G,
) -> IResult<Input, Output, Error>
where
  Input: Clone + ::traits::Offset + InputLength + InputTake + InputTakeAtPosition + Slice<RangeFrom<usize>> + InputIter,
  Input: ::traits::ExtendInto<Item = ExtendItem, Extender = Output>,
  O1: ::traits::ExtendInto<Item = ExtendItem, Extender = Output>,
  O2: ::traits::ExtendInto<Item = ExtendItem, Extender = Output>,
  Output: core::iter::Extend<<Input as ::traits::ExtendInto>::Item>,
  Output: core::iter::Extend<<O1 as ::traits::ExtendInto>::Item>,
  Output: core::iter::Extend<<O2 as ::traits::ExtendInto>::Item>,
  <Input as InputIter>::Item: ::traits::AsChar,
  F: Fn(Input) -> IResult<Input, O1, Error>,
  G: Fn(Input) -> IResult<Input, O2, Error>,
  Error: ParseError<Input>,
{
  escaped_transform(normal, control_char, transform)(i)

}