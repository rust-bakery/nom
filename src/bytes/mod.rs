#[macro_use]
mod macros;

use lib::std::result::Result::*;
use lib::std::ops::RangeFrom;
use traits::{
  need_more, need_more_err, AtEof, Compare, CompareResult, FindSubstring, FindToken, InputIter, InputLength, InputTake,
  InputTakeAtPosition, Slice, ToUsize,
};
use {Err, ErrorKind, IResult, Needed, ParseError};

//FIXME: streaming
/// Recognizes a pattern
///
/// The input data will be compared to the tag combinator's argument and will return the part of
/// the input that matches the argument
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::tag;
/// # fn main() {
/// let parser = |s: &'static str| {
///   tag::<_, _, (_, ErrorKind)>("Hello")(s)
/// };
///
/// assert_eq!(parser("Hello, World!"), Ok((", World!", "Hello")));
/// assert_eq!(parser("Something"), Err(Err::Error(("Something", ErrorKind::Tag))));
/// assert_eq!(parser(""), Err(Err::Incomplete(Needed::Size(5))));
/// # }
/// ```
pub fn tag<'a, T: 'a, Input: 'a, Error: ParseError<Input>>(tag: T) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
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
        let e: ErrorKind = ErrorKind::Tag;
        Err(Err::Error(Error::from_error_kind(i, e)))
      }
    };
    res
  }
}

//FIXME: streaming
/// Recognizes a case insensitive pattern
///
/// The input data will be compared to the tag combinator's argument and will return the part of
/// the input that matches the argument with no regard to case
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::tag_no_case;
/// # fn main() {
/// let parser = |s: &'static str| {
///   tag_no_case::<_, _, (_, ErrorKind)>("hello")(s)
/// };
///
/// assert_eq!(parser("Hello, World!"), Ok((", World!", "Hello")));
/// assert_eq!(parser("hello, World!"), Ok((", World!", "hello")));
/// assert_eq!(parser("HeLlO, World!"), Ok((", World!", "HeLlO")));
/// assert_eq!(parser("Something"), Err(Err::Error(("Something", ErrorKind::Tag))));
/// assert_eq!(parser(""), Err(Err::Incomplete(Needed::Size(5))));
/// # }
/// ```
pub fn tag_no_case<T, Input, Error: ParseError<Input>>(tag: T) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
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
        let e: ErrorKind = ErrorKind::Tag;
        Err(Err::Error(Error::from_error_kind(i, e)))
      }
    };
    res
  }
}

//FIXME: streaming
/// Parse till certain characters is met
///
/// The parser will return the longest slice till  one of the characters of the combinator's argument is met.
///
/// It doesn't consume the matched character, and will return a `Err::Incomplete(Needed::Size(1))` if the
/// pattern wasn't met
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::is_not;
/// # fn main() {
/// let not_space = |s: &'static str| {
///   is_not::<_, _, (_, ErrorKind)>(" \t\r\n")(s)
/// };
///
/// assert_eq!(not_space("Hello, World!"), Ok((" World!", "Hello,")));
/// assert_eq!(not_space("Sometimes\t"), Ok(("\t", "Sometimes")));
/// assert_eq!(not_space("Nospace"), Err(Err::Incomplete(Needed::Size(1))));
/// assert_eq!(not_space(""), Err(Err::Incomplete(Needed::Size(1))));
/// # }
/// ```
pub fn is_not<T, Input, Error: ParseError<Input>>(arr: T) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  T: InputLength + FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::IsNot;
    i.split_at_position1(|c| arr.find_token(c), e)
  }
}

//FIXME: streaming
/// Returns the longest slice of the matches the pattern
///
/// The parser will return the longest slice consisting of the characters in provided in the
/// combinator's argument
///
/// *Streaming version* will return a `Err::Incomplete(Needed::Size(1))` if the pattern wasn't met
/// or if the pattern reaches the end of the input
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::is_a;
/// # fn main() {
/// let hex = |s: &'static str| {
///   is_a::<_, _, (_, ErrorKind)>("1234567890ABCDEF")(s)
/// };
///
/// assert_eq!(hex("123 and voila"), Ok((" and voila", "123")));
/// assert_eq!(hex("DEADBEEF and others"), Ok((" and others", "DEADBEEF")));
/// assert_eq!(hex("BADBABEsomething"), Ok(("something", "BADBABE")));
/// assert_eq!(hex("D15EA5E"), Err(Err::Incomplete(Needed::Size(1))));
/// assert_eq!(hex(""), Err(Err::Incomplete(Needed::Size(1))));
/// # }
/// ```
pub fn is_a<T, Input, Error: ParseError<Input>>(arr: T) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  T: InputLength + FindToken<<Input as InputTakeAtPosition>::Item>,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::IsA;
    i.split_at_position1(|c| !arr.find_token(c), e)
  }
}

//FIXME: streaming
/// Returns the longest slice of the input that matches the predicate
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*
///
/// *Streaming version* will return a `Err::Incomplete(Needed::Size(1))` if the pattern reaches the end of the input
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::{take_while, is_alphabetic};
/// # fn main() {
/// let alpha = |s: &'static [u8]| {
///   take_while::<_, _, (_, ErrorKind)>(is_alphabetic)(s)
/// };
///
/// assert_eq!(alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(alpha(b"12345"), Ok((&b"12345"[..], &b""[..])));
/// assert_eq!(alpha(b"latin"), Err(Err::Incomplete(Needed::Size(1))));
/// assert_eq!(alpha(b""), Err(Err::Incomplete(Needed::Size(1))));
/// # }
/// ```
pub fn take_while<F, Input, Error: ParseError<Input>>(cond: F) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position(|c| !cond(c))
}

//FIXME: streaming
/// Returns the longest slice of the input that matches the predicate
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*
///
/// *Streaming version* will return a `Err::Incomplete(Needed::Size(1))` or if the pattern reaches the end of the input.
/// And will return an `Err(Err::Error((_, ErrorKind::TakeWhile1)))` if the pattern wasn't met
///
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::{take_while1, is_alphabetic};
/// # fn main() {
/// let alpha = |s: &'static [u8]| {
///   take_while1::<_, _, (_, ErrorKind)>(is_alphabetic)(s)
/// };
///
/// assert_eq!(alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(alpha(b"latin"), Err(Err::Incomplete(Needed::Size(1))));
/// assert_eq!(alpha(b"12345"), Err(Err::Error((&b"12345"[..], ErrorKind::TakeWhile1))));
/// # }
/// ```
pub fn take_while1<F, Input, Error: ParseError<Input>>(cond: F) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::TakeWhile1;
    i.split_at_position1(|c| !cond(c), e)
  }
}

//FIXME: streaming
/// Returns the longest slice between m and n of the input that matches the predicate
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*
///
/// *Streaming version* will return a `Err::Incomplete(Needed::Size(1))` or if the pattern reaches the end of the input or is too short.
/// And will return an `Err(Err::Error((_, ErrorKind::TakeWhileMN)))` if the pattern wasn't met
///
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::{take_while_m_n, is_alphabetic};
/// # fn main() {
/// let short_alpha = |s: &'static [u8]| {
///   take_while_m_n::<_, _, (_, ErrorKind)>(3, 6, is_alphabetic)(s)
/// };
///
/// assert_eq!(short_alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(short_alpha(b"lengthy"), Ok((&b"y"[..], &b"length"[..])));
/// assert_eq!(short_alpha(b"latin"), Err(Err::Incomplete(Needed::Size(1))));
/// assert_eq!(short_alpha(b"ed"), Err(Err::Incomplete(Needed::Size(1))));
/// assert_eq!(short_alpha(b"12345"), Err(Err::Error((&b"12345"[..], ErrorKind::TakeWhileMN))));
/// # }
/// ```
pub fn take_while_m_n<F, Input, Error: ParseError<Input>>(m: usize, n: usize, cond: F) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
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
          if input.at_eof() {
            if len >= m && len <= n {
              let res: IResult<_, _, Error> = Ok((input.slice(len..), input));
              res
            } else {
              let e = ErrorKind::TakeWhileMN;
              Err(Err::Error(Error::from_error_kind(input, e)))
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
/// Returns the longest slice of the input till a predicate is met
///
/// The parser will return the longest slice till the given predicate *(a function that
/// takes the input and returns a bool)*
///
/// *Streaming version* will return a `Err::Incomplete(Needed::Size(1))` if the match reaches the
/// end of input or if there was not match
///
///
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::{take_till, is_digit};
/// # fn main() {
/// let till_colon = |s: &'static str| {
///   take_till::<_, _, (_, ErrorKind)>(|c| c == ':')(s)
/// };
///
/// assert_eq!(till_colon("latin:123"), Ok((":123", "latin")));
/// assert_eq!(till_colon(":empty matched"), Ok((":empty matched", ""))); //allowed
/// assert_eq!(till_colon("12345"), Err(Err::Incomplete(Needed::Size(1))));
/// assert_eq!(till_colon(""), Err(Err::Incomplete(Needed::Size(1))));
/// # }
/// ```
pub fn take_till<F, Input, Error: ParseError<Input>>(cond: F) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| i.split_at_position(cond)
}

//FIXME: streaming
/// Returns the longest (atleast 1) slice of the input till a predicate is met
///
/// The parser will return the longest slice till the given predicate *(a function that
/// takes the input and returns a bool)*
///
/// *Streaming version* will return a `Err::Incomplete(Needed::Size(1))` if the match reaches the
/// end of input or if there was not match
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::{take_till1, is_digit};
/// # fn main() {
/// let till_colon = |s: &'static str| {
///   take_till1::<_, _, (_, ErrorKind)>(|c| c == ':')(s)
/// };
///
/// assert_eq!(till_colon("latin:123"), Ok((":123", "latin")));
/// assert_eq!(till_colon(":empty matched"), Err(Err::Error((":empty matched", ErrorKind::TakeTill1))));
/// assert_eq!(till_colon("12345"), Err(Err::Incomplete(Needed::Size(1))));
/// assert_eq!(till_colon(""), Err(Err::Incomplete(Needed::Size(1))));
/// # }
/// ```
pub fn take_till1<F, Input, Error: ParseError<Input>>(cond: F) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
where
  Input: InputTakeAtPosition,
  F: Fn(<Input as InputTakeAtPosition>::Item) -> bool,
{
  move |i: Input| {
    let e: ErrorKind = ErrorKind::TakeTill1;
    i.split_at_position1(cond, e)
  }
}

//FIXME: streaming
/// Returns a slice of the first N number of input (Input[..N])
///
///
/// *Streaming version* will return a `Err::Incomplete(Needed::Size(N))` where N is the
/// argument if the input is less than the length provided
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::take;
/// # fn main() {
/// let take6 = |s: &'static str| {
///   take::<_, _, (_, ErrorKind)>(6usize)(s)
/// };
///
/// assert_eq!(take6("1234567"), Ok(("7", "123456")));
/// assert_eq!(take6("things"), Ok(("", "things")));
/// assert_eq!(take6("short"), Err(Err::Incomplete(Needed::Size(6)))); //N doesn't change
/// assert_eq!(take6(""), Err(Err::Incomplete(Needed::Size(6))));
/// # }
/// ```
pub fn take<C, Input, Error: ParseError<Input>>(count: C) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
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
/// Returns the longest slice till it matches the pattern
///
/// *Streaming version* will return a `Err::Incomplete(Needed::Size(N))` if the input doesn't
/// contain the pattern
/// argument if the input is less than the length provided
/// ```rust
/// # #[macro_use] extern crate nom;
/// # use nom::{Err, ErrorKind, Needed};
/// use nom::take_until;
/// # fn main() {
/// let until_eof = |s: &'static str| {
///   take_until::<_, _, (_, ErrorKind)>("eof")(s)
/// };
///
/// assert_eq!(until_eof("hello, worldeof"), Ok(("eof", "hello, world")));
/// assert_eq!(until_eof("hello, world"), Err(Err::Incomplete(Needed::Size(3))));
/// assert_eq!(until_eof(""), Err(Err::Incomplete(Needed::Size(3))));
/// # }
/// ```
pub fn take_until<T, Input, Error: ParseError<Input>>(tag: T) -> impl FnOnce(Input) -> IResult<Input, Input, Error>
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
