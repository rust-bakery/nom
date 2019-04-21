//! choice combinators

#[macro_use]
mod macros;

use internal::{Err, IResult};
use error::ParseError;
use error::ErrorKind;

pub fn or<I: Clone, O, E: ParseError<I>, F, G>(f: F, g: G) -> impl Fn(I) -> IResult<I, O, E>
where
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(I) -> IResult<I, O, E>,
{
  move |i: I| {
    match f(i.clone()) {
      Err(Err::Error(e)) => g(i).map_err(|e2| match e2 {
        Err::Error(e2) => Err::Error(e.or(e2)),
        e2 => e2,
      }),
      res => res
    }
  }
}

pub trait Alt<I,O,E> {
  fn parse(&self, input: I) -> IResult<I,O,E>;
}

macro_rules! tuple_choice(
  ($first:ident $second:ident $($id: ident)+) => (
    tuple_choice!(__impl $first $second; $($id)+);
  );
  (__impl $($current:ident)*; $head:ident $($id: ident)+) => (
    tuple_choice_impl!($($current)*);

    tuple_choice!(__impl $($current)* $head; $($id)+);
  );
  (__impl $($current:ident)*; $head:ident) => (
    tuple_choice_impl!($($current)*);
    tuple_choice_impl!($($current)* $head);
  );
);

macro_rules! tuple_choice_impl(
  ($($id:ident)+) => (
    impl<
      Input: Clone, Output, Error: ParseError<Input>,
      $($id: Fn(Input) -> IResult<Input, Output, Error>),+
    > Alt<Input, Output, Error> for ( $($id),+ ) {

      fn parse(&self, input: Input) -> IResult<Input, Output, Error> {
        let mut err = None;
        tuple_choice_inner!(0, self, input, err, $($id)+);

        Err(Err::Error(Error::append(input, ErrorKind::Alt, err.unwrap())))
      }
    }
  );
);

macro_rules! tuple_choice_inner(
  ($it:tt, $self:expr, $input:expr, $err:expr, $head:ident $($id:ident)+) => (
    match acc!($it, $self)($input.clone()) {
      Err(Err::Error(e)) => {
        if $err.is_none() {
          $err = Some(e);
        } else {
          $err = Some($err.unwrap().or(e));
        }
        succ!($it, tuple_choice_inner!($self, $input, $err, $($id)+))
      },
      res => return res,
    }
  );
  ($it:tt, $self:expr, $input:expr, $err:expr, $head:ident) => (
    match acc!($it, $self)($input.clone()) {
      Err(Err::Error(e)) => {
        if $err.is_none() {
          $err = Some(e);
        } else {
          $err = Some($err.unwrap().or(e));
        }
      },
      res => return res,
    }
  );
);

tuple_choice!(A B C D E F G H I J K L M N O P Q R S T U);

pub fn alt<I: Clone, O, E: ParseError<I>, List: Alt<I,O,E>>(l: List)  -> impl Fn(I) -> IResult<I, O, E> {
  move |i: I| {
    l.parse(i)
  }
}

