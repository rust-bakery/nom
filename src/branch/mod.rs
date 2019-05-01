//! choice combinators

#[macro_use]
mod macros;

use error::ErrorKind;
use error::ParseError;
use internal::{Err, IResult};

pub fn or<I: Clone, O, E: ParseError<I>, F, G>(f: F, g: G) -> impl Fn(I) -> IResult<I, O, E>
where
  F: Fn(I) -> IResult<I, O, E>,
  G: Fn(I) -> IResult<I, O, E>,
{
  move |i: I| match f(i.clone()) {
    Err(Err::Error(e)) => g(i).map_err(|e2| match e2 {
      Err::Error(e2) => Err::Error(e.or(e2)),
      e2 => e2,
    }),
    res => res,
  }
}

/// helper trait for arguments to [alt]
pub trait Alt<I, O, E> {
  fn choice(&self, input: I) -> IResult<I, O, E>;
}

pub fn alt<I: Clone, O, E: ParseError<I>, List: Alt<I, O, E>>(l: List) -> impl Fn(I) -> IResult<I, O, E> {
  move |i: I| l.choice(i)
}

/// helper trait for arguments to [permutation]
pub trait Permutation<I, O, E> {
  fn permutation(&self, input: I) -> IResult<I, O, E>;
}

pub fn permutation<I: Clone, O, E: ParseError<I>, List: Permutation<I, O, E>>(l: List) -> impl Fn(I) -> IResult<I, O, E> {
  move |i: I| l.permutation(i)
}

macro_rules! alt_trait(
  ($first:ident $second:ident $($id: ident)+) => (
    alt_trait!(__impl $first $second; $($id)+);
  );
  (__impl $($current:ident)*; $head:ident $($id: ident)+) => (
    alt_trait_impl!($($current)*);

    alt_trait!(__impl $($current)* $head; $($id)+);
  );
  (__impl $($current:ident)*; $head:ident) => (
    alt_trait_impl!($($current)*);
    alt_trait_impl!($($current)* $head);
  );
);

macro_rules! alt_trait_impl(
  ($($id:ident)+) => (
    impl<
      Input: Clone, Output, Error: ParseError<Input>,
      $($id: Fn(Input) -> IResult<Input, Output, Error>),+
    > Alt<Input, Output, Error> for ( $($id),+ ) {

      fn choice(&self, input: Input) -> IResult<Input, Output, Error> {
        let mut err = None;
        alt_trait_inner!(0, self, input, err, $($id)+);

        Err(Err::Error(Error::append(input, ErrorKind::Alt, err.unwrap())))
      }
    }
  );
);

macro_rules! alt_trait_inner(
  ($it:tt, $self:expr, $input:expr, $err:expr, $head:ident $($id:ident)+) => (
    match $self.$it($input.clone()) {
      Err(Err::Error(e)) => {
        if $err.is_none() {
          $err = Some(e);
        } else {
          $err = Some($err.unwrap().or(e));
        }
        succ!($it, alt_trait_inner!($self, $input, $err, $($id)+))
      },
      res => return res,
    }
  );
  ($it:tt, $self:expr, $input:expr, $err:expr, $head:ident) => (
    match $self.$it($input.clone()) {
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

alt_trait!(A B C D E F G H I J K L M N O P Q R S T U);

macro_rules! permutation_trait(
  ($name1:ident $ty1:ident, $name2:ident $ty2:ident) => (
    permutation_trait_impl!($name1 $ty1, $name2 $ty2);
  );
  ($name1:ident $ty1:ident, $name2: ident $ty2:ident, $($name:ident $ty:ident),*) => (
    permutation_trait!(__impl $name1 $ty1, $name2 $ty2; $($name $ty),*);
  );
  (__impl $($name:ident $ty: ident),+; $name1:ident $ty1:ident, $($name2:ident $ty2:ident),*) => (
    permutation_trait_impl!($($name $ty),+);
    permutation_trait!(__impl $($name $ty),+ , $name1 $ty1; $($name2 $ty2),*);
  );
  (__impl $($name:ident $ty: ident),+; $name1:ident $ty1:ident) => (
    permutation_trait_impl!($($name $ty),+);
    permutation_trait_impl!($($name $ty),+, $name1 $ty1);
  );
);

macro_rules! permutation_trait_impl(
  ($($name:ident $ty: ident),+) => (
    impl<
      Input: Clone, $($ty),+ , Error: ParseError<Input>,
      $($name: Fn(Input) -> IResult<Input, $ty, Error>),+
    > Permutation<Input, ( $($ty),+ ), Error> for ( $($name),+ ) {

      fn permutation(&self, mut input: Input) -> IResult<Input, ( $($ty),+ ), Error> {
        let mut res = permutation_init!((), $($name),+);

        loop {
          let mut all_done = true;
          permutation_trait_inner!(0, self, input, res, all_done, $($name)+);

          //if we reach that part, it means none of the parsers were able to read anything
          if !all_done {
            //FIXME: should wrap the error returned by the child parser
            return Err(Err::Error(error_position!(input, ErrorKind::Permutation)));
          }
          break;
        }

        if let Some(unwrapped_res) = { permutation_trait_unwrap!(0, (), res, $($name),+) } {
          Ok((input, unwrapped_res))
        } else {
          Err(Err::Error(error_position!(input, ErrorKind::Permutation)))
        }
      }
    }
  );
);

macro_rules! permutation_trait_inner(
  ($it:tt, $self:expr, $input:ident, $res:expr, $all_done:expr, $head:ident $($id:ident)+) => ({
    if $res.$it.is_none() {
      match $self.$it($input.clone()) {
        Ok((i,o))     => {
          $input = i;
          $res.$it = Some(o);
          continue;
        },
        Err(Err::Error(_)) => {
          $all_done = false;
        },
        Err(e) => {
          return Err(e);
        }
      };
    }
    succ!($it, permutation_trait_inner!($self, $input, $res, $all_done, $($id)*));
  });
  ($it:tt, $self:expr, $input:ident, $res:expr, $all_done:expr, $head:ident) => ({
    if $res.$it.is_none() {
      match $self.$it($input.clone()) {
        Ok((i,o))     => {
          $input = i;
          $res.$it = Some(o);
          continue;
        },
        Err(Err::Error(_)) => {
          $all_done = false;
        },
        Err(e) => {
          return Err(e);
        }
      };
    }
  });
);

#[doc(hidden)]
#[macro_export(local_inner_macros)]
macro_rules! permutation_trait_unwrap (
  ($it:tt,  (), $res:ident, $e:ident, $($name:ident),+) => ({
    let res = $res.$it;
    if res.is_some() {
      succ!($it, permutation_trait_unwrap!((res.unwrap()), $res, $($name),+))
    } else {
      $crate::lib::std::option::Option::None
    }
  });

  ($it:tt, ($($parsed:expr),*), $res:ident, $e:ident, $($name:ident),+) => ({
    let res = $res.$it;
    if res.is_some() {
      succ!($it, permutation_trait_unwrap!(($($parsed),* , res.unwrap()), $res, $($name),+))
    } else {
      $crate::lib::std::option::Option::None
    }
  });

  ($it:tt, ($($parsed:expr),*), $res:ident, $name:ident) => ({
    let res = $res.$it;
    if res.is_some() {
      $crate::lib::std::option::Option::Some(($($parsed),* , res.unwrap() ))
    } else {
      $crate::lib::std::option::Option::None
    }
  });

);

permutation_trait!(FnA A, FnB B, FnC C, FnD D, FnE E, FnF F, FnG G, FnH H, FnI I, FnJ J, FnK K, FnL L, FnM M, FnN N, FnO O, FnP P, FnQ Q, FnR R, FnS S, FnT T, FnU U);
