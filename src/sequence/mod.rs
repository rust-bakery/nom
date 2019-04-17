#[macro_use]
mod macros;

use internal::IResult;
use error::ParseError;

pub fn pair<I, O1, O2, E: ParseError<I>, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, (O1, O2), E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  move |input: I| {
    let (input, o1) = first(input)?;
    second(input).map(|(i, o2)| (i, (o1, o2)))
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
pub fn pairc<I, O1, O2, E: ParseError<I>, F, G>(input: I, first: F, second: G) -> IResult<I, (O1, O2), E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  pair(first, second)(input)
}

pub fn preceded<I, O1, O2, E: ParseError<I>, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  move |input: I| {
    let (input, _) = first(input)?;
    second(input)
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
pub fn precededc<I, O1, O2, E: ParseError<I>, F, G>(input: I, first: F, second: G) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  preceded(first, second)(input)
}

pub fn terminated<I, O1, O2, E: ParseError<I>, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, O1, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  move |input: I| {
    let (input, o1) = first(input)?;
    second(input).map(|(i, _)| (i, o1))
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
pub fn terminatedc<I, O1, O2, E: ParseError<I>, F, G>(input: I, first: F, second: G) -> IResult<I, O1, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  terminated(first, second)(input)
}

pub fn separated_pair<I, O1, O2, O3, E: ParseError<I>, F, G, H>(first: F, sep: G, second: H) -> impl Fn(I) -> IResult<I, (O1, O3), E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  H: Fn(I) -> IResult<I, O3, E>,
{
  move |input: I| {
    let (input, o1) = first(input)?;
    let (input, _) = sep(input)?;
    second(input).map(|(i, o2)| (i, (o1, o2)))
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
pub fn separated_pairc<I, O1, O2, O3, E: ParseError<I>, F, G, H>(input: I, first: F, sep: G, second: H) -> IResult<I, (O1, O3), E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  H: Fn(I) -> IResult<I, O3, E>,
{
  separated_pair(first, sep, second)(input)
}

pub fn delimited<I, O1, O2, O3, E: ParseError<I>, F, G, H>(first: F, sep: G, second: H) -> impl Fn(I) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  H: Fn(I) -> IResult<I, O3, E>,
{
  move |input: I| {
    let (input, _) = first(input)?;
    let (input, o2) = sep(input)?;
    second(input).map(|(i, _)| (i, o2))
  }
}

// this implementation is used for type inference issues in macros
#[doc(hidden)]
pub fn delimitedc<I, O1, O2, O3, E: ParseError<I>, F, G, H>(input: I, first: F, sep: G, second: H) -> IResult<I, O2, E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
  H: Fn(I) -> IResult<I, O3, E>,
{
  delimited(first, sep, second)(input)
}

pub trait Tuple<I,O,E> {
  fn parse(&self, input: I) -> IResult<I,O,E>;
}

macro_rules! tuple_trait(
  ($name1:ident $ty1:ident, $name2: ident $ty2:ident, $($name:ident $ty:ident),*) => (
    tuple_trait!(__impl $name1 $ty1, $name2 $ty2; $($name $ty),*);
  );
  (__impl $($name:ident $ty: ident),+; $name1:ident $ty1:ident, $($name2:ident $ty2:ident),*) => (
    tuple_trait_impl!($($name $ty),+);
    tuple_trait!(__impl $($name $ty),+ , $name1 $ty1; $($name2 $ty2),*);
  );
  (__impl $($name:ident $ty: ident),+; $name1:ident $ty1:ident) => (
    tuple_trait_impl!($($name $ty),+);
    tuple_trait_impl!($($name $ty),+, $name1 $ty1);
  );
);

macro_rules! tuple_trait_impl(
  ($($name:ident $ty: ident),+) => (
    impl<
      Input: Clone, $($ty),+ , Error: ParseError<Input>,
      $($name: Fn(Input) -> IResult<Input, $ty, Error>),+
    > Tuple<Input, ( $($ty),+ ), Error> for ( $($name),+ ) {

      fn parse(&self, input: Input) -> IResult<Input, ( $($ty),+ ), Error> {
        tuple_trait_inner!(0, self, input, (), $($name)+)

      }
    }
  );
);

macro_rules! tuple_trait_inner(
  ($it:tt, $self:expr, $input:expr, (), $head:ident $($id:ident)+) => ({
    let (i, o) = acc!($it, $self)($input.clone())?;

    succ!($it, tuple_trait_inner!($self, i, ( o ), $($id)+))
  });
  ($it:tt, $self:expr, $input:expr, ($($parsed:tt)*), $head:ident $($id:ident)+) => ({
    let (i, o) = acc!($it, $self)($input.clone())?;

    succ!($it, tuple_trait_inner!($self, i, ($($parsed)* , o), $($id)+))
  });
  ($it:tt, $self:expr, $input:expr, ($($parsed:tt)*), $head:ident) => ({
    let (i, o) = acc!($it, $self)($input.clone())?;

    Ok((i, ($($parsed)* , o)))
  });
);

tuple_trait!(FnA A, FnB B, FnC C, FnD D, FnE E, FnF F, FnG G, FnH H, FnI I, FnJ J, FnK K, FnL L,
  FnM M, FnN N, FnO O, FnP P, FnQ Q, FnR R, FnS S, FnT T, FnU U);

pub fn tuple<I: Clone, O, E: ParseError<I>, List: Tuple<I,O,E>>(l: List)  -> impl Fn(I) -> IResult<I, O, E> {
  move |i: I| {
    l.parse(i)
  }
}
