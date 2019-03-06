#[macro_use]
mod macros;

use internal::IResult;

pub fn pairc<I, O1, O2, E, F, G>(input: I, first: F, second: G) -> IResult<I, (O1, O2), E>
  where F: Fn(I) -> IResult<I, O1, E>,
        G: Fn(I) -> IResult<I, O2, E> {

  let (input, o1) = first(input)?;
  second(input).map(|(i, o2)| (i, (o1, o2)))
}

pub fn precededc<I, O1, O2, E, F, G>(input: I, first: F, second: G) -> IResult<I, O2, E>
  where F: Fn(I) -> IResult<I, O1, E>,
        G: Fn(I) -> IResult<I, O2, E> {

  let (input, _) = first(input)?;
  second(input)
}

pub fn terminatedc<I, O1, O2, E, F, G>(input: I, first: F, second: G) -> IResult<I, O1, E>
  where F: Fn(I) -> IResult<I, O1, E>,
        G: Fn(I) -> IResult<I, O2, E> {

  let (input, o1) = first(input)?;
  second(input).map(|(i, _)| (i, o1))
}

pub fn separated_pairc<I, O1, O2, O3, E, F, G, H>(input: I, first: F, sep: G, second: H) -> IResult<I, (O1, O3), E>
  where F: Fn(I) -> IResult<I, O1, E>,
        G: Fn(I) -> IResult<I, O2, E>,
        H: Fn(I) -> IResult<I, O3, E> {

  let (input, o1) = first(input)?;
  let (input, _)  = sep(input)?;
  second(input).map(|(i, o2)| (i, (o1, o2)))
}

// needs FnMut because fold_many0 in tests/reborrow_fold.rs will not compile otherwise
pub fn delimitedc<I, O1, O2, O3, E, F, G, H>(input: I, mut first: F, mut sep: G, mut second: H) -> IResult<I, O2, E>
  where F: FnMut(I) -> IResult<I, O1, E>,
        G: FnMut(I) -> IResult<I, O2, E>,
        H: FnMut(I) -> IResult<I, O3, E> {

  let (input, _) = first(input)?;
  let (input, o2)  = sep(input)?;
  second(input).map(|(i, _)| (i, o2))
}

