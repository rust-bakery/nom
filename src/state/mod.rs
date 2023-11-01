//! Tools to carry state through a parser

use core::{
  any::{Any, TypeId},
  cell::RefCell,
  marker::PhantomData,
  ops::ControlFlow,
};
use std::{collections::HashMap, thread_local};

use crate::{error::ParseError, internal::Err, IResult, OutputM, OutputMode, PResult, Parser};

thread_local!(
  static STATES: RefCell<HashMap<TypeId, Box<dyn Any>>> = RefCell::new(HashMap::new());
);

/// TODO
pub struct InitialState<T: 'static, F> {
  initial: T,
  parser: F,
}

///create
pub fn state<I, E: ParseError<I>, F, T: Clone + 'static>(
  initial_state: T,
  parser: F,
) -> impl Parser<I, Output = <F as Parser<I>>::Output, Error = E>
where
  F: Parser<I, Error = E>,
{
  let state = InitialState {
    initial: initial_state.clone(),
    parser,
  };

  state
}

///on input
pub fn on_input<T: Clone + 'static, I, F, G>(
  mut parser: F,
  mut map: G,
) -> impl Parser<I, Output = <F as Parser<I>>::Output, Error = <F as Parser<I>>::Error>
where
  F: Parser<I>,
  G: FnMut(
    &mut T,
    I,
  ) -> ControlFlow<IResult<I, <F as Parser<I>>::Output, <F as Parser<I>>::Error>, I>,
{
  move |input: I| match InitialState::<T, F>::update_input(&mut map, input) {
    ControlFlow::Continue(i) => parser.parse(i),
    ControlFlow::Break(result) => result,
  }
}

fn st<State, Input, P>(input: Input, parser: P) -> StateParser<State, P>
//impl Parser<Input, Output = <P as Parser<Input>>::Output, Error = <P as Parser<Input>>::Error>
where
  P: Parser<Input>,
{
  StateParser {
    parser,
    st: PhantomData,
  }
}

struct StateParser<State, P> {
  parser: P,
  st: PhantomData<State>,
}

impl<State, Input, P> Parser<Input> for StateParser<State, P>
where
  P: Parser<Input>,
{
  type Output = <P as Parser<Input>>::Output;

  type Error = <P as Parser<Input>>::Error;

  fn process<OM: OutputMode>(
    &mut self,
    input: Input,
  ) -> PResult<OM, Input, Self::Output, Self::Error> {
    todo!()
  }
}

/*
fn st2<State, Input, F, O, E>(f: F) -> impl Parser<Input, Output = O, Error = E>
where
  F: FnMut(State, Input) -> PResult<OM, Input, O, E>,
{
  todo!()
}
*/

/*
trait StateTrait<I>: Parser<I> {
  fn on_input<T: Clone + 'static, G>(
    map: G,
  ) -> impl Parser<I, Output = <Self as Parser<I>>::Output, Error = <Self as Parser<I>>::Error>
  where
    G: FnMut(
      &mut T,
      I,
    )
      -> ControlFlow<IResult<I, <Self as Parser<I>>::Output, <Self as Parser<I>>::Error>, I>;
}

impl<I, P> StateTrait<I> for P
where
  P: Parser<I>,
{
  fn on_input<T: Clone + 'static, G>(
    mut map: G,
  ) -> impl Parser<I, Output = <Self as Parser<I>>::Output, Error = <Self as Parser<I>>::Error>
  where
    G: FnMut(
      &mut T,
      I,
    )
      -> ControlFlow<IResult<I, <Self as Parser<I>>::Output, <Self as Parser<I>>::Error>, I>,
  {
    move |input: I| match InitialState::<T, F>::update_input(&mut map, input) {
      ControlFlow::Continue(i) => parser.parse(i),
      ControlFlow::Break(result) => result,
    }
  }
}*/

struct StateInput<State, P, F> {
  parser: P,
  f: F,
  st: PhantomData<State>,
}

impl<State, Input, P, F> Parser<Input> for StateInput<State, P, F>
where
  P: Parser<Input>,
  F: FnMut(
    &mut State,
    Input,
  ) -> ControlFlow<
    IResult<Input, <Self as Parser<Input>>::Output, <Self as Parser<Input>>::Error>,
    Input,
  >,
{
  type Output = <P as Parser<Input>>::Output;

  type Error = <P as Parser<Input>>::Error;

  fn process<OM: OutputMode>(
    &mut self,
    input: Input,
  ) -> PResult<OM, Input, Self::Output, Self::Error> {
    match InitialState::<State, F>::update_input(&mut self.f, input) {
      ControlFlow::Continue(i) => self
        .parser
        .process::<OutputM<OM::Output, OM::Error, OM::Incomplete>>(i),
      ControlFlow::Break(result) => result,
    }
  }
}

impl<T: Clone + 'static, F> InitialState<T, F> {
  fn update_input<G, Res, Input>(mut fun: G, input: Input) -> Res
  where
    G: FnMut(&mut T, Input) -> Res,
  {
    STATES.with(|states| {
      let mut h = states.borrow_mut();
      let v = h.get_mut(&TypeId::of::<T>());
      let value = v.unwrap();

      fun(value.downcast_mut::<T>().unwrap(), input)
    })
  }

  fn reset(&self) {
    STATES.with(|states| {
      let mut h = states.borrow_mut();
      h.insert(TypeId::of::<T>(), Box::new(self.initial.clone()));
    })
  }
}

impl<I, F, T: Clone + 'static> Parser<I> for InitialState<T, F>
where
  F: Parser<I>,
{
  type Output = <F as Parser<I>>::Output;

  type Error = <F as Parser<I>>::Error;

  #[inline(always)]
  fn process<OM: OutputMode>(&mut self, input: I) -> PResult<OM, I, Self::Output, Self::Error> {
    self.reset();
    match self
      .parser
      .process::<OutputM<OM::Output, OM::Error, OM::Incomplete>>(input)
    {
      Err(Err::Error(e)) => Err(Err::Error(e)),
      Err(Err::Failure(e)) => Err(Err::Failure(e)),
      Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
      Ok((i, o)) => Ok((i, o)),
    }
  }
}
/*
struct StateParser<F> {
  fun: F,
}

impl<I, F, State> Parser<I> for StateParser<F>
where
  F: FnMut(State, I) -> Parser<I>,
{
  type Output = <F as Parser<I>>::Output;

  type Error = <F as Parser<I>>::Error;

  #[inline(always)]
  fn process<OM: OutputMode>(&mut self, input: I) -> PResult<OM, I, Self::Output, Self::Error> {
    self.reset();
    match self
      .parser
      .process::<OutputM<OM::Output, OM::Error, OM::Incomplete>>(input)
    {
      Err(Err::Error(e)) => Err(Err::Error(e)),
      Err(Err::Failure(e)) => Err(Err::Failure(e)),
      Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
      Ok((i, o)) => Ok((i, o)),
    }
  }
}*/

#[cfg(test)]
mod tests {
  use crate::{branch::alt, bytes::complete::tag, sequence::preceded};

  use super::*;

  #[test]
  fn state_update() {
    fn a(i: &str) -> IResult<&str, &str, ()> {
      on_input::<u8, &str, _, _>(preceded(tag("a"), b), |state, input| {
        if *state == 3 {
          ControlFlow::Break(Err(Err::Failure(())))
        } else {
          *state += 1;
          ControlFlow::Continue(input)
        }
      })
      .parse(i)
    }

    fn b(i: &str) -> IResult<&str, &str, ()> {
      preceded(tag("b"), alt((a, tag(".")))).parse(i)
    }

    let mut parser = state(0u8, a);

    assert_eq!(parser.parse("abababab"), Err(Err::Failure(())));

    assert_eq!(parser.parse("abab."), Ok(("", ".")));
  }

  #[test]
  fn multistate() {
    //fn a(i: &str) -> IResult<&str, &str, ()> {
    /*
    st(|state| {
      if state.is_valid() {
        preceded(tag("a"), b).map(|o|
          //NO! double mutable borrow state.update())
      }
    })

    preceded(tag("a"), b)
      .on_input(|state, input| -> ControlFlow)
      .on_output(|state, result| -> result)
      */

    /*on_input::<u8, &str, _, _, _>(preceded(tag("a"), b), |state, input| {
      if *state == 3 {
        ControlFlow::Break(Err(Err::Failure(())))
      } else {
        *state += 1;
        ControlFlow::Continue(input)
      }
    })
    .parse(i)*/
    //}
  }
}
