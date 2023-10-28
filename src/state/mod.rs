//! Tools to carry state through a parser

use core::{
  any::{Any, TypeId},
  cell::RefCell,
  ops::ControlFlow,
};
use std::{collections::HashMap, thread_local};

use crate::{error::ParseError, internal::Err, IResult, OutputM, OutputMode, PResult, Parser};

thread_local!(
  static STATES: RefCell<HashMap<TypeId, Box<dyn Any>>> = RefCell::new(HashMap::new());
);

/// TODO
pub struct State<T: 'static, F> {
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
  let state = State {
    initial: initial_state.clone(),
    parser,
  };

  state
}

///on input
pub fn on_input<T: Clone + 'static, I, E: ParseError<I>, F, G>(
  mut parser: F,
  mut map: G,
) -> impl Parser<I, Output = <F as Parser<I>>::Output, Error = E>
where
  F: Parser<I, Error = E>,
  G: FnMut(&mut T, I) -> ControlFlow<IResult<I, <F as Parser<I>>::Output, E>, I>,
{
  move |input: I| match State::<T, F>::update_input(&mut map, input) {
    ControlFlow::Continue(i) => parser.parse(i),
    ControlFlow::Break(result) => result,
  }
}

impl<T: Clone + 'static, F> State<T, F> {
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

impl<I, F, T: Clone + 'static> Parser<I> for State<T, F>
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

#[cfg(test)]
mod tests {
  use crate::{branch::alt, bytes::complete::tag, sequence::preceded};

  use super::*;

  #[test]
  fn state_update() {
    fn a(i: &str) -> IResult<&str, &str, ()> {
      on_input::<u8, &str, _, _, _>(preceded(tag("a"), b), |state, input| {
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
  fn multistate() {}
}
