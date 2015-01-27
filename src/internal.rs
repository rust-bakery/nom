use self::IResult::*;

pub type Err = u32;

//#[derive(Debug)]
type IResultClosure<'a,I,O> = Box<FnMut(I) -> IResult<'a,I,O> +'a>;

//type IResultClosure<'a,I,O> = |I|:'a -> IResult<'a,I,O>;
//type IResultClosure<'a,I,O> = Fn<I, IResult<'a,I,O>>;
#[derive(Show,PartialEq,Eq)]
pub enum IResult<'a,I,O> {
  Done(I,O),
  Error(Err),
  //Incomplete(proc(I):'a -> IResult<I,O>)
 // Incomplete(u32)
  Incomplete(IResultClosure<'a,I,O>)
  //Incomplete(|I|:'a -> IResult<'a,I,O>)
  //Incomplete(fn(I) -> IResult<'a,I,O>)
}

impl<'a,I,O> IResult<'a,I,O> {
  pub fn is_done(&self) -> bool {
    match self {
      &Done(_,_) => true,
      _          => false
    }
  }

  pub fn is_err(&self) -> bool {
    match self {
      &Error(_) => true,
      _         => false
    }
  }

  pub fn is_incomplete(&self) -> bool {
    match self {
      &Incomplete(_) => true,
      _              => false
    }
  }
}

pub trait GetInput<I> {
  fn remaining_input(&self) -> Option<I>;
}

pub trait GetOutput<O> {
  fn output(&self) -> Option<O>;
}

impl<'a,'b,I,O> GetInput<&'a[I]> for IResult<'b,&'a[I],O> {
  fn remaining_input(&self) -> Option<&'a[I]> {
    match self {
      &Done(ref i,_) => Some(*i),
      _          => None
    }
  }
}

impl<'a,'b,O> GetInput<()> for IResult<'b,(),O> {
  fn remaining_input(&self) -> Option<()> {
    match self {
      &Done((),_) => Some(()),
      _          => None
    }
  }
}

impl<'a,'b,I,O> GetOutput<&'a[O]> for IResult<'b,I,&'a[O]> {
  fn output(&self) -> Option<&'a[O]> {
    match self {
      &Done(_, ref o) => Some(*o),
      _          => None
    }
  }
}

impl<'a,'b,I> GetOutput<()> for IResult<'b,I,()> {
  fn output(&self) -> Option<()> {
    match self {
      &Done(_,()) => Some(()),
      _          => None
    }
  }
}

