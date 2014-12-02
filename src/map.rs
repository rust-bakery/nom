use internal::*;
use internal::IResult::*;

pub trait Mapper<O,N> for Sized? {
  fn flat_map(& self, f: |O| -> IResult<O,N>) -> IResult<O,N>;
  fn map_opt(& self, f: |O| -> Option<N>) -> IResult<O,N>;
}

impl<'a,R,S,T> Mapper<&'a[S], T> for IResult<R,&'a [S]> {
  fn flat_map(&self, f: |&'a[S]| -> IResult<&'a[S],T>) -> IResult<&'a[S],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }

  fn map_opt(&self, f: |&'a[S]| -> Option<T>) -> IResult<&'a[S],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, ref o) => match f(*o) {
        Some(output) => Done(*o, output),
        None         => Error(0)
      }
    }
  }
}

impl<'a,R,T> Mapper<&'a str, T> for IResult<R,&'a str> {
  fn flat_map(&self, f: |&'a str| -> IResult<&'a str,T>) -> IResult<&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }

  fn map_opt(&self, f: |&'a str| -> Option<T>) -> IResult<&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, ref o) => match f(*o) {
        Some(output) => Done(*o, output),
        None         => Error(0)
      }
    }
  }
}

impl<'a,R,T> Mapper<(), T> for IResult<R,()> {
  fn flat_map(&self, f: |()| -> IResult<(),T>) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, _) => f(())
    }
  }

  fn map_opt(&self, f: |()| -> Option<T>) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(_, __) => match f(()) {
        Some(output) => Done((), output),
        None         => Error(0)
      }
    }
  }
}

pub trait Mapper2<O,N,I> for Sized? {
  fn map(& self, f: |O| -> N) -> IResult<I,N>;
}

impl<'a,R,S,T> Mapper2<&'a[S], T, &'a R> for IResult<&'a R,&'a [S]> {
  fn map(&self, f: |&'a[S]| -> T) -> IResult<&'a R,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }   
  }
}

impl<'a,R,S,T> Mapper2<&'a[S], T, &'a [R]> for IResult<&'a [R],&'a [S]> {
  fn map(&self, f: |&'a[S]| -> T) -> IResult<&'a [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }   
  }
}

impl<'a,R,T> Mapper2<(), T, &'a R> for IResult<&'a R,()> {
  fn map(&self, f: |()| -> T) -> IResult<&'a R,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,S,T> Mapper2<&'a[S], T, ()> for IResult<(),&'a [S]> {
  fn map(&self, f: |&'a[S]| -> T) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => Done((),f(*o))
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::IResult;
  use internal::IResult::*;
  use std::str;
  use std::fmt::Show;

  fn local_print<'a,T: Show>(input: T) -> IResult<T, ()> {
    println!("{}", input);
    Done(input, ()) 
  }

  #[test]
  fn flat_map_fn() {
    Done((),()).flat_map(local_print);
  }

  #[test]
  fn flat_map_closure() {
    Done((),()).flat_map(|data| { println!("data: {}", data); Done(data,())});
    //assert_eq!(decoded.number, 10);
  }

  #[test]
  fn map() {
    let res = Done((),"abcd".as_bytes()).map(|data| { str::from_utf8(data).unwrap() }); 
    assert_eq!(res, Done((), "abcd"));
  }

  #[test]
  fn map_2() {
    let res = Done("abcd".as_bytes(),"efgh".as_bytes()).map(|data| { str::from_utf8(data).unwrap() }); 
    assert_eq!(res, Done("abcd".as_bytes(), "efgh"));
  }

  #[test]
  fn t1() {
    let v1:Vec<u8> = vec![1,2,3];
    let v2:Vec<u8> = vec![4,5,6];
    let d = Done(v1.as_slice(), v2.as_slice());
    let res = d.flat_map(local_print);
    assert_eq!(res, Done(v2.as_slice(), ()));
  }
}
