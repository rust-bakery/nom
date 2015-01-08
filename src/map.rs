use internal::*;
use internal::IResult::*;

pub trait FlatMapper<O:?Sized,N:?Sized> {
  fn flat_map<F:Fn(O) -> IResult<O,N>>(& self, f: F) -> IResult<O,N>;
}

impl<'a,R,S,T> FlatMapper<&'a[S], T> for IResult<R,&'a [S]> {
  fn flat_map<F:Fn(&'a[S]) -> IResult<&'a[S],T>>(&self, f: F) -> IResult<&'a[S],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }
}

impl<'a,R,T> FlatMapper<&'a str, T> for IResult<R,&'a str> {
  fn flat_map<F:Fn(&'a str) -> IResult<&'a str,T>>(&self, f: F) -> IResult<&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }
}

impl<R,T> FlatMapper<(), T> for IResult<R,()> {
  fn flat_map<F:Fn(()) -> IResult<(),T>>(&self, f: F) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, _) => f(())
    }
  }
}

pub trait Mapper<I,O,N> {
  fn map_opt<F: Fn(O) -> Option<N>>(& self, f: F) -> IResult<I,N>;
  fn map_res<P,F: Fn(O) -> Result<N,P>>(& self, f: F) -> IResult<I,N>;
}

impl<'a,'b,R,S,T> Mapper<&'b [R],&'a[S], T> for IResult<&'b [R],&'a [S]> {
  fn map_opt<F:Fn(&'a[S]) -> Option<T>>(&self, f: F) -> IResult<&'b [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Some(output) => Done(*i, output),
        None         => Error(0)
      }
    }
  }

  fn map_res<U, F: Fn(&'a[S]) -> Result<T,U>>(&self, f: F) -> IResult<&'b [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Ok(output) => Done(*i, output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'a,'b,S,T> Mapper<&'b str, &'a[S], T> for IResult<&'b str,&'a [S]> {
  fn map_opt<F:Fn(&'a[S]) -> Option<T>>(&self, f: F) -> IResult<&'b str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Some(output) => Done(*i, output),
        None         => Error(0)
      }
    }
  }

  fn map_res<U, F: Fn(&'a[S]) -> Result<T,U>>(&self, f: F) -> IResult<&'b str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Ok(output) => Done(*i, output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'a,S,T> Mapper<(), &'a[S], T> for IResult<(),&'a [S]> {
  fn map_opt<F:Fn(&'a[S]) -> Option<T>>(&self, f: F) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => match f(*o) {
        Some(output) => Done((), output),
        None         => Error(0)
      }
    }
  }

  fn map_res<U, F: Fn(&'a[S]) -> Result<T,U>>(&self, f: F) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => match f(*o) {
        Ok(output) => Done((), output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'a,'b,R,T> Mapper<&'b [R],&'a str, T> for IResult<&'b [R],&'a str> {
  fn map_opt<F:Fn(&'a str) -> Option<T>>(&self, f: F) -> IResult<&'b [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Some(output) => Done(*i, output),
        None         => Error(0)
      }
    }
  }

  fn map_res<U, F: Fn(&'a str) -> Result<T,U>>(&self, f: F) -> IResult<&'b [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Ok(output) => Done(*i, output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'a,'b,T> Mapper<&'b str, &'a str, T> for IResult<&'b str,&'a str> {
  fn map_opt<F:Fn(&'a str) -> Option<T>>(&self, f: F) -> IResult<&'b str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Some(output) => Done(*i, output),
        None         => Error(0)
      }
    }
  }

  fn map_res<U, F: Fn(&'a str) -> Result<T,U>>(&self, f: F) -> IResult<&'b str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Ok(output) => Done(*i, output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'a,T> Mapper<(),&'a str, T> for IResult<(),&'a str> {
  fn map_opt<F:Fn(&'a str) -> Option<T>>(&self, f: F) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => match f(*o) {
        Some(output) => Done((), output),
        None         => Error(0)
      }
    }
  }

  fn map_res<U, F: Fn(&'a str) -> Result<T,U>>(&self, f: F) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => match f(*o) {
        Ok(output) => Done((), output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'a,R,T> Mapper<&'a[R], (), T> for IResult<&'a[R],()> {
  fn map_opt<F:Fn(()) -> Option<T>>(&self, f: F) -> IResult<&'a[R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, __) => match f(()) {
        Some(output) => Done(*i, output),
        None         => Error(0)
      }
    }
  }

  fn map_res<U, F: Fn(()) -> Result<T,U>>(&self, f: F) -> IResult<&'a [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Ok(output) => Done(*i, output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'a,T> Mapper<&'a str, (), T> for IResult<&'a str,()> {
  fn map_opt<F:Fn(()) -> Option<T>>(&self, f: F) -> IResult<&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, __) => match f(()) {
        Some(output) => Done(*i, output),
        None         => Error(0)
      }
    }
  }

  fn map_res<U, F: Fn(()) -> Result<T,U>>(&self, f: F) -> IResult<&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Ok(output) => Done(*i, output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<T> Mapper<(),(), T> for IResult<(),()> {
  fn map_opt<F:Fn(()) -> Option<T>>(&self, f: F) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), __) => match f(()) {
        Some(output) => Done((), output),
        None         => Error(0)
      }
    }
  }

  fn map_res<U, F: Fn(()) -> Result<T,U>>(&self, f: F) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => match f(*o) {
        Ok(output) => Done(*o, output),
        Err(_)     => Error(0)
      }
    }
  }
}

pub trait Mapper2<I,O,N> {
  fn map<F: Fn(O) -> N>(& self, f: F) -> IResult<I,N>;
}

impl<'a,R,S,T> Mapper2<&'a R, &'a[S], T> for IResult<&'a R,&'a [S]> {
  fn map<F: Fn(&'a[S]) -> T>(&self, f: F) -> IResult<&'a R,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,R,S,T> Mapper2<&'a [R], &'a[S], T> for IResult<&'a [R],&'a [S]> {
  fn map<F: Fn(&'a[S]) -> T>(&self, f: F) -> IResult<&'a [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,S,T> Mapper2<&'a str, &'a[S], T> for IResult<&'a str,&'a [S]> {
  fn map<F: Fn(&'a[S]) -> T>(&self, f: F) -> IResult<&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,S,T> Mapper2<(), &'a[S], T> for IResult<(),&'a [S]> {
  fn map<F: Fn(&'a[S]) -> T>(&self, f: F) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => Done((),f(*o))
    }
  }
}

impl<'a,R,T> Mapper2<&'a R, (), T> for IResult<&'a R,()> {
  fn map<F: Fn(()) -> T>(&self, f: F) -> IResult<&'a R,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,R,T> Mapper2<&'a [R], (), T> for IResult<&'a [R],()> {
  fn map<F: Fn(()) -> T>(&self, f: F) -> IResult<&'a [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,T> Mapper2<&'a str, (), T> for IResult<&'a str,()> {
  fn map<F: Fn(()) -> T>(&self, f: F) -> IResult<&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,T> Mapper2<(), (), T> for IResult<(),()> {
  fn map<F: Fn(()) -> T>(&self, f: F) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,'b,R,T> Mapper2<&'b R, &'a str, T> for IResult<&'b R,&'a str> {
  fn map<F: Fn(&'a str) -> T>(&self, f: F) -> IResult<&'b R,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,'b,R,T> Mapper2<&'b [R], &'a str, T> for IResult<&'b [R],&'a str> {
  fn map<F: Fn(&'a str) -> T>(&self, f: F) -> IResult<&'b [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}
impl<'a,'b,T> Mapper2<&'b str, &'a str, T> for IResult<&'b str,&'a str> {
  fn map<F: Fn(&'a str) -> T>(&self, f: F) -> IResult<&'b str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,T> Mapper2<(), &'a str, T> for IResult<(),&'a str> {
  fn map<F:  Fn(&'a str) -> T>(&self, f: F) -> IResult<(),T> {
  //fn map<F: Fn(&'a str) -> T>(&self, f: F) -> IResult<(),T> {
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
    println!("{:?}", input);
    Done(input, ())
  }

  #[test]
  fn flat_map_fn() {
    Done((),()).flat_map(local_print);
  }

  #[test]
  fn flat_map_closure() {
    Done((),()).flat_map(|data| { println!("data: {:?}", data); Done(data,())});
    //assert_eq!(decoded.number, 10);
  }

  #[test]
  fn map() {
    let res = Done((),"abcd".as_bytes()).map(|data| { str::from_utf8(data).unwrap() });
    assert_eq!(res, Done((), "abcd"));
    let res2 = Done("abcd".as_bytes(),"efgh".as_bytes()).map(|data| { str::from_utf8(data).unwrap() });
    assert_eq!(res2, Done("abcd".as_bytes(), "efgh"));
    let res3 = Done("abcd","efgh".as_bytes()).map(|data| { str::from_utf8(data).unwrap() });
    assert_eq!(res3, Done("abcd", "efgh"));
  }

  #[test]
  fn map_option() {
    let res = Done((),"abcd".as_bytes()).map_opt(|data| { str::from_utf8(data).ok() });
    assert_eq!(res, Done((), "abcd"));
    let res2 = Done("abcd".as_bytes(),"efgh".as_bytes()).map_opt(|data| { str::from_utf8(data).ok() });
    assert_eq!(res2, Done("abcd".as_bytes(), "efgh"));
    let res3 = Done("abcd","efgh".as_bytes()).map_opt(|data| { str::from_utf8(data).ok() });
    assert_eq!(res3, Done("abcd", "efgh"));
  }

  #[test]
  fn map_result() {
    let res = Done((),"abcd".as_bytes()).map_res(|data| { str::from_utf8(data) });
    assert_eq!(res, Done((), "abcd"));
    let res2 = Done("abcd".as_bytes(),"efgh".as_bytes()).map_res(|data| { str::from_utf8(data) });
    assert_eq!(res2, Done("abcd".as_bytes(), "efgh"));
    let res3 = Done("abcd","efgh".as_bytes()).map_res(|data| { str::from_utf8(data) });
    assert_eq!(res3, Done("abcd", "efgh"));
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
