use internal::*;
use internal::IResult::*;

pub trait FlatMapper<O:?Sized,N:?Sized> {
  fn flat_map<'a,F:Fn(O) -> IResult<'a,O,N>>(& self, f: F) -> IResult<O,N>;
}

impl<'a,'b,R,S,T> FlatMapper<&'a[S], T> for IResult<'b,R,&'a [S]> {
  fn flat_map<F:Fn(&'a[S]) -> IResult<&'a[S],T>>(&self, f: F) -> IResult<'b,&'a[S],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }
}

impl<'a,'b,R,T> FlatMapper<&'a str, T> for IResult<'b,R,&'a str> {
  fn flat_map<F:Fn(&'a str) -> IResult<'b,&'a str,T>>(&self, f: F) -> IResult<'b,&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, ref o) => f(*o)
    }
  }
}

impl<'a,R,T> FlatMapper<(), T> for IResult<'a,R,()> {
  fn flat_map<F:Fn(()) -> IResult<'a,(),T>>(&self, f: F) -> IResult<'a,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done(_, _) => f(())
    }
  }
}

pub trait Mapper<I,O,N> {
  fn map_opt<'a,F: Fn(O) -> Option<N>>(& self, f: F) -> IResult<'a,I,N>;
  fn map_res<'a,P,F: Fn(O) -> Result<N,P>>(& self, f: F) -> IResult<'a,I,N>;
}

impl<'a,'b,'c,R,S,T> Mapper<&'b [R],&'a[S], T> for IResult<'c,&'b [R],&'a [S]> {
  fn map_opt<F:Fn(&'a[S]) -> Option<T>>(&self, f: F) -> IResult<'c,&'b [R],T> {
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

impl<'a,'b,'c,S,T> Mapper<&'b str, &'a[S], T> for IResult<'c,&'b str,&'a [S]> {
  fn map_opt<F:Fn(&'a[S]) -> Option<T>>(&self, f: F) -> IResult<'c,&'b str,T> {
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

  fn map_res<U, F: Fn(&'a[S]) -> Result<T,U>>(&self, f: F) -> IResult<'c,&'b str,T> {
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

impl<'a,'b,S,T> Mapper<(), &'a[S], T> for IResult<'b,(),&'a [S]> {
  fn map_opt<F:Fn(&'a[S]) -> Option<T>>(&self, f: F) -> IResult<'b,(),T> {
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

  fn map_res<U, F: Fn(&'a[S]) -> Result<T,U>>(&self, f: F) -> IResult<'b,(),T> {
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

impl<'a,'b,'c,R,T> Mapper<&'b [R],&'a str, T> for IResult<'c,&'b [R],&'a str> {
  fn map_opt<F:Fn(&'a str) -> Option<T>>(&self, f: F) -> IResult<'c,&'b [R],T> {
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

  fn map_res<U, F: Fn(&'a str) -> Result<T,U>>(&self, f: F) -> IResult<'c,&'b [R],T> {
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

impl<'a,'b,'c,T> Mapper<&'b str, &'a str, T> for IResult<'c,&'b str,&'a str> {
  fn map_opt<F:Fn(&'a str) -> Option<T>>(&self, f: F) -> IResult<'c,&'b str,T> {
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

  fn map_res<U, F: Fn(&'a str) -> Result<T,U>>(&self, f: F) -> IResult<'c,&'b str,T> {
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

impl<'a,'b,T> Mapper<(),&'a str, T> for IResult<'b,(),&'a str> {
  fn map_opt<F:Fn(&'a str) -> Option<T>>(&self, f: F) -> IResult<'b,(),T> {
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

  fn map_res<U, F: Fn(&'a str) -> Result<T,U>>(&self, f: F) -> IResult<'b,(),T> {
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

impl<'a,'b,R,T> Mapper<&'a[R], (), T> for IResult<'b,&'a[R],()> {
  fn map_opt<F:Fn(()) -> Option<T>>(&self, f: F) -> IResult<'b,&'a[R],T> {
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

  fn map_res<U, F: Fn(()) -> Result<T,U>>(&self, f: F) -> IResult<'b,&'a [R],T> {
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

impl<'a,'z,T> Mapper<&'a str, (), T> for IResult<'z,&'a str,()> {
  fn map_opt<F:Fn(()) -> Option<T>>(&self, f: F) -> IResult<'z,&'a str,T> {
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

  fn map_res<U, F: Fn(()) -> Result<T,U>>(&self, f: F) -> IResult<'z,&'a str,T> {
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

impl<'z,T> Mapper<(),(), T> for IResult<'z,(),()> {
  fn map_opt<F:Fn(()) -> Option<T>>(&self, f: F) -> IResult<'z,(),T> {
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

  fn map_res<U, F: Fn(()) -> Result<T,U>>(&self, f: F) -> IResult<'z,(),T> {
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
  fn map<'z,F: Fn(O) -> N>(& self, f: F) -> IResult<'z,I,N>;
}

impl<'a,'z,R,S,T> Mapper2<&'a R, &'a[S], T> for IResult<'z,&'a R,&'a [S]> {
  fn map<F: Fn(&'a[S]) -> T>(&self, f: F) -> IResult<'z,&'a R,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,'z,R,S,T> Mapper2<&'a [R], &'a[S], T> for IResult<'z,&'a [R],&'a [S]> {
  fn map<F: Fn(&'a[S]) -> T>(&self, f: F) -> IResult<'z,&'a [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,'z,S,T> Mapper2<&'a str, &'a[S], T> for IResult<'z,&'a str,&'a [S]> {
  fn map<F: Fn(&'a[S]) -> T>(&self, f: F) -> IResult<'z,&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,'z,S,T> Mapper2<(), &'a[S], T> for IResult<'z,(),&'a [S]> {
  fn map<F: Fn(&'a[S]) -> T>(&self, f: F) -> IResult<'z,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => Done((),f(*o))
    }
  }
}

impl<'a,'z,R,T> Mapper2<&'a R, (), T> for IResult<'z,&'a R,()> {
  fn map<F: Fn(()) -> T>(&self, f: F) -> IResult<'z,&'a R,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,'z,R,T> Mapper2<&'a [R], (), T> for IResult<'z,&'a [R],()> {
  fn map<F: Fn(()) -> T>(&self, f: F) -> IResult<'z,&'a [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,'z,T> Mapper2<&'a str, (), T> for IResult<'z,&'a str,()> {
  fn map<F: Fn(()) -> T>(&self, f: F) -> IResult<'z,&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,'z,T> Mapper2<(), (), T> for IResult<'z,(),()> {
  fn map<F: Fn(()) -> T>(&self, f: F) -> IResult<'z,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,'b,'z,R,T> Mapper2<&'b R, &'a str, T> for IResult<'z,&'b R,&'a str> {
  fn map<F: Fn(&'a str) -> T>(&self, f: F) -> IResult<'z,&'b R,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,'b,'z,R,T> Mapper2<&'b [R], &'a str, T> for IResult<'z,&'b [R],&'a str> {
  fn map<F: Fn(&'a str) -> T>(&self, f: F) -> IResult<'z,&'b [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}
impl<'a,'b,'z,T> Mapper2<&'b str, &'a str, T> for IResult<'z,&'b str,&'a str> {
  fn map<F: Fn(&'a str) -> T>(&self, f: F) -> IResult<'z,&'b str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => Done(*i,f(*o))
    }
  }
}

impl<'a,'z,T> Mapper2<(), &'a str, T> for IResult<'z,(),&'a str> {
  fn map<F:  Fn(&'a str) -> T>(&self, f: F) -> IResult<'z,(),T> {
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
  use std::fmt::Debug;

  fn local_print<'a,T: Debug>(input: T) -> IResult<'a,T, ()> {
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
