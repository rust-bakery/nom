//! Basic combination functions
//!
//! Provides the flat_map, map, map_opt and map_res methods used elsewhere.
//!
//! Traits provided here must be implemented for any new combination of I and O types in IResult<I,O>

use internal::*;
use internal::IResult::*;

/// flat_map is a method of IResult<R,S>, takes a function Fn(S) -> IResult<S,T>,
/// and returns a IResult<S,T>
///
/// ```
/// use nom::IResult::Done;
/// use nom::FlatMapper;
/// use std::str;
/// Done((),()).flat_map(|data| { println!("data: {:?}", data); Done(data,())});
/// ```
pub trait FlatMapper<I:?Sized,O:?Sized,N:?Sized> {
  fn flat_map<'y,F:Fn(O) -> IResult<'y,O,N>>(& self, f: F) -> IResult<'y,I,N>;
}
/*
pub fn compose<'x,'y,'z,R,S,T,F:Fn(S) -> IResult<'y,S,T>>(f:F, g:IResultClosure<'z,R,S>) -> IResultClosure<'x,R,T> {
  Box::new(move |input: R| -> IResult<'x,R,T> {
    g(input).flat_map(f)
  })
}
*/
/// derives flat_map implementation for a list of IResult types with referenced types
/// like str or vectors
///
/// ```
/// //flat_map_ref_impl! { [bool] [uint] };
/// ```
#[macro_export]
macro_rules! flat_map_ref_impl {
  ($($t:ty)*) => ($(
      impl<'a,'b,'z,R,T> FlatMapper<&'b R,&'a $t, T> for IResult<'z,&'b R,&'a $t> {
        #[allow(unused_variables)]
        fn flat_map<'y,F:Fn(&'a $t) -> IResult<'y,&'a $t,T>>(&self, f: F) -> IResult<'y,&'b R,T> {
          match self {
            &Error(ref e) => Error(*e),
            &Incomplete(ref cl) => Error(42),//Incomplete(|input:&'b R| { cl(input).map(f) }),
            &Done(ref i, ref o) => match f(*o) {
              Error(ref e) => Error(*e),
              Incomplete(ref i2) => Error(42),
              Done(_, o2) => Done(*i, o2)
            }
          }
        }
      }
      impl<'a,'z,T> FlatMapper<(),&'a $t, T> for IResult<'z,(),&'a $t> {
        #[allow(unused_variables)]
        fn flat_map<'y,F:Fn(&'a $t) -> IResult<'y,&'a $t,T>>(&self, f: F) -> IResult<'y,(),T> {
          match self {
            &Error(ref e) => Error(*e),
            &Incomplete(ref cl) => Error(42), //Incomplete(|input:I| { cl(input).map(f) })
            &Done((), ref o) => match f(*o) {
              Error(ref e) => Error(*e),
              Incomplete(ref i2) => Error(42),
              Done(_, o2) => Done((), o2)
            }
          }
        }
      }
  )*)
}

flat_map_ref_impl! {
  str [bool] [char] [usize] [u8] [u16] [u32] [u64] [isize] [i8] [i16] [i32] [i64] [f32] [f64]
}


/// derives flat_map implementation for a list of specific IResult types
///
/// ```
/// //flat_map_impl! { bool uint };
/// ```
#[macro_export]
macro_rules! flat_map_impl {
  ($($t:ty)*) => ($(
      impl<'a,'z,R,T> FlatMapper<&'a R,$t, T> for IResult<'z,&'a R,$t> {
        #[allow(unused_variables)]
        fn flat_map<'y,F:Fn($t) -> IResult<'y,$t,T>>(&self, f: F) -> IResult<'y,&'a R,T> {
          match self {
            &Error(ref e) => Error(*e),
            &Incomplete(ref i) => Error(42),//Incomplete(*i),
            &Done(ref i, o) => match f(o) {
              Error(ref e) => Error(*e),
              Incomplete(ref i2) => Error(42),
              Done(i2, o2) => Done(*i, o2)
            }
          }
        }
      }
      impl<'z,T> FlatMapper<(),$t, T> for IResult<'z,(),$t> {
        #[allow(unused_variables)]
        fn flat_map<'y,F:Fn($t) -> IResult<'y,$t,T>>(&self, f: F) -> IResult<'y,(),T> {
          match self {
            &Error(ref e) => Error(*e),
            &Incomplete(ref i) => Error(42),//Incomplete(*i),
            &Done((), o) => match f(o) {
              Error(ref e) => Error(*e),
              Incomplete(ref i2) => Error(42),
              Done(i2, o2) => Done((), o2)
            }
          }
        }
      }
  )*)
}

flat_map_impl! {
  bool char usize u8 u16 u32 u64 isize i8 i16 i32 i64 f32 f64
}


impl<'a,'z,R,T> FlatMapper<&'a R,(), T> for IResult<'z,&'a R,()> {
  #[allow(unused_variables)]
  fn flat_map<'y,F: Fn(()) -> IResult<'y,(),T>>(&self, f: F) -> IResult<'y,&'a R,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      //&Incomplete(ref cl) => Incomplete(Box::new(move |input| { cl(input).flat_map(f) })),
      &Done(ref i, ()) => match f(()) {
        Error(ref e) => Error(*e),
        Incomplete(ref i2) => Error(42),
        Done(_, o2) => Done(*i, o2)
      }
    }
  }
}

impl<'a,'x,'z,S,T> FlatMapper<(),&'a S,T> for IResult<'z,(),&'a S> {
  #[allow(unused_variables)]
  fn flat_map<'y,F:Fn(&'a S) -> IResult<'y,&'a S,T>>(&self, f: F) -> IResult<'y,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done((), ref o) => match f(*o) {
        Error(ref e) => Error(*e),
        Incomplete(ref i2) => Error(42),
        Done(_, o2) => Done((), o2)
      }
    }
  }
}

impl<'x,'z,T> FlatMapper<(),(),T> for IResult<'z,(),()> {
  #[allow(unused_variables)]
  fn flat_map<'y,F:Fn(()) -> IResult<'y,(),T>>(&self, f: F) -> IResult<'y,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Incomplete(f), //Incomplete(|input:I| { cl(input).map(f) })
      &Done((), ()) => match f(()) {
        Error(ref e) => Error(*e),
        Incomplete(ref i2) => Error(42),
        Done(_, o2) => Done((), o2)
      }
    }
  }
}

/// map_opt and map_res are used to combine common functions with parsers
///
/// ```
/// use nom::IResult::Done;
/// use nom::Mapper;
/// use std::str;
/// let res = Done((),"abcd".as_bytes()).map_res(|&: data| { str::from_utf8(data) });
/// assert_eq!(res, Done((), "abcd"));
/// ```
pub trait Mapper<I,O,N> {
  fn map_opt<'y,F: Fn(O) -> Option<N>>(& self, f: F) -> IResult<'y,I,N>;
  fn map_res<'y,P,F: Fn(O) -> Result<N,P>>(& self, f: F) -> IResult<'y,I,N>;
}

/// derives map_opt and map_res implementations for a list of IResult types with referenced types
/// like str or vectors
#[macro_export]
macro_rules! map_ref_impl {
  ($i:ty, $o:ty) => (
      impl<'a,'b,'z,T> Mapper<&'b $i,&'a $o, T> for IResult<'z,&'b $i,&'a $o> {
        fn map_opt<'y,F:Fn(&'a $o) -> Option<T>>(&self, f: F) -> IResult<'y,&'b $i,T> {
          match self {
            &Error(ref e) => Error(*e),
            &Incomplete(ref i) => Error(42),//Incomplete(*i),
            //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
            &Done(ref i, ref o) => match f(*o) {
              Some(output) => Done(*i, output),
              None         => Error(0)
            }
          }
        }

        fn map_res<'y,U, F: Fn(&'a $o) -> Result<T,U>>(&self, f: F) -> IResult<'y,&'b $i,T> {
          match self {
            &Error(ref e) => Error(*e),
            &Incomplete(ref i) => Error(42),//Incomplete(*i),
            //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
            &Done(ref i, ref o) => match f(*o) {
              Ok(output) => Done(*i, output),
              Err(_)     => Error(0)
            }
          }
        }
      }
  )
}

map_ref_impl!([u8], [u8]);
map_ref_impl!([u8], str);
map_ref_impl!(str,  [u8]);
map_ref_impl!(str,  str);

impl<'a,'z,S,T> Mapper<(), &'a[S], T> for IResult<'z,(),&'a [S]> {
  fn map_opt<'y,F:Fn(&'a[S]) -> Option<T>>(&self, f: F) -> IResult<'y,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => match f(*o) {
        Some(output) => Done((), output),
        None         => Error(0)
      }
    }
  }

  fn map_res<'y,U, F: Fn(&'a[S]) -> Result<T,U>>(&self, f: F) -> IResult<'y,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => match f(*o) {
        Ok(output) => Done((), output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'a,'z,T> Mapper<(),&'a str, T> for IResult<'z,(),&'a str> {
  fn map_opt<'y,F:Fn(&'a str) -> Option<T>>(&self, f: F) -> IResult<'y,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => match f(*o) {
        Some(output) => Done((), output),
        None         => Error(0)
      }
    }
  }

  fn map_res<'y,U, F: Fn(&'a str) -> Result<T,U>>(&self, f: F) -> IResult<'y,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => match f(*o) {
        Ok(output) => Done((), output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'a,'z,R,T> Mapper<&'a[R], (), T> for IResult<'z,&'a[R],()> {
  fn map_opt<'y,F:Fn(()) -> Option<T>>(&self, f: F) -> IResult<'y,&'a[R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, __) => match f(()) {
        Some(output) => Done(*i, output),
        None         => Error(0)
      }
    }
  }

  fn map_res<'y,U, F: Fn(()) -> Result<T,U>>(&self, f: F) -> IResult<'y,&'a [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Ok(output) => Done(*i, output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'a,'z,T> Mapper<&'a str, (), T> for IResult<'z,&'a str,()> {
  fn map_opt<'y,F:Fn(()) -> Option<T>>(&self, f: F) -> IResult<'y,&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, __) => match f(()) {
        Some(output) => Done(*i, output),
        None         => Error(0)
      }
    }
  }

  fn map_res<'y,U, F: Fn(()) -> Result<T,U>>(&self, f: F) -> IResult<'y,&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),// Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ref o) => match f(*o) {
        Ok(output) => Done(*i, output),
        Err(_)     => Error(0)
      }
    }
  }
}

impl<'z,T> Mapper<(),(), T> for IResult<'z,(),()> {
  fn map_opt<'y,F:Fn(()) -> Option<T>>(&self, f: F) -> IResult<'y,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), __) => match f(()) {
        Some(output) => Done((), output),
        None         => Error(0)
      }
    }
  }

  fn map_res<'y,U, F: Fn(()) -> Result<T,U>>(&self, f: F) -> IResult<'y,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => match f(*o) {
        Ok(output) => Done(*o, output),
        Err(_)     => Error(0)
      }
    }
  }
}

/// map applies a parser function directly to the output of another parser function
///
///```
/// use nom::IResult::Done;
/// use nom::Mapper2;
/// use std::str;
/// let res = Done((),"abcd".as_bytes()).map(|data| { str::from_utf8(data).unwrap() });
/// assert_eq!(res, Done((), "abcd"));
///```
pub trait Mapper2<I,O,N> {
  fn map<'y,F: Fn(O) -> N>(& self, f: F) -> IResult<'y,I,N>;
}

#[macro_export]
macro_rules! map2_ref_impl {
  ($i:ty, $o:ty) => (
      impl<'a,'b,'z,T> Mapper2<&'b $i,&'a $o, T> for IResult<'z,&'b $i,&'a $o> {
        fn map<'y,F: Fn(&'a $o) -> T>(&self, f: F) -> IResult<'y,&'b $i,T> {
          match self {
            &Error(ref e) => Error(*e),
            &Incomplete(ref i) => Error(42),//Incomplete(*i),
            //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
            &Done(ref i, ref o) => Done(*i,f(*o))
          }
        }
      }
  )
}

map2_ref_impl!([u8], [u8]);
map2_ref_impl!([u8], str);
map2_ref_impl!(str,  [u8]);
map2_ref_impl!(str,  str);

impl<'a,'z,S,T> Mapper2<(), &'a[S], T> for IResult<'z,(),&'a [S]> {
  fn map<'y,F: Fn(&'a[S]) -> T>(&self, f: F) -> IResult<'y,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done((), ref o) => Done((),f(*o))
    }
  }
}

impl<'a,'z,R,T> Mapper2<&'a R, (), T> for IResult<'z,&'a R,()> {
  fn map<'y,F: Fn(()) -> T>(&self, f: F) -> IResult<'y,&'a R,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,'z,R,T> Mapper2<&'a [R], (), T> for IResult<'z,&'a [R],()> {
  fn map<'y,F: Fn(()) -> T>(&self, f: F) -> IResult<'y,&'a [R],T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,'z,T> Mapper2<&'a str, (), T> for IResult<'z,&'a str,()> {
  fn map<'y,F: Fn(()) -> T>(&self, f: F) -> IResult<'y,&'a str,T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,'z,T> Mapper2<(), (), T> for IResult<'z,(),()> {
  fn map<'y,F: Fn(()) -> T>(&self, f: F) -> IResult<'y,(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
      //&Incomplete(ref cl) => Error(0),//Incomplete(|input: &'a I| {*cl(input).mapf(f)}),
      &Done(ref i, ()) => Done(*i,f(()))
    }
  }
}

impl<'a,'z,T> Mapper2<(), &'a str, T> for IResult<'z,(),&'a str> {
  fn map<'y,F: Fn(&'a str) -> T>(&self, f: F) -> IResult<'y,(),T> {
  //fn map<F: Fn(&'a str) -> T>(&self, f: F) -> IResult<(),T> {
    match self {
      &Error(ref e) => Error(*e),
      &Incomplete(ref i) => Error(42),//Incomplete(*i),
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

  fn local_print<'a,T: Debug>(input: T) -> IResult<'a,T,()> {
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
    let d = Done(&v1[], &v2[]);
    let res = local_print(&v2[]);
    assert_eq!(res, Done(&v2[], ()));
  }
}
