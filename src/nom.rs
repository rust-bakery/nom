#![desc = "Omnomnom incremental byte parser"]
#![license = "MIT"]

extern crate collections;

use std::fmt::Show;

type Err = uint;
pub enum Parser<'a,I,O> {
  Done(I,O),
  Error(I, Err),
  //Incomplete(|I|:'a -> Parser<I,O>)
  Incomplete(fn(I) -> Parser<'a,I,O>)
}

/*
pub fn parse<'a,I,O>(input: I) -> Option<O> {

}
*/
/*pub fn parseString(input: String) -> Option<int> {
  parse(vec![0]) match {
    
  }
}*/

pub fn feed() -> () {
  let v = vec![1, 2, 3, 4, 5];
  let mut acc = v.slice(0, 1);
  let mut idx = 0;
  let mut parser = Incomplete(parse);
  loop {
    match parser {
      Error(i, e) => {
        println!("error: {} input: {}", e, i);
        break;
      },
      Done(i, o)  => {
        println!("done: {}, rest: {}", o, i);
        break;
      },
      Incomplete(f) => {
        idx = idx + 1;
        println!("incomplete");
        parser = f(v.slice(0, idx));
      }
    }
  }
}

pub fn parse<'a>(input: &'a [u8]) -> Parser<'a, &'a [u8], &'a [u8]> {

  match input.len() {
    0 => Error(input, 0),
    1 => Incomplete(parse),
    _ => Done(input.slice_from(2), input.slice(0,2))
  }
}

pub fn print<'a, T: Show>(input: &'a T) -> Parser<'a, (), ()> {
  println!("{}", input);
  Done((), ())
}
