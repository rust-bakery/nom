#![no_main]
use libfuzzer_sys::fuzz_target;
use std::str;

extern crate nom;

use nom::{
  branch::alt,
  bytes::complete::tag,
  character::complete::char,
  character::complete::{digit1 as digit, space0 as space},
  combinator::{map, map_res, verify},
  multi::fold_many0,
  sequence::{delimited, pair, terminated},
  IResult, Parser
};

use std::cell::RefCell;
use std::str::FromStr;

thread_local! {
    pub static LEVEL: RefCell<u32> = RefCell::new(0);
}

fn reset() {
  LEVEL.with(|l| {
    *l.borrow_mut() = 0;
  });
}

fn incr(i: &str) -> IResult<&str, ()> {
  LEVEL.with(|l| {
    *l.borrow_mut() += 1;

    // limit the number of recursions, the fuzzer keeps running into them
    if *l.borrow() >= 8192 {
      return Err(nom::Err::Failure(nom::error::Error::new(
        i,
        nom::error::ErrorKind::Count,
      )));
    } else {
      Ok((i, ()))
    }
  })
}

fn decr() {
  LEVEL.with(|l| {
    *l.borrow_mut() -= 1;
  });
}

fn parens(i: &str) -> IResult<&str, i64> {
  delimited(
    space,
    delimited(terminated(tag("("), incr), expr, map(tag(")"), |_| decr())),
    space,
  ).parse(i)
}

fn factor(i: &str) -> IResult<&str, i64> {
  alt((
    map_res(delimited(space, digit, space), FromStr::from_str),
    parens,
  )).parse(i)
}

fn term(i: &str) -> IResult<&str, i64> {
  incr(i)?;
  let (i, init) = factor(i).map_err(|e| {
    decr();
    e
  })?;

  let res = fold_many0(
    alt((
      pair(char('*'), factor),
      pair(char('/'), verify(factor, |i| *i != 0)),
    )),
    || init,
    |acc, (op, val): (char, i64)| {
      if op == '*' {
        acc.saturating_mul(val)
      } else {
        match acc.checked_div(val) {
          Some(v) => v,
          // we get a division with overflow because we can get acc = i64::MIN and val = -1
          // the division by zero is already checked earlier by verify
          None => i64::MAX,
        }
      }
    },
  ).parse(i);

  decr();
  res
}

fn expr(i: &str) -> IResult<&str, i64> {
  incr(i)?;
  let (i, init) = term(i).map_err(|e| {
    decr();
    e
  })?;

  let res = fold_many0(
    pair(alt((char('+'), char('-'))), term),
    || init,
    |acc, (op, val): (char, i64)| {
      if op == '+' {
        acc.saturating_add(val)
      } else {
        acc.saturating_sub(val)
      }
    },
  ).parse(i);

  decr();
  res
}

fuzz_target!(|data: &[u8]| {
  reset();
  // fuzzed code goes here
  let _ = match str::from_utf8(data) {
    Ok(v) => {
      //println!("v: {}", v);
      factor(v)
    }
    Err(_) => factor("2"),
  };
});
