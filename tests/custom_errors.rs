#![allow(dead_code)]
#![cfg_attr(feature = "cargo-clippy", allow(block_in_if_condition_stmt))]

#[macro_use]
extern crate nom;

use nom::IResult;
use nom::digit;

use std::convert::From;

pub struct CustomError(String);
impl From<u32> for CustomError {
  fn from(error: u32) -> Self {
    CustomError(format!("error code was: {}", error))
  }
}

fn test1(input: &str) -> IResult<&str, &str, CustomError> {
  fix_error!(input, CustomError, tag!("abcd"))
}

fn test2(input: &str) -> IResult<&str, &str, CustomError> {
  terminated!(input, test1, fix_error!(CustomError, digit))
}

fn test3(input: &str) -> IResult<&str, &str, CustomError> {
  verify!(input, test1, |s: &str| {
    s.starts_with("abcd")
  })
}

#[cfg(feature = "alloc")]
fn test4(input: &str) -> IResult<&str, Vec<&str>, CustomError> {
  count!(input, test1, 4)
}
