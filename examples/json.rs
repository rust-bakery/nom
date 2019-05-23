#![cfg(feature = "alloc")]

#[macro_use]
extern crate nom;
extern crate jemallocator;

#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use nom::{
  branch::alt,
  bytes::complete::{escaped, tag, take_while},
  character::complete::{alphanumeric1 as alphanumeric, char, one_of},
  combinator::{complete, map, not, cut},
  error::{context, ErrorKind, ParseError},
  error::{VerboseError, VerboseErrorKind},
  multi::separated_list,
  number::complete::double,
  sequence::{delimited, preceded, separated_pair, terminated},
  Err, IResult, Offset,
};
use std::collections::HashMap;
use std::iter::repeat;
use std::str;

#[derive(Debug, PartialEq)]
pub enum JsonValue {
  Str(String),
  Boolean(bool),
  Num(f64),
  Array(Vec<JsonValue>),
  Object(HashMap<String, JsonValue>),
}

fn sp<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
  let chars = " \t\r\n";

  take_while(move |c| chars.contains(c))(i)
}

fn parse_str<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
  escaped(alphanumeric, '\\', one_of("\"n\\"))(i)
}

fn string<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
  let (i, _) = char('\"')(i)?;

  context("string", cut(terminated(parse_str, char('\"'))))(i)
}

fn boolean<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, bool, E> {
  alt((
      map(tag("false"), |_| false),
      map(tag("true"), |_| true)
  ))(input)
}

fn array<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Vec<JsonValue>, E> {
  let (i, _) = char('[')(i)?;

  context(
    "array",
    cut(terminated(
      separated_list(preceded(sp, char(',')), value),
      preceded(sp, char(']'))))
  )(i)
}

fn key_value<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, (&'a str, JsonValue), E> {
  separated_pair(preceded(sp, string), preceded(sp, char(':')), value)(i)
}

fn hash<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, HashMap<String, JsonValue>, E> {
  let (i, _) = char('{')(i)?;
  context(
    "map",
    cut(terminated(
      map(
        separated_list(preceded(sp, char(',')), key_value),
        |tuple_vec| {
          tuple_vec.into_iter().map(|(k, v)| (String::from(k), v)).collect()
      }),
      preceded(sp, char('}')),
    ))
  )(i)
}

fn value<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, JsonValue, E> {
  preceded(
    sp,
    alt((
      map(hash, JsonValue::Object),
      map(array, JsonValue::Array),
      map(string, |s| JsonValue::Str(String::from(s))),
      map(double, JsonValue::Num),
      map(boolean, JsonValue::Boolean),
    )),
  )(i)
}

fn root<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, JsonValue, E> {
  delimited(
    sp,
    alt((map(hash, JsonValue::Object), map(array, JsonValue::Array))),
    not(complete(sp)),
  )(i)
}

fn convert_error(input: &str, e: VerboseError<&str>) -> String {
  let lines: Vec<_> = input.lines().map(String::from).collect();
  //println!("lines: {:#?}", lines);

  let mut result = String::new();

  for (i, (substring, kind)) in e.errors.iter().enumerate() {
    let mut offset = input.offset(substring);

    let mut line = 0;
    let mut column = 0;

    for (j, l) in lines.iter().enumerate() {
      if offset <= l.len() {
        line = j;
        column = offset;
        break;
      } else {
        offset = offset - l.len();
      }
    }

    match kind {
      VerboseErrorKind::Char(c) => {
        result += &format!("{}: at line {}:\n", i, line);
        result += &lines[line];
        result += "\n";
        if column > 0 {
          result += &repeat(' ').take(column - 1).collect::<String>();
        }
        result += "^\n";
        result += &format!("expected '{}', found {}\n\n", c, substring.chars().next().unwrap());
      }
      VerboseErrorKind::Context(s) => {
        result += &format!("{}: at line {}, in {}:\n", i, line, s);
        result += &lines[line];
        result += "\n";
        if column > 0 {
          result += &repeat(' ').take(column - 1).collect::<String>();
        }
        result += "^\n\n";
      }
      _ => {}
    }
  }

  result
}

fn main() {
  let data = "  { \"a\"\t: 42,
  \"b\": [ \"x\", \"y\", 12 ] ,
  \"c\": { 1\"hello\" : \"world\"
  }
  } ";

  println!("will try to parse:\n\n**********\n{}\n**********\n", data);
  println!(
    "basic errors - `root::<(&str, ErrorKind)>(data)`:\n{:#?}\n",
    root::<(&str, ErrorKind)>(data)
  );
  println!("parsed verbose: {:#?}", root::<VerboseError<&str>>(data));

  match root::<VerboseError<&str>>(data) {
    Err(Err::Error(e)) | Err(Err::Failure(e)) => {
      println!("verbose errors - `root::<VerboseError>(data)`:\n{}", convert_error(data, e));
    }
    _ => panic!(),
  }
}
