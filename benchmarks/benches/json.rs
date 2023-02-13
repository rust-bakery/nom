#[macro_use]
extern crate criterion;

#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use criterion::Criterion;
use nom::{
  branch::alt,
  bytes::complete::{tag, take},
  character::complete::{anychar, char, multispace0, none_of},
  combinator::{map, map_opt, map_res, value, verify},
  error::{Error, ErrorKind, FromExternalError, ParseError, VerboseError},
  multi::{fold, separated_list0},
  number::complete::{double, recognize_float},
  sequence::{delimited, preceded, separated_pair},
  IResult, Parser,
};

use std::{collections::HashMap, num::ParseIntError};

#[derive(Debug, PartialEq, Clone)]
pub enum JsonValue {
  Null,
  Bool(bool),
  Str(String),
  Num(f64),
  Array(Vec<JsonValue>),
  Object(HashMap<String, JsonValue>),
}

fn boolean<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, bool, E> {
  alt((value(false, tag("false")), value(true, tag("true"))))(input)
}

fn u16_hex<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, u16, E> {
  map_res(take(4usize), |s| u16::from_str_radix(s, 16))(input)
}

fn unicode_escape<'a, E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError>>(
  input: &'a str,
) -> IResult<&str, char, E> {
  map_opt(
    alt((
      // Not a surrogate
      map(verify(u16_hex, |cp| !(0xD800..0xE000).contains(cp)), |cp| {
        cp as u32
      }),
      // See https://en.wikipedia.org/wiki/UTF-16#Code_points_from_U+010000_to_U+10FFFF for details
      map(
        verify(
          separated_pair(u16_hex, tag("\\u"), u16_hex),
          |(high, low)| (0xD800..0xDC00).contains(high) && (0xDC00..0xE000).contains(low),
        ),
        |(high, low)| {
          let high_ten = (high as u32) - 0xD800;
          let low_ten = (low as u32) - 0xDC00;
          (high_ten << 10) + low_ten + 0x10000
        },
      ),
    )),
    // Could probably be replaced with .unwrap() or _unchecked due to the verify checks
    std::char::from_u32,
  )(input)
}

fn character<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError> + FromExternalError<&'a str, ()>,
>(
  input: &'a str,
) -> IResult<&str, char, E> {
  let (input, c) = none_of("\"")(input)?;
  if c == '\\' {
    alt((
      map_res(anychar, |c| {
        Ok(match c {
          '"' | '\\' | '/' => c,
          'b' => '\x08',
          'f' => '\x0C',
          'n' => '\n',
          'r' => '\r',
          't' => '\t',
          _ => return Err(()),
        })
      }),
      preceded(char('u'), unicode_escape),
    ))(input)
  } else {
    Ok((input, c))
  }
}

fn string<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError> + FromExternalError<&'a str, ()>,
>(
  input: &'a str,
) -> IResult<&str, String, E> {
  delimited(
    char('"'),
    fold(0.., character, String::new, |mut string, c| {
      string.push(c);
      string
    }),
    char('"'),
  )(input)
}

fn ws<
  'a,
  O,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError> + FromExternalError<&'a str, ()>,
  F: Parser<&'a str, Output = O, Error = E>,
>(
  f: F,
) -> impl Parser<&'a str, Output = O, Error = E> {
  delimited(multispace0, f, multispace0)
}

fn array<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError> + FromExternalError<&'a str, ()>,
>(
  input: &'a str,
) -> IResult<&str, Vec<JsonValue>, E> {
  delimited(
    char('['),
    ws(separated_list0(ws(char(',')), json_value)),
    char(']'),
  )(input)
}

fn object<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError> + FromExternalError<&'a str, ()>,
>(
  input: &'a str,
) -> IResult<&str, HashMap<String, JsonValue>, E> {
  map(
    delimited(
      char('{'),
      ws(separated_list0(
        ws(char(',')),
        separated_pair(string, ws(char(':')), json_value),
      )),
      char('}'),
    ),
    |key_values| key_values.into_iter().collect(),
  )(input)
}

fn json_value<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError> + FromExternalError<&'a str, ()>,
>(
  input: &'a str,
) -> IResult<&str, JsonValue, E> {
  use JsonValue::*;

  alt((
    value(Null, tag("null")),
    map(boolean, Bool),
    map(string, Str),
    map(double, Num),
    map(array, Array),
    map(object, Object),
  ))(input)
}

fn json<
  'a,
  E: ParseError<&'a str> + FromExternalError<&'a str, ParseIntError> + FromExternalError<&'a str, ()>,
>(
  input: &'a str,
) -> IResult<&'a str, JsonValue, E> {
  ws(json_value).parse(input)
}

fn json_bench(c: &mut Criterion) {
  let data = "  { \"a\"\t: 42,
  \"b\": [ \"x\", \"y\", 12 ,\"\\u2014\", \"\\uD83D\\uDE10\"] ,
  \"c\": { \"hello\" : \"world\"
  }
  }  ";

  // test once to make sure it parses correctly
  json::<Error<&str>>(data).unwrap();

  // println!("data:\n{:?}", json(data));
  c.bench_function("json", |b| {
    b.iter(|| json::<Error<&str>>(data).unwrap());
  });
}

static CANADA: &str = include_str!("../canada.json");
fn canada_json(c: &mut Criterion) {
  // test once to make sure it parses correctly
  json::<Error<&str>>(CANADA).unwrap();

  // println!("data:\n{:?}", json(data));
  c.bench_function("json canada", |b| {
    b.iter(|| json::<Error<&str>>(CANADA).unwrap());
  });
}

fn verbose_json(c: &mut Criterion) {
  let data = "  { \"a\"\t: 42,
  \"b\": [ \"x\", \"y\", 12 ,\"\\u2014\", \"\\uD83D\\uDE10\"] ,
  \"c\": { \"hello\" : \"world\"
  }
  }  ";

  // test once to make sure it parses correctly
  json::<VerboseError<&str>>(data).unwrap();

  // println!("data:\n{:?}", json(data));
  c.bench_function("json vebose", |b| {
    b.iter(|| json::<VerboseError<&str>>(data).unwrap());
  });
}

fn verbose_canada_json(c: &mut Criterion) {
  // test once to make sure it parses correctly
  json::<VerboseError<&str>>(CANADA).unwrap();

  // println!("data:\n{:?}", json(data));
  c.bench_function("json canada verbose", |b| {
    b.iter(|| json::<VerboseError<&str>>(CANADA).unwrap());
  });
}

fn recognize_float_bytes(c: &mut Criterion) {
  println!(
    "recognize_float_bytes result: {:?}",
    recognize_float::<_, (_, ErrorKind)>(&b"-1.234E-12"[..])
  );
  c.bench_function("recognize float bytes", |b| {
    b.iter(|| recognize_float::<_, (_, ErrorKind)>(&b"-1.234E-12"[..]));
  });
}

fn recognize_float_str(c: &mut Criterion) {
  println!(
    "recognize_float_str result: {:?}",
    recognize_float::<_, (_, ErrorKind)>("-1.234E-12")
  );
  c.bench_function("recognize float str", |b| {
    b.iter(|| recognize_float::<_, (_, ErrorKind)>("-1.234E-12"));
  });
}

fn float_bytes(c: &mut Criterion) {
  println!(
    "float_bytes result: {:?}",
    double::<_, (_, ErrorKind)>(&b"-1.234E-12"[..])
  );
  c.bench_function("float bytes", |b| {
    b.iter(|| double::<_, (_, ErrorKind)>(&b"-1.234E-12"[..]));
  });
}

fn float_str(c: &mut Criterion) {
  println!(
    "float_str result: {:?}",
    double::<_, (_, ErrorKind)>("-1.234E-12")
  );
  c.bench_function("float str", |b| {
    b.iter(|| double::<_, (_, ErrorKind)>("-1.234E-12"));
  });
}

use nom::Err;
use nom::ParseTo;
fn std_float(input: &[u8]) -> IResult<&[u8], f64, (&[u8], ErrorKind)> {
  match recognize_float(input) {
    Err(e) => Err(e),
    Ok((i, s)) => match s.parse_to() {
      Some(n) => Ok((i, n)),
      None => Err(Err::Error((i, ErrorKind::Float))),
    },
  }
}

fn std_float_bytes(c: &mut Criterion) {
  println!(
    "std_float_bytes result: {:?}",
    std_float(&b"-1.234E-12"[..])
  );
  c.bench_function("std_float bytes", |b| {
    b.iter(|| std_float(&b"-1.234E-12"[..]));
  });
}

criterion_group!(
  benches,
  json_bench,
  verbose_json,
  canada_json,
  verbose_canada_json,
  recognize_float_bytes,
  recognize_float_str,
  float_bytes,
  std_float_bytes,
  float_str
);
criterion_main!(benches);
