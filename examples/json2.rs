//#[global_allocator]
//static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use nom::{
  branch::alt,
  bytes::{tag, take},
  character::{anychar, char, multispace0, none_of},
  combinator::{map, map_opt, map_res, value, verify},
  error::{Error, ParseError},
  multi::{fold, separated_list0},
  number::double,
  sequence::{delimited, preceded, separated_pair},
  Complete, Emit, Mode, OutputM, Parser,
};

use std::collections::HashMap;

#[derive(Debug, PartialEq, Clone)]
pub enum JsonValue {
  Null,
  Bool(bool),
  Str(String),
  Num(f64),
  Array(Vec<JsonValue>),
  Object(HashMap<String, JsonValue>),
}

fn boolean<'a>() -> impl Parser<&'a str, Output = bool, Error = Error<&'a str>> {
  alt((value(false, tag("false")), value(true, tag("true"))))
}

fn u16_hex<'a>() -> impl Parser<&'a str, Output = u16, Error = Error<&'a str>> {
  map_res(take(4usize), |s| u16::from_str_radix(s, 16))
}

fn unicode_escape<'a>() -> impl Parser<&'a str, Output = char, Error = Error<&'a str>> {
  map_opt(
    alt((
      // Not a surrogate
      map(
        verify(u16_hex(), |cp| !(0xD800..0xE000).contains(cp)),
        |cp| cp as u32,
      ),
      // See https://en.wikipedia.org/wiki/UTF-16#Code_points_from_U+010000_to_U+10FFFF for details
      map(
        verify(
          separated_pair(u16_hex(), tag("\\u"), u16_hex()),
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
  )
}

fn character<'a>() -> impl Parser<&'a str, Output = char, Error = Error<&'a str>> {
  Character
  /*let (input, c) = none_of("\"")(input)?;
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
      preceded(char('u'), unicode_escape()),
    ))
    .parse(input)
  } else {
    Ok((input, c))
  }*/
}

struct Character;

impl<'a> Parser<&'a str> for Character {
  type Output = char;

  type Error = Error<&'a str>;

  fn process<OM: nom::OutputMode>(
    &mut self,
    input: &'a str,
  ) -> nom::PResult<OM, &'a str, Self::Output, Self::Error> {
    let (input, c): (&str, char) =
      none_of("\"").process::<OutputM<Emit, OM::Error, OM::Incomplete>>(input)?;
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
        preceded(char('u'), unicode_escape()),
      ))
      .process::<OM>(input)
    } else {
      Ok((input, OM::Output::bind(|| c)))
    }
  }
}

fn string<'a>() -> impl Parser<&'a str, Output = String, Error = Error<&'a str>> {
  delimited(
    char('"'),
    fold(0.., character(), String::new, |mut string, c| {
      string.push(c);
      string
    }),
    char('"'),
  )
}

fn ws<'a, O, E: ParseError<&'a str>, F: Parser<&'a str, Output = O, Error = E>>(
  f: F,
) -> impl Parser<&'a str, Output = O, Error = E> {
  delimited(multispace0(), f, multispace0())
}

fn array<'a>() -> impl Parser<&'a str, Output = Vec<JsonValue>, Error = Error<&'a str>> {
  delimited(
    char('['),
    ws(separated_list0(ws(char(',')), json_value())),
    char(']'),
  )
}

fn object<'a>() -> impl Parser<&'a str, Output = HashMap<String, JsonValue>, Error = Error<&'a str>>
{
  map(
    delimited(
      char('{'),
      ws(separated_list0(
        ws(char(',')),
        separated_pair(string(), ws(char(':')), json_value()),
      )),
      char('}'),
    ),
    |key_values| key_values.into_iter().collect(),
  )
}

fn json_value() -> JsonParser {
  JsonParser
}

struct JsonParser;

// the main Parser implementation is done explicitely on a real type,
// because haaving json_value return `impl Parser` would result in
// "recursive opaque type" errors
impl<'a> Parser<&'a str> for JsonParser {
  type Output = JsonValue;
  type Error = Error<&'a str>;

  fn process<OM: nom::OutputMode>(
    &mut self,
    input: &'a str,
  ) -> nom::PResult<OM, &'a str, Self::Output, Self::Error> {
    use JsonValue::*;

    let mut parser = alt((
      value(Null, tag("null")),
      map(boolean(), Bool),
      map(string(), Str),
      map(double(), Num),
      map(array(), Array),
      map(object(), Object),
    ));

    parser.process::<OM>(input)
  }
}

fn json<'a>() -> impl Parser<&'a str, Output = JsonValue, Error = Error<&'a str>> {
  ws(json_value())
}

fn main() {
  let data = include_str!("../benchmarks/canada.json");

  loop {
    let _a = json()
      .process::<OutputM<Emit, Emit, Complete>>(data)
      .unwrap();
  }
}
