#![cfg(feature = "alloc")]

use nom::{
  branch::alt,
  bytes::complete::{escaped, tag, take_while},
  character::complete::{alphanumeric1 as alphanumeric, char, one_of},
  combinator::{cut, map},
  error::{context, ParseError},
  multi::separated_list0,
  number::complete::double,
  sequence::{preceded, separated_pair, terminated},
  IResult,
};
use std::collections::HashMap;

use std::cell::Cell;
use std::str;

#[derive(Clone, Debug)]
pub struct JsonValue<'a, 'b> {
  input: &'a str,
  pub offset: &'b Cell<usize>,
}

impl<'a, 'b: 'a> JsonValue<'a, 'b> {
  pub fn new(input: &'a str, offset: &'b Cell<usize>) -> JsonValue<'a, 'b> {
    JsonValue { input, offset }
  }

  pub fn offset(&self, input: &'a str) {
    let offset = input.as_ptr() as usize - self.input.as_ptr() as usize;
    self.offset.set(offset);
  }

  pub fn data(&self) -> &'a str {
    &self.input[self.offset.get()..]
  }

  pub fn string(&self) -> Option<&'a str> {
    println!("string()");
    match string(self.data()) {
      Ok((i, s)) => {
        self.offset(i);
        println!("-> {}", s);
        Some(s)
      }
      _ => None,
    }
  }

  pub fn boolean(&self) -> Option<bool> {
    println!("boolean()");
    match boolean(self.data()) {
      Ok((i, o)) => {
        self.offset(i);
        println!("-> {}", o);
        Some(o)
      }
      _ => None,
    }
  }

  pub fn number(&self) -> Option<f64> {
    println!("number()");
    match double::<_, ()>(self.data()) {
      Ok((i, o)) => {
        self.offset(i);
        println!("-> {}", o);
        Some(o)
      }
      _ => None,
    }
  }

  pub fn array(&self) -> Option<impl Iterator<Item = JsonValue<'a, 'b>>> {
    println!("array()");

    match tag::<_, _, ()>("[")(self.data()) {
      Err(_) => None,
      Ok((i, _)) => {
        println!("[");
        self.offset(i);
        let mut first = true;
        let mut done = false;
        let mut previous = std::usize::MAX;

        let v = self.clone();

        Some(std::iter::from_fn(move || {
          if done {
            return None;
          }

          // if we ignored one of the items, skip over the value
          if v.offset.get() == previous {
            println!("skipping value");
            match value(v.data()) {
              Ok((i, _)) => {
                v.offset(i);
              }
              Err(_) => {}
            }
          }

          match tag::<_, _, ()>("]")(v.data()) {
            Ok((i, _)) => {
              println!("]");
              v.offset(i);
              done = true;
              return None;
            }
            Err(_) => {}
          };

          if first {
            first = false;
          } else {
            match tag::<_, _, ()>(",")(v.data()) {
              Ok((i, _)) => {
                println!(",");
                v.offset(i);
              }
              Err(_) => {
                done = true;
                return None;
              }
            }
          }

          println!("-> {}", v.data());
          previous = v.offset.get();
          Some(v.clone())
        }))
      }
    }
  }

  pub fn object(&self) -> Option<impl Iterator<Item = (&'a str, JsonValue<'a, 'b>)>> {
    println!("object()");
    match tag::<_, _, ()>("{")(self.data()) {
      Err(_) => None,
      Ok((i, _)) => {
        self.offset(i);

        println!("{{");

        let mut first = true;
        let mut done = false;
        let mut previous = std::usize::MAX;

        let v = self.clone();

        Some(std::iter::from_fn(move || {
          if done {
            return None;
          }

          // if we ignored one of the items, skip over the value
          if v.offset.get() == previous {
            println!("skipping value");
            match value(v.data()) {
              Ok((i, _)) => {
                v.offset(i);
              }
              Err(_) => {}
            }
          }

          match tag::<_, _, ()>("}")(v.data()) {
            Ok((i, _)) => {
              println!("}}");
              v.offset(i);
              done = true;
              return None;
            }
            Err(_) => {}
          };

          if first {
            first = false;
          } else {
            match tag::<_, _, ()>(",")(v.data()) {
              Ok((i, _)) => {
                println!(",");
                v.offset(i);
              }
              Err(_) => {
                done = true;
                return None;
              }
            }
          }

          match string(v.data()) {
            Ok((i, key)) => {
              v.offset(i);

              match tag::<_, _, ()>(":")(v.data()) {
                Err(_) => None,
                Ok((i, _)) => {
                  v.offset(i);

                  previous = v.offset.get();

                  println!("-> {} => {}", key, v.data());
                  Some((key, v.clone()))
                }
              }
            }
            _ => None,
          }
        }))
      }
    }
  }
}

fn sp<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
  let chars = " \t\r\n";

  take_while(move |c| chars.contains(c))(i)
}

fn parse_str<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
  escaped(alphanumeric, '\\', one_of("\"n\\"))(i)
}

fn string<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
  context(
    "string",
    preceded(char('\"'), cut(terminated(parse_str, char('\"')))),
  )(i)
}

fn boolean<'a>(input: &'a str) -> IResult<&'a str, bool> {
  alt((map(tag("false"), |_| false), map(tag("true"), |_| true)))(input)
}

fn array<'a>(i: &'a str) -> IResult<&'a str, ()> {
  context(
    "array",
    preceded(
      char('['),
      cut(terminated(
        map(separated_list0(preceded(sp, char(',')), value), |_| ()),
        preceded(sp, char(']')),
      )),
    ),
  )(i)
}

fn key_value<'a>(i: &'a str) -> IResult<&'a str, (&'a str, ())> {
  separated_pair(preceded(sp, string), cut(preceded(sp, char(':'))), value)(i)
}

fn hash<'a>(i: &'a str) -> IResult<&'a str, ()> {
  context(
    "map",
    preceded(
      char('{'),
      cut(terminated(
        map(separated_list0(preceded(sp, char(',')), key_value), |_| ()),
        preceded(sp, char('}')),
      )),
    ),
  )(i)
}

fn value<'a>(i: &'a str) -> IResult<&'a str, ()> {
  preceded(
    sp,
    alt((
      hash,
      array,
      map(string, |_| ()),
      map(double, |_| ()),
      map(boolean, |_| ()),
    )),
  )(i)
}

/// object(input) -> iterator over (key, JsonValue)
/// array(input) -> iterator over JsonValue
///
/// JsonValue.string -> iterator over String (returns None after first successful call)
///
/// object(input).filter(|(k, _)| k == "users").flatten(|(_, v)| v.object()).filter(|(k, _)| k == "city").flatten(|(_,v)| v.string())
fn main() {
  /*let data = "{
  \"users\": {
    \"user1\" : { \"city\": \"Nantes\", \"country\": \"France\" },
    \"user2\" : { \"city\": \"Bruxelles\", \"country\": \"Belgium\" },
    \"user3\": { \"city\": \"Paris\", \"country\": \"France\", \"age\": 30 }
  },
  \"countries\": [\"France\", \"Belgium\"]
  }";
  */
  let data = "{\"users\":{\"user1\":{\"city\":\"Nantes\",\"country\":\"France\"},\"user2\":{\"city\":\"Bruxelles\",\"country\":\"Belgium\"},\"user3\":{\"city\":\"Paris\",\"country\":\"France\",\"age\":30}},\"countries\":[\"France\",\"Belgium\"]}";

  let offset = Cell::new(0);
  {
    let parser = JsonValue::new(data, &offset);

    if let Some(o) = parser.object() {
      let s: HashMap<&str, &str> = o
        .filter(|(k, _)| *k == "users")
        .filter_map(|(_, v)| v.object())
        .flatten()
        .filter_map(|(user, v)| v.object().map(|o| (user, o)))
        .map(|(user, o)| {
          o.filter(|(k, _)| *k == "city")
            .filter_map(move |(_, v)| v.string().map(|s| (user, s)))
        })
        .flatten()
        .collect();

      println!("res = {:?}", s);
    }
  };
}
