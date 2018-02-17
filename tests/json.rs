#![cfg(feature = "alloc")]
//#![feature(trace_macros)]

#[macro_use]
extern crate nom;

use nom::{is_alphanumeric, recognize_float};

use std::str;
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
pub enum JsonValue {
  Str(String),
  Num(f32),
  Array(Vec<JsonValue>),
  Object(HashMap<String, JsonValue>),
}

named!(float<f32>, flat_map!(recognize_float, parse_to!(f32)));

//FIXME: verify how json strings are formatted
named!(
  string<&str>,
  delimited!(
    tag!("\""),
    //map_res!(escaped!(call!(alphanumeric), '\\', is_a!("\"n\\")), str::from_utf8),
    map_res!(
      escaped!(take_while1!(is_alphanumeric), '\\', one_of!("\"n\\")),
      str::from_utf8
    ),
    tag!("\"")
  )
);

named!(
  array<Vec<JsonValue>>,
  ws!(delimited!(
    tag!("["),
    separated_list!(tag!(","), value),
    tag!("]")
  ))
);

named!(
  key_value<(&str, JsonValue)>,
  ws!(separated_pair!(string, tag!(":"), value))
);

named!(
  hash<HashMap<String, JsonValue>>,
  ws!(map!(
    delimited!(tag!("{"), separated_list!(tag!(","), key_value), tag!("}")),
    |tuple_vec| {
      let mut h: HashMap<String, JsonValue> = HashMap::new();
      for (k, v) in tuple_vec {
        h.insert(String::from(k), v);
      }
      h
    }
  ))
);

named!(
  value<JsonValue>,
  ws!(alt!(
      hash   => { |h|   JsonValue::Object(h)            } |
      array  => { |v|   JsonValue::Array(v)             } |
      string => { |s|   JsonValue::Str(String::from(s)) } |
      float  => { |num| JsonValue::Num(num)             }
    ))
);

#[test]
fn hash_test() {
  let test = &b"  { \"a\"\t: 42,
  \"b\": \"x\"
  }\0";

  //FIXME: top level value must be an object?
  println!("{:?}", value(&test[..]).unwrap());
  //assert!(false);
}

#[test]
fn parse_example_test() {
  let test = &b"  { \"a\"\t: 42,
  \"b\": [ \"x\", \"y\", 12 ] ,
  \"c\": { \"hello\" : \"world\"
  }
  }\0";

  //FIXME: top level value must be an object?
  println!("{:?}", value(&test[..]).unwrap());
  //assert!(false);
}
