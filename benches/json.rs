#[macro_use]
extern crate nom;
#[macro_use]
extern crate criterion;
extern crate jemallocator;

#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use criterion::Criterion;
use nom::{error::ErrorKind, character::alphanumeric, number::recognize_float};


use std::str;
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
pub enum JsonValue {
  Str(String),
  Boolean(bool),
  Num(f32),
  Array(Vec<JsonValue>),
  Object(HashMap<String, JsonValue>),
}

named!(float<f32>, flat_map!(recognize_float, parse_to!(f32)));

//FIXME: verify how json strings are formatted
named!(
  string<&str>,
  delimited!(
    char!('\"'),
    map_res!(
      escaped!(call!(alphanumeric), '\\', one_of!("\"n\\")),
      str::from_utf8
    ),
    //map_res!(escaped!(take_while1!(is_alphanumeric), '\\', one_of!("\"n\\")), str::from_utf8),
    char!('\"')
  )
);

named!(
  boolean<bool>,
  alt!(value!(false, tag!("false")) | value!(true, tag!("true")))
);

named!(
  array<Vec<JsonValue>>,
  ws!(delimited!(
    char!('['),
    separated_list!(char!(','), value),
    char!(']')
  ))
);

named!(
  key_value<(&str, JsonValue)>,
  ws!(separated_pair!(string, char!(':'), value))
);

named!(
  hash<HashMap<String, JsonValue>>,
  ws!(map!(
    delimited!(
      char!('{'),
      separated_list!(char!(','), key_value),
      char!('}')
    ),
    |tuple_vec| tuple_vec
      .into_iter()
      .map(|(k, v)| (String::from(k), v))
      .collect()
  ))
);

named!(
  value<JsonValue>,
  ws!(alt!(
      hash    => { |h| JsonValue::Object(h)            } |
      array   => { |v| JsonValue::Array(v)             } |
      string  => { |s| JsonValue::Str(String::from(s)) } |
      float   => { |f| JsonValue::Num(f)               } |
      boolean => { |b| JsonValue::Boolean(b)           }
    ))
);

fn json_bench(c: &mut Criterion) {
  let data = &b"  { \"a\"\t: 42,
  \"b\": [ \"x\", \"y\", 12 ] ,
  \"c\": { \"hello\" : \"world\"
  }
  }  \0";

  //println!("data:\n{:?}", value(&data[..]));
  c.bench_function("json", move |b| {
    b.iter(|| value(&data[..]).unwrap());
  });
}

fn recognize_float_bytes(c: &mut Criterion) {
  use nom::number::recognize_float;
  c.bench_function("recognize float bytes", |b| {
    b.iter(|| recognize_float::<_, (_,ErrorKind)>(&b"-1.234E-12"[..]));
  });
}

fn recognize_float_str(c: &mut Criterion) {
  use nom::number::recognize_float;
  c.bench_function("recognize float str", |b| {
    b.iter(|| recognize_float::<_, (_,ErrorKind)>("-1.234E-12"));
  });
}

fn float_bytes(c: &mut Criterion) {
  use nom::number::float;
  c.bench_function("float bytes", |b| {
    b.iter(|| float::<_, (_,ErrorKind)>(&b"-1.234E-12"[..]));
  });
}

fn float_str(c: &mut Criterion) {
  use nom::number::float_s;
  c.bench_function("float str", |b| {
    b.iter(|| float_s::<_, (_,ErrorKind)>("-1.234E-12"));
  });
}

criterion_group!(benches, json_bench, recognize_float_bytes, recognize_float_str, float_bytes, float_str);
criterion_main!(benches);
