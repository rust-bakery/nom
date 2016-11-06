//#![feature(trace_macros)]

#[macro_use]
extern crate nom;

use nom::{digit, alphanumeric};

use std::str::{self,FromStr};
use std::collections::HashMap;

#[derive(Debug,PartialEq)]
pub enum JsonValue {
  Str(String),
  Num(f32),
  Array(Vec<JsonValue>),
  Object(HashMap<String,JsonValue>)
}

// FIXME: since we already parsed a serie of digits and dots,
// we know it is correct UTF-8. no need to use from_utf8 to
// verify it is correct
// FIXME: use alt_complete (implement ws for alt_complete)
named!(unsigned_float <f32>, map_res!(
  map_res!(
    recognize!(
      alt_complete!(
        delimited!(digit, tag!("."), opt!(complete!(digit))) |
        delimited!(opt!(digit), tag!("."), digit)            |
        digit
      )
    ),
    str::from_utf8
  ),
  FromStr::from_str
));
named!(float<f32>, map!(
  pair!(
    opt!(alt!(tag!("+") | tag!("-"))),
    unsigned_float
  ),
  |(sign, value): (Option<&[u8]>, f32)| {
    sign.and_then(|s| if s[0] == ('-' as u8) { Some(-1f32) } else { None }).unwrap_or(1f32) * value
  }
));

//FIXME: verify how json strings are formatted
named!(string<&str>,
  delimited!(
    tag!("\""),
    map_res!(escaped!(call!(alphanumeric), '\\', is_a!("\"n\\")), str::from_utf8),
    tag!("\"")
  )
);

named!(array < Vec<JsonValue> >,
  ws!(
    delimited!(
      tag!("["),
      separated_list!(tag!(","), value),
      tag!("]")
    )
  )
);

named!(key_value<(&str,JsonValue)>,
  ws!(
    separated_pair!(
      string,
      tag!(":"),
      value
    )
  )
);

named!(hash< HashMap<String,JsonValue> >,
  ws!(
    map!(
      delimited!(
        tag!("{"),
        separated_list!(tag!(","), key_value),
        tag!("}")
        ),
      |tuple_vec| {
        let mut h: HashMap<String, JsonValue> = HashMap::new();
        for (k, v) in tuple_vec {
          h.insert(String::from(k), v);
        }
        h
      }
    )
  )
);

named!(value<JsonValue>,
  ws!(
    alt!(
      hash   => { |h|   JsonValue::Object(h)            } |
      array  => { |v|   JsonValue::Array(v)             } |
      string => { |s|   JsonValue::Str(String::from(s)) } |
      float  => { |num| JsonValue::Num(num)             }
    )
  )
);



#[test]
fn hash_test() {
  let test = &b"  { \"a\"\t: 42,
  \"b\": \"x\"
  }";

//FIXME: top level value must be an object?
  println!("{:?}", value(&test[..]));
  //assert!(false);
}

#[test]
fn parse_example_test() {
  let test = &b"  { \"a\"\t: 42,
  \"b\": [ \"x\", \"y\", 12 ] ,
  \"c\": { \"hello\" : \"world\" 
  }
  }";

//FIXME: top level value must be an object?
  println!("{:?}", value(&test[..]));
  //assert!(false);
}

