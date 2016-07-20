
#[macro_use]
extern crate nom;

use nom::{IResult,not_line_ending, space, alphanumeric, multispace};

use std::str;
use std::collections::HashMap;

named!(category<&str>, map_res!(
    terminated!(
        delimited!(tag!("["), take_until!("]"), tag!("]")),
        opt!(multispace)
    ),
    str::from_utf8
));

named!(key_value    <&[u8],(&str,&str)>,
  chain!(
    key: map_res!(alphanumeric, std::str::from_utf8) ~
         space?                            ~
         tag!("=")                         ~
         space?                            ~
    val: map_res!(
           take_until_either!("\n;"),
           str::from_utf8
         )                                 ~
         space?                            ~
         chain!(
           tag!(";")        ~
           not_line_ending  ,
           ||{}
         ) ?                               ~
         multispace?                       ,
    ||{(key, val)}
  )
);


named!(keys_and_values_aggregator<&[u8], Vec<(&str,&str)> >, many0!(key_value));

fn keys_and_values(input:&[u8]) -> IResult<&[u8], HashMap<&str, &str> > {
  let mut h: HashMap<&str, &str> = HashMap::new();

  match keys_and_values_aggregator(input) {
    IResult::Done(i,tuple_vec) => {
      for &(k,v) in &tuple_vec {
        h.insert(k, v);
      }
      IResult::Done(i, h)
    },
    IResult::Incomplete(a)     => IResult::Incomplete(a),
    IResult::Error(a)          => IResult::Error(a)
  }
}

named!(category_and_keys<&[u8],(&str,HashMap<&str,&str>)>,
  chain!(
    category: category    ~
    keys: keys_and_values ,
    move ||{(category, keys)}
  )
);

named!(categories_aggregator<&[u8], Vec<(&str, HashMap<&str,&str>)> >, many0!(category_and_keys));

fn categories(input: &[u8]) -> IResult<&[u8], HashMap<&str, HashMap<&str, &str> > > {
  let mut h: HashMap<&str, HashMap<&str, &str>> = HashMap::new();

  match categories_aggregator(input) {
    IResult::Done(i,tuple_vec) => {
      for &(k,ref v) in &tuple_vec {
        h.insert(k, v.clone());
      }
      IResult::Done(i, h)
    },
    IResult::Incomplete(a)     => IResult::Incomplete(a),
    IResult::Error(a)          => IResult::Error(a)
  }
}

#[test]
fn parse_category_test() {
  let ini_file = &b"[category]

parameter=value
key = value2"[..];

  let ini_without_category = &b"parameter=value
key = value2"[..];

  let res = category(ini_file);
  println!("{:?}", res);
  match res {
    IResult::Done(i, o) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error")
  }

  assert_eq!(res, IResult::Done(ini_without_category, "category"));
}

#[test]
fn parse_key_value_test() {
  let ini_file = &b"parameter=value
key = value2"[..];

  let ini_without_key_value = &b"key = value2"[..];

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    IResult::Done(i, (o1, o2)) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i), o1, o2),
    _ => println!("error")
  }

  assert_eq!(res, IResult::Done(ini_without_key_value, ("parameter", "value")));
}


#[test]
fn parse_key_value_with_space_test() {
  let ini_file = &b"parameter = value
key = value2"[..];

  let ini_without_key_value = &b"key = value2"[..];

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    IResult::Done(i, (o1, o2)) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i), o1, o2),
    _ => println!("error")
  }

  assert_eq!(res, IResult::Done(ini_without_key_value, ("parameter", "value")));
}

#[test]
fn parse_key_value_with_comment_test() {
  let ini_file = &b"parameter=value;abc
key = value2"[..];

  let ini_without_key_value = &b"key = value2"[..];

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    IResult::Done(i, (o1, o2)) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i), o1, o2),
    _ => println!("error")
  }

  assert_eq!(res, IResult::Done(ini_without_key_value, ("parameter", "value")));
}

#[test]
fn parse_multiple_keys_and_values_test() {
  let ini_file = &b"parameter=value;abc

key = value2

[category]"[..];

  let ini_without_key_value = &b"[category]"[..];

  let res = keys_and_values(ini_file);
  println!("{:?}", res);
  match res {
    IResult::Done(i, ref o) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error")
  }

  let mut expected: HashMap<&str, &str> = HashMap::new();
  expected.insert("parameter", "value");
  expected.insert("key", "value2");
  assert_eq!(res, IResult::Done(ini_without_key_value, expected));
}

#[test]
fn parse_category_then_multiple_keys_and_values_test() {
  //FIXME: there can be an empty line or a comment line after a category
  let ini_file = &b"[abcd]
parameter=value;abc

key = value2

[category]"[..];

  let ini_after_parser = &b"[category]"[..];

  let res = category_and_keys(ini_file);
  println!("{:?}", res);
  match res {
    IResult::Done(i, ref o) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error")
  }

  let mut expected_h: HashMap<&str, &str> = HashMap::new();
  expected_h.insert("parameter", "value");
  expected_h.insert("key", "value2");
  assert_eq!(res, IResult::Done(ini_after_parser, ("abcd", expected_h)));
}

#[test]
fn parse_multiple_categories_test() {
  let ini_file = &b"[abcd]

parameter=value;abc

key = value2

[category]
parameter3=value3
key4 = value4
"[..];

  let ini_after_parser = &b""[..];

  let res = categories(ini_file);
  //println!("{:?}", res);
  match res {
    IResult::Done(i, ref o) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error")
  }

  let mut expected_1: HashMap<&str, &str> = HashMap::new();
  expected_1.insert("parameter", "value");
  expected_1.insert("key", "value2");
  let mut expected_2: HashMap<&str, &str> = HashMap::new();
  expected_2.insert("parameter3", "value3");
  expected_2.insert("key4", "value4");
  let mut expected_h: HashMap<&str, HashMap<&str, &str>> = HashMap::new();
  expected_h.insert("abcd",     expected_1);
  expected_h.insert("category", expected_2);
  assert_eq!(res, IResult::Done(ini_after_parser, expected_h));
}
