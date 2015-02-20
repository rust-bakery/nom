#[macro_use]
extern crate nom;

use nom::{IResult,FlatMapOpt,line_ending,not_line_ending, space, alphanumeric, multispace};
use nom::IResult::*;

use std::str;
use std::collections::HashMap;


fn empty_result(i:&[u8]) -> IResult<&[u8], ()> { Done(i,()) }
tag!(semicolon ";".as_bytes());
tag!(lsb       "[".as_bytes());
tag!(rsb       "]".as_bytes());
tag!(equal     "=".as_bytes());


take_until_and_leave!(category_bytes "]".as_bytes());
fn category_name(input: &[u8]) -> IResult<&[u8], &str> {
  category_bytes(input).map_res(str::from_utf8)
}

take_until!(not_equal      "=".as_bytes());
take_until_either_and_leave!(value_bytes "\n;".as_bytes());

fn value_parser(input:&[u8]) -> IResult<&[u8], &str> {
  value_bytes(input).map_res(str::from_utf8)
}

fn parameter_parser(input: &[u8]) -> IResult<&[u8], &str> {
  alphanumeric(input).map_res(str::from_utf8)
}

o!(comment_body     <&[u8], &[u8]>       semicolon ~ [ not_line_ending ]);
o!(comment          <&[u8], ()>          comment_body ~ line_ending ~ [ empty_result ]);
opt!(opt_comment    <&[u8], &[u8]>       comment_body);

chain!(category     <&[u8], &str>,
          lsb             ~
    name: category_name   ~
          rsb             ~
          multispace?     ,
    ||{ name }
);
chain!(key_value    <&[u8],(&str,&str)>,
    key: parameter_parser ~
         space?           ~
         equal            ~
         space?           ~
    val: value_parser     ~
         space?           ~
         comment_body?    ~
         multispace?      ,
    ||{(key, val)}
);

fn keys_and_values<'a>(input: &'a[u8], mut z: HashMap<&'a str, &'a str>) -> IResult<&'a[u8], HashMap<&'a str, &'a str> > {
  fold0_impl!(<&[u8], HashMap<&str, &str> >, | mut h:HashMap<&'a str, &'a str>, (k, v)| {
    h.insert(k,v);
    h
  }, key_value, input, z);
}

fn keys_and_values_wrapper<'a>(input:&'a[u8]) -> IResult<&'a[u8], HashMap<&'a str, &'a str> > {
  let h: HashMap<&str, &str> = HashMap::new();
  let res = keys_and_values(input, h);
  //println!("{:?}", res);
  res
}

chain!(category_and_keys<&[u8],(&str,HashMap<&str,&str>)>,
    category: category            ~
    keys: keys_and_values_wrapper ,
    move ||{(category, keys)}
);

fn categories<'a>(input: &'a[u8]) -> IResult<&'a[u8], HashMap<&'a str, HashMap<&'a str, &'a str> > > {
  let z: HashMap<&str, HashMap<&str, &str>> = HashMap::new();
  fold0_impl!(<&[u8], HashMap<&str, HashMap<&str, &str> > >, |mut h:HashMap<&'a str, HashMap<&'a str, &'a str> >, (k, v)| {
    h.insert(k,v);
    h
  }, category_and_keys, input, z);
}

#[test]
fn parse_comment_test() {
  let ini_file = ";comment
[category]
parameter=value
key = value2

[other]
number = 1234
str = a b cc dd ; comment";

  let ini_without_comment = "[category]
parameter=value
key = value2

[other]
number = 1234
str = a b cc dd ; comment";

  let res = comment(ini_file.as_bytes());
  println!("{:?}", res);
  match res {
    IResult::Done(i, o) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_comment.as_bytes(), ()));
}

#[test]
fn parse_category_test() {
  let ini_file = "[category]

parameter=value
key = value2";

  let ini_without_category = "parameter=value
key = value2";

  let res = category(ini_file.as_bytes());
  println!("{:?}", res);
  match res {
    IResult::Done(i, o) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_category.as_bytes(), "category"));
}

#[test]
fn parse_value_test() {
  let ini_file1 = "value
key =";
  let end = "
key =";

  let res = value_parser(ini_file1.as_bytes());
  println!("{:?}", res);
  match res {
    IResult::Done(i, o) => println!("i: {:?} | o: {:?})", str::from_utf8(i), o),
    _ => println!("error")
  }

  assert_eq!(res, Done(end.as_bytes(),  "value"));

  let ini_file2 = "value;blah
key =";
  let end2 = ";blah
key =";

  let res2 = value_parser(ini_file2.as_bytes());
  println!("{:?}", res2);
  match res2 {
    IResult::Done(i, o) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error")
  }

  assert_eq!(res2, Done(end2.as_bytes(),  "value"));
}

#[test]
fn parse_key_value_test() {
  let ini_file = "parameter=value
key = value2";

  let ini_without_key_value = "key = value2";

  let res = key_value(ini_file.as_bytes());
  println!("{:?}", res);
  match res {
    IResult::Done(i, (o1, o2)) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i), o1, o2),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_key_value.as_bytes(), ("parameter", "value")));
}


#[test]
fn parse_key_value_with_space_test() {
  let ini_file = "parameter = value
key = value2";

  let ini_without_key_value = "key = value2";

  let res = key_value(ini_file.as_bytes());
  println!("{:?}", res);
  match res {
    IResult::Done(i, (o1, o2)) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i), o1, o2),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_key_value.as_bytes(), ("parameter", "value")));
}

#[test]
fn parse_key_value_with_comment_test() {
  let ini_file = "parameter=value;abc
key = value2";

  let ini_without_key_value = "key = value2";

  let res = key_value(ini_file.as_bytes());
  println!("{:?}", res);
  match res {
    IResult::Done(i, (o1, o2)) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i), o1, o2),
    _ => println!("error")
  }

  assert_eq!(res, Done(ini_without_key_value.as_bytes(), ("parameter", "value")));
}

#[test]
fn parse_multiple_keys_and_values_test() {
  let ini_file = "parameter=value;abc

key = value2

[category]";

  let ini_without_key_value = "[category]";

  let h: HashMap<&str, &str> = HashMap::new();
  let res = keys_and_values(ini_file.as_bytes(), h);
  println!("{:?}", res);
  match res {
    IResult::Done(i, ref o) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error")
  }

  let mut expected: HashMap<&str, &str> = HashMap::new();
  expected.insert("parameter", "value");
  expected.insert("key", "value2");
  assert_eq!(res, Done(ini_without_key_value.as_bytes(), expected));
}

#[test]
fn parse_category_then_multiple_keys_and_values_test() {
  //FIXME: there can be an empty line or a comment line after a category
  let ini_file = "[abcd]
parameter=value;abc

key = value2

[category]";

  let ini_after_parser = "[category]";

  let res = category_and_keys(ini_file.as_bytes());
  println!("{:?}", res);
  match res {
    IResult::Done(i, ref o) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error")
  }

  let mut expected_h: HashMap<&str, &str> = HashMap::new();
  expected_h.insert("parameter", "value");
  expected_h.insert("key", "value2");
  assert_eq!(res, Done(ini_after_parser.as_bytes(), ("abcd", expected_h)));
}

#[test]
fn parse_multiple_categories_test() {
  let ini_file = "[abcd]

parameter=value;abc

key = value2

[category]
parameter3=value3
key4 = value4
";

  let ini_after_parser = "";

  let res = categories(ini_file.as_bytes());
  println!("{:?}", res);
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
  assert_eq!(res, Done(ini_after_parser.as_bytes(), expected_h));
}

