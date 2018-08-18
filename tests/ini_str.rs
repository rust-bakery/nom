#[macro_use]
extern crate nom;

use nom::IResult;
use nom::types::CompleteStr;

use std::collections::HashMap;

fn is_alphabetic(chr: char) -> bool {
  (chr as u8 >= 0x41 && chr as u8 <= 0x5A) || (chr as u8 >= 0x61 && chr as u8 <= 0x7A)
}

fn is_digit(chr: char) -> bool {
  chr as u8 >= 0x30 && chr as u8 <= 0x39
}

fn is_alphanumeric(chr: char) -> bool {
  is_alphabetic(chr) || is_digit(chr)
}

fn is_space(chr: char) -> bool {
  chr == ' ' || chr == '\t'
}

fn is_line_ending_or_comment(chr: char) -> bool {
  chr == ';' || chr == '\n'
}

named!(alphanumeric<CompleteStr,CompleteStr>,         take_while_s!(is_alphanumeric));
named!(not_line_ending<CompleteStr,CompleteStr>,      is_not_s!("\r\n"));
named!(space<CompleteStr,CompleteStr>,                take_while_s!(is_space));
named!(space_or_line_ending<CompleteStr,CompleteStr>, is_a_s!(" \r\n"));

fn right_bracket(c: char) -> bool {
  c == ']'
}

named!(category     <CompleteStr, &str>,
  do_parse!(
          tag_s!("[")                 >>
    name: take_till_s!(right_bracket) >>
          tag_s!("]")                 >>
          opt!(space_or_line_ending)  >>
    (name.0)
  )
);

named!(key_value    <CompleteStr,(&str,&str)>,
  do_parse!(
    key: alphanumeric                              >>
         opt!(space)                               >>
         tag_s!("=")                               >>
         opt!(space)                               >>
    val: take_till_s!(is_line_ending_or_comment)   >>
         opt!(space)                               >>
         opt!(pair!(tag_s!(";"), not_line_ending)) >>
         opt!(space_or_line_ending)                >>
    (key.0, val.0)
  )
);

named!(keys_and_values_aggregator<CompleteStr, Vec<(&str, &str)> >, many0!(key_value));

fn keys_and_values(input: CompleteStr) -> IResult<CompleteStr, HashMap<&str, &str>> {
  match keys_and_values_aggregator(input) {
    Ok((i, tuple_vec)) => Ok((i, tuple_vec.into_iter().collect())),
    Err(e) => Err(e),
  }
}

named!(category_and_keys<CompleteStr,(&str,HashMap<&str,&str>)>,
  pair!(category, keys_and_values)
);

named!(categories_aggregator<CompleteStr, Vec<(&str, HashMap<&str,&str>)> >, many0!(category_and_keys));

fn categories(input: CompleteStr) -> IResult<CompleteStr, HashMap<&str, HashMap<&str, &str>>> {
  match categories_aggregator(input) {
    Ok((i, tuple_vec)) => Ok((i, tuple_vec.into_iter().collect())),
    Err(e) => Err(e),
  }
}

#[test]
fn parse_category_test() {
  let ini_file = CompleteStr(
    "[category]

parameter=value
key = value2",
  );

  let ini_without_category = CompleteStr(
    "parameter=value
key = value2",
  );

  let res = category(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, o)) => println!("i: {} | o: {:?}", i.0, o),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_category, "category")));
}

#[test]
fn parse_key_value_test() {
  let ini_file = CompleteStr(
    "parameter=value
key = value2",
  );

  let ini_without_key_value = CompleteStr("key = value2");

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, (o1, o2))) => println!("i: {} | o: ({:?},{:?})", i.0, o1, o2),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_key_value, ("parameter", "value"))));
}

#[test]
fn parse_key_value_with_space_test() {
  let ini_file = CompleteStr(
    "parameter = value
key = value2",
  );

  let ini_without_key_value = CompleteStr("key = value2");

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, (o1, o2))) => println!("i: {} | o: ({:?},{:?})", i.0, o1, o2),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_key_value, ("parameter", "value"))));
}

#[test]
fn parse_key_value_with_comment_test() {
  let ini_file = CompleteStr(
    "parameter=value;abc
key = value2",
  );

  let ini_without_key_value = CompleteStr("key = value2");

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, (o1, o2))) => println!("i: {} | o: ({:?},{:?})", i.0, o1, o2),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_key_value, ("parameter", "value"))));
}

#[test]
fn parse_multiple_keys_and_values_test() {
  let ini_file = CompleteStr(
    "parameter=value;abc

key = value2

[category]",
  );

  let ini_without_key_value = CompleteStr("[category]");

  let res = keys_and_values(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, ref o)) => println!("i: {} | o: {:?}", i.0, o),
    _ => println!("error"),
  }

  let mut expected: HashMap<&str, &str> = HashMap::new();
  expected.insert("parameter", "value");
  expected.insert("key", "value2");
  assert_eq!(res, Ok((ini_without_key_value, expected)));
}

#[test]
fn parse_category_then_multiple_keys_and_values_test() {
  //FIXME: there can be an empty line or a comment line after a category
  let ini_file = CompleteStr(
    "[abcd]
parameter=value;abc

key = value2

[category]",
  );

  let ini_after_parser = CompleteStr("[category]");

  let res = category_and_keys(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, ref o)) => println!("i: {} | o: {:?}", i.0, o),
    _ => println!("error"),
  }

  let mut expected_h: HashMap<&str, &str> = HashMap::new();
  expected_h.insert("parameter", "value");
  expected_h.insert("key", "value2");
  assert_eq!(res, Ok((ini_after_parser, ("abcd", expected_h))));
}

#[test]
fn parse_multiple_categories_test() {
  let ini_file = CompleteStr(
    "[abcd]

parameter=value;abc

key = value2

[category]
parameter3=value3
key4 = value4
",
  );

  let res = categories(ini_file);
  //println!("{:?}", res);
  match res {
    Ok((i, ref o)) => println!("i: {} | o: {:?}", i.0, o),
    _ => println!("error"),
  }

  let mut expected_1: HashMap<&str, &str> = HashMap::new();
  expected_1.insert("parameter", "value");
  expected_1.insert("key", "value2");
  let mut expected_2: HashMap<&str, &str> = HashMap::new();
  expected_2.insert("parameter3", "value3");
  expected_2.insert("key4", "value4");
  let mut expected_h: HashMap<&str, HashMap<&str, &str>> = HashMap::new();
  expected_h.insert("abcd", expected_1);
  expected_h.insert("category", expected_2);
  assert_eq!(res, Ok((CompleteStr(""), expected_h)));
}
