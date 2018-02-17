#[macro_use]
extern crate nom;

use nom::{alphanumeric, multispace, space};
use nom::types::CompleteByteSlice;

use std::str;
use std::collections::HashMap;

named!(category<CompleteByteSlice, &str>, map_res!(
    delimited!(
      char!('['),
      take_while!(call!(|c| c != b']')),
      char!(']')
    ),
    complete_byte_slice_to_str
));

fn complete_byte_slice_to_str<'a>(s: CompleteByteSlice<'a>) -> Result<&'a str, str::Utf8Error> {
  str::from_utf8(s.0)
}

named!(key_value    <CompleteByteSlice,(&str,&str)>,
  do_parse!(
     key: map_res!(alphanumeric, complete_byte_slice_to_str)
  >>      opt!(space)
  >>      char!('=')
  >>      opt!(space)
  >> val: map_res!(
           take_while!(call!(|c| c != b'\n' && c != b';')),
           complete_byte_slice_to_str
         )
  >>      opt!(pair!(char!(';'), take_while!(call!(|c| c != b'\n'))))
  >>      (key, val)
  )
);

named!(keys_and_values<CompleteByteSlice, HashMap<&str, &str> >,
  map!(
    many0!(terminated!(key_value, opt!(multispace))),
    |vec: Vec<_>| vec.into_iter().collect()
  )
);

named!(category_and_keys<CompleteByteSlice,(&str,HashMap<&str,&str>)>,
  do_parse!(
    category: category         >>
              opt!(multispace) >>
    keys: keys_and_values      >>
    (category, keys)
  )
);

named!(categories<CompleteByteSlice, HashMap<&str, HashMap<&str,&str> > >,
  map!(
    many0!(
      separated_pair!(
        category,
        opt!(multispace),
        map!(
          many0!(terminated!(key_value, opt!(multispace))),
          |vec: Vec<_>| vec.into_iter().collect()
        )
      )
    ),
    |vec: Vec<_>| vec.into_iter().collect()
  )
);

#[test]
fn parse_category_test() {
  let ini_file = CompleteByteSlice(
    b"[category]

parameter=value
key = value2",
  );

  let ini_without_category = CompleteByteSlice(
    b"\n\nparameter=value
key = value2",
  );

  let res = category(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, o)) => println!("i: {:?} | o: {:?}", str::from_utf8(i.0), o),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_category, "category")));
}

#[test]
fn parse_key_value_test() {
  let ini_file = CompleteByteSlice(
    b"parameter=value
key = value2",
  );

  let ini_without_key_value = CompleteByteSlice(b"\nkey = value2");

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, (o1, o2))) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i.0), o1, o2),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_key_value, ("parameter", "value"))));
}

#[test]
fn parse_key_value_with_space_test() {
  let ini_file = CompleteByteSlice(
    b"parameter = value
key = value2",
  );

  let ini_without_key_value = CompleteByteSlice(b"\nkey = value2");

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, (o1, o2))) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i.0), o1, o2),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_key_value, ("parameter", "value"))));
}

#[test]
fn parse_key_value_with_comment_test() {
  let ini_file = CompleteByteSlice(
    b"parameter=value;abc
key = value2",
  );

  let ini_without_key_value = CompleteByteSlice(b"\nkey = value2");

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, (o1, o2))) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i.0), o1, o2),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_key_value, ("parameter", "value"))));
}

#[test]
fn parse_multiple_keys_and_values_test() {
  let ini_file = CompleteByteSlice(
    b"parameter=value;abc

key = value2

[category]",
  );

  let ini_without_key_value = CompleteByteSlice(b"[category]");

  let res = keys_and_values(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, ref o)) => println!("i: {:?} | o: {:?}", str::from_utf8(i.0), o),
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
  let ini_file = CompleteByteSlice(
    b"[abcd]
parameter=value;abc

key = value2

[category]",
  );

  let ini_after_parser = CompleteByteSlice(b"[category]");

  let res = category_and_keys(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, ref o)) => println!("i: {:?} | o: {:?}", str::from_utf8(i.0), o),
    _ => println!("error"),
  }

  let mut expected_h: HashMap<&str, &str> = HashMap::new();
  expected_h.insert("parameter", "value");
  expected_h.insert("key", "value2");
  assert_eq!(res, Ok((ini_after_parser, ("abcd", expected_h))));
}

#[test]
fn parse_multiple_categories_test() {
  let ini_file = CompleteByteSlice(
    b"[abcd]

parameter=value;abc

key = value2

[category]
parameter3=value3
key4 = value4
",
  );

  let ini_after_parser = CompleteByteSlice(b"");

  let res = categories(ini_file);
  //println!("{:?}", res);
  match res {
    Ok((i, ref o)) => println!("i: {:?} | o: {:?}", str::from_utf8(i.0), o),
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
  assert_eq!(res, Ok((ini_after_parser, expected_h)));
}
