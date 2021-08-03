extern crate criterion;
extern crate jemallocator;

#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use criterion::*;
use nom::{
  bytes::complete::take_while,
  character::complete::{
    alphanumeric1 as alphanumeric, char, multispace1 as multispace, space1 as space,
  },
  combinator::{map, map_res, opt},
  multi::many0,
  sequence::{delimited, pair, separated_pair, terminated},
  IResult,
};
use std::collections::HashMap;
use std::str;

fn category(i: &[u8]) -> IResult<&[u8], &str> {
  map_res(
    delimited(char('['), take_while(|c| c != b']'), char(']')),
    str::from_utf8,
  )(i)
}

fn complete_byte_slice_to_str<'a>(s: &'a [u8]) -> Result<&'a str, str::Utf8Error> {
  str::from_utf8(s)
}

fn key_value(s: &[u8]) -> IResult<&[u8], (&str, &str)> {
  let (s, key) = map_res(alphanumeric, complete_byte_slice_to_str)(s)?;
  let (s, _) = opt(space)(s)?;
  let (s, _) = char('=')(s)?;
  let (s, _) = opt(space)(s)?;
  let (s, val) = map_res(
    take_while(|c| c != b'\n' && c != b';'),
    complete_byte_slice_to_str,
  )(s)?;
  let (s, _) = opt(pair(char(';'), take_while(|c| c != b'\n')))(s)?;

  Ok((s, (key, val)))
}

fn keys_and_values(s: &[u8]) -> IResult<&[u8], HashMap<&str, &str>> {
  map(
    many0(terminated(key_value, opt(multispace))),
    |vec: Vec<_>| vec.into_iter().collect(),
  )(s)
}

fn category_and_keys(s: &[u8]) -> IResult<&[u8], (&str, HashMap<&str, &str>)> {
  let (s, category) = category(s)?;
  let (s, _) = opt(multispace)(s)?;
  let (s, keys) = keys_and_values(s)?;

  Ok((s, (category, keys)))
}

fn categories(s: &[u8]) -> IResult<&[u8], HashMap<&str, HashMap<&str, &str>>> {
  map(
    many0(separated_pair(
      category,
      opt(multispace),
      map(
        many0(terminated(key_value, opt(multispace))),
        |vec: Vec<_>| vec.into_iter().collect(),
      ),
    )),
    |vec: Vec<_>| vec.into_iter().collect(),
  )(s)
}

#[test]
fn parse_category_test() {
  let ini_file = &b"[category]

parameter=value
key = value2"[..];

  let ini_without_category = &b"\n\nparameter=value
key = value2"[..];

  let res = category(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, o)) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_category, "category")));
}

#[test]
fn parse_key_value_test() {
  let ini_file = &b"parameter=value
key = value2"[..];

  let ini_without_key_value = &b"\nkey = value2"[..];

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, (o1, o2))) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i), o1, o2),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_key_value, ("parameter", "value"))));
}

#[test]
fn parse_key_value_with_space_test() {
  let ini_file = &b"parameter = value
key = value2"[..];

  let ini_without_key_value = &b"\nkey = value2"[..];

  let res = key_value(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, (o1, o2))) => println!("i: {:?} | o: ({:?},{:?})", str::from_utf8(i), o1, o2),
    _ => println!("error"),
  }

  assert_eq!(res, Ok((ini_without_key_value, ("parameter", "value"))));
}

#[test]
fn parse_key_value_with_comment_test() {
  let ini_file = &b"parameter=value;abc
key = value2"[..];

  let ini_without_key_value = &b"\nkey = value2"[..];

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
  let ini_file = &b"parameter=value;abc

key = value2

[category]"[..];

  let ini_without_key_value = &b"[category]"[..];

  let res = keys_and_values(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, ref o)) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
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
  let ini_file = &b"[abcd]
parameter=value;abc

key = value2

[category]"[..];

  let ini_after_parser = &b"[category]"[..];

  let res = category_and_keys(ini_file);
  println!("{:?}", res);
  match res {
    Ok((i, ref o)) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
    _ => println!("error"),
  }

  let mut expected_h: HashMap<&str, &str> = HashMap::new();
  expected_h.insert("parameter", "value");
  expected_h.insert("key", "value2");
  assert_eq!(res, Ok((ini_after_parser, ("abcd", expected_h))));
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
    Ok((i, ref o)) => println!("i: {:?} | o: {:?}", str::from_utf8(i), o),
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

fn bench_ini_complete(c: &mut Criterion) {
  let s = "[owner]
name=John Doe
organization=Acme Widgets Inc.

[database]
server=192.0.2.62
port=143
file=payroll.dat
";

  let mut ini_complete_group = c.benchmark_group("bench ini complete");
  ini_complete_group.throughput(Throughput::Bytes(s.len() as u64));
  ini_complete_group.bench_with_input(BenchmarkId::new("parse", s.len()), s, |b, s| {
    b.iter(|| categories(s.as_bytes()).unwrap());
  });

  ini_complete_group.finish();
}

fn bench_ini_complete_keys_and_values(c: &mut Criterion) {
  let s = "server=192.0.2.62
port=143
file=payroll.dat
";

  fn acc(s: &[u8]) -> IResult<&[u8], Vec<(&str,&str)> > {
    many0(key_value)(s)
  }

  let mut ini_complete_keys_and_values_group =
    c.benchmark_group("bench ini complete keys and values");
  ini_complete_keys_and_values_group.throughput(Throughput::Bytes(s.len() as u64));
  ini_complete_keys_and_values_group.bench_with_input(
    BenchmarkId::new("parse", s.len()),
    s,
    |b, s| {
      b.iter(|| acc(s.as_bytes()).unwrap());
    },
  );

  ini_complete_keys_and_values_group.finish();
}

fn bench_ini_complete_key_value(c: &mut Criterion) {
  let s = "server=192.0.2.62\n";

  let mut ini_complete_key_value_group = c.benchmark_group("bench ini complete key value");
  ini_complete_key_value_group.throughput(Throughput::Bytes(s.len() as u64));
  ini_complete_key_value_group.bench_with_input(BenchmarkId::new("parse", s.len()), s, |b, s| {
    b.iter(|| key_value(s.as_bytes()).unwrap());
  });

  ini_complete_key_value_group.finish();
}

criterion_group!(
  benches,
  bench_ini_complete,
  bench_ini_complete_keys_and_values,
  bench_ini_complete_key_value
);
criterion_main!(benches);
