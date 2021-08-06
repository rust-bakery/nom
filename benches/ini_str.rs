#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use criterion::*;

use nom::{
  bytes::complete::{is_a, tag, take_till, take_while},
  character::complete::{alphanumeric1 as alphanumeric, char, not_line_ending, space0 as space},
  combinator::opt,
  multi::many0,
  sequence::{delimited, pair, terminated, tuple},
  IResult,
};

use std::collections::HashMap;

fn is_line_ending_or_comment(chr: char) -> bool {
  chr == ';' || chr == '\n'
}

fn space_or_line_ending(i: &str) -> IResult<&str, &str> {
  is_a(" \r\n")(i)
}

fn category(i: &str) -> IResult<&str, &str> {
  terminated(
    delimited(char('['), take_while(|c| c != ']'), char(']')),
    opt(is_a(" \r\n")),
  )(i)
}

fn key_value(i: &str) -> IResult<&str, (&str, &str)> {
  let (i, key) = alphanumeric(i)?;
  let (i, _) = tuple((opt(space), tag("="), opt(space)))(i)?;
  let (i, val) = take_till(is_line_ending_or_comment)(i)?;
  let (i, _) = opt(space)(i)?;
  let (i, _) = opt(pair(tag(";"), not_line_ending))(i)?;
  let (i, _) = opt(space_or_line_ending)(i)?;
  Ok((i, (key, val)))
}

fn keys_and_values_aggregator(i: &str) -> IResult<&str, Vec<(&str, &str)>> {
  many0(key_value)(i)
}

fn keys_and_values(input: &str) -> IResult<&str, HashMap<&str, &str>> {
  match keys_and_values_aggregator(input) {
    Ok((i, tuple_vec)) => Ok((i, tuple_vec.into_iter().collect())),
    Err(e) => Err(e),
  }
}

fn category_and_keys(i: &str) -> IResult<&str, (&str, HashMap<&str, &str>)> {
  pair(category, keys_and_values)(i)
}

fn categories_aggregator(i: &str) -> IResult<&str, Vec<(&str, HashMap<&str, &str>)>> {
  many0(category_and_keys)(i)
}

fn categories(input: &str) -> IResult<&str, HashMap<&str, HashMap<&str, &str>>> {
  match categories_aggregator(input) {
    Ok((i, tuple_vec)) => Ok((i, tuple_vec.into_iter().collect())),
    Err(e) => Err(e),
  }
}

fn bench_ini_str(c: &mut Criterion) {
  let s = "[owner]
name=John Doe
organization=Acme Widgets Inc.

[database]
server=192.0.2.62
port=143
file=payroll.dat
";

  let mut group = c.benchmark_group("ini str");
  group.throughput(Throughput::Bytes(s.len() as u64));
  group.bench_function(BenchmarkId::new("parse", s.len()), |b| {
    b.iter(|| categories(s).unwrap())
  });
}

criterion_group!(benches, bench_ini_str);
criterion_main!(benches);
