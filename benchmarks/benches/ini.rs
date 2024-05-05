#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use codspeed_criterion_compat::*;

use nom::{
  bytes::complete::take_while,
  character::complete::{
    alphanumeric1 as alphanumeric, char, multispace1 as multispace, space1 as space,
  },
  combinator::{map_res, opt},
  multi::many,
  sequence::{delimited, pair, separated_pair, terminated, tuple},
  IResult, Parser,
};
use std::collections::HashMap;
use std::str;

fn category(i: &[u8]) -> IResult<&[u8], &str> {
  map_res(
    delimited(char('['), take_while(|c| c != b']'), char(']')),
    str::from_utf8,
  )
  .parse_complete(i)
}

fn key_value(i: &[u8]) -> IResult<&[u8], (&str, &str)> {
  let (i, key) = map_res(alphanumeric, str::from_utf8).parse_complete(i)?;
  let (i, _) = tuple((opt(space), char('='), opt(space))).parse_complete(i)?;
  let (i, val) =
    map_res(take_while(|c| c != b'\n' && c != b';'), str::from_utf8).parse_complete(i)?;
  let (i, _) = opt(pair(char(';'), take_while(|c| c != b'\n'))).parse_complete(i)?;
  Ok((i, (key, val)))
}

fn categories(i: &[u8]) -> IResult<&[u8], HashMap<&str, HashMap<&str, &str>>> {
  many(
    0..,
    separated_pair(
      category,
      opt(multispace),
      many(0.., terminated(key_value, opt(multispace))),
    ),
  )
  .parse_complete(i)
}

fn bench_ini(c: &mut Criterion) {
  let str = "[owner]
name=John Doe
organization=Acme Widgets Inc.

[database]
server=192.0.2.62
port=143
file=payroll.dat
\0";

  let mut group = c.benchmark_group("ini");
  group.throughput(Throughput::Bytes(str.len() as u64));
  group.bench_function(BenchmarkId::new("parse", str.len()), |b| {
    b.iter(|| categories(str.as_bytes()).unwrap())
  });
}

fn bench_ini_keys_and_values(c: &mut Criterion) {
  let str = "server=192.0.2.62
port=143
file=payroll.dat
\0";

  fn acc(i: &[u8]) -> IResult<&[u8], Vec<(&str, &str)>> {
    many(0.., key_value).parse_complete(i)
  }

  let mut group = c.benchmark_group("ini keys and values");
  group.throughput(Throughput::Bytes(str.len() as u64));
  group.bench_function(BenchmarkId::new("parse", str.len()), |b| {
    b.iter(|| acc(str.as_bytes()).unwrap())
  });
}

fn bench_ini_key_value(c: &mut Criterion) {
  let str = "server=192.0.2.62\n";

  let mut group = c.benchmark_group("ini key value");
  group.throughput(Throughput::Bytes(str.len() as u64));
  group.bench_function(BenchmarkId::new("parse", str.len()), |b| {
    b.iter(|| key_value(str.as_bytes()).unwrap())
  });
}

criterion_group!(
  benches,
  bench_ini,
  bench_ini_keys_and_values,
  bench_ini_key_value
);
criterion_main!(benches);
