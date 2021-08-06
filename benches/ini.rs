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
  sequence::{delimited, pair, separated_pair, terminated, tuple},
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

fn key_value(i: &[u8]) -> IResult<&[u8], (&str, &str)> {
  let (i, key) = map_res(alphanumeric, str::from_utf8)(i)?;
  let (i, _) = tuple((opt(space), char('='), opt(space)))(i)?;
  let (i, val) = map_res(take_while(|c| c != b'\n' && c != b';'), str::from_utf8)(i)?;
  let (i, _) = opt(pair(char(';'), take_while(|c| c != b'\n')))(i)?;
  Ok((i, (key, val)))
}

fn categories(i: &[u8]) -> IResult<&[u8], HashMap<&str, HashMap<&str, &str>>> {
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
  )(i)
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
    many0(key_value)(i)
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
