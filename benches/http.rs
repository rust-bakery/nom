#![cfg_attr(rustfmt, rustfmt_skip)]

#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use criterion::*;
use nom::{IResult, bytes::complete::{tag, take_while1}, character::complete::{line_ending, char}, multi::many1};

#[cfg_attr(rustfmt, rustfmt_skip)]
#[derive(Debug)]
struct Request<'a> {
  method:  &'a [u8],
  uri:     &'a [u8],
  version: &'a [u8],
}

#[derive(Debug)]
struct Header<'a> {
  name: &'a [u8],
  value: Vec<&'a [u8]>,
}

#[cfg_attr(rustfmt, rustfmt_skip)]
#[cfg_attr(feature = "cargo-clippy", allow(match_same_arms))]
fn is_token(c: u8) -> bool {
  match c {
    128..=255 => false,
    0..=31    => false,
    b'('      => false,
    b')'      => false,
    b'<'      => false,
    b'>'      => false,
    b'@'      => false,
    b','      => false,
    b';'      => false,
    b':'      => false,
    b'\\'     => false,
    b'"'      => false,
    b'/'      => false,
    b'['      => false,
    b']'      => false,
    b'?'      => false,
    b'='      => false,
    b'{'      => false,
    b'}'      => false,
    b' '      => false,
    _         => true,
  }
}

fn not_line_ending(c: u8) -> bool {
  c != b'\r' && c != b'\n'
}

fn is_space(c: u8) -> bool {
  c == b' '
}

fn is_not_space(c: u8) -> bool {
  c != b' '
}
fn is_horizontal_space(c: u8) -> bool {
  c == b' ' || c == b'\t'
}

fn is_version(c: u8) -> bool {
  c >= b'0' && c <= b'9' || c == b'.'
}

fn request_line(input: &[u8]) -> IResult<&[u8], Request<'_>> {
  let (input, method) = take_while1(is_token)(input)?;
  let (input, _) = take_while1(is_space)(input)?;
  let (input, uri) = take_while1(is_not_space)(input)?;
  let (input, _) = take_while1(is_space)(input)?;
  let (input, version) = http_version(input)?;
  let (input, _) = line_ending(input)?;

  Ok((input, Request {method, uri, version}))
}

fn http_version(input: &[u8]) -> IResult<&[u8], &[u8]> {
  let (input, _) = tag("HTTP/")(input)?;
  let (input, version) = take_while1(is_version)(input)?;

  Ok((input, version))
}

fn message_header_value(input: &[u8]) -> IResult<&[u8], &[u8]> {
  let (input, _) = take_while1(is_horizontal_space)(input)?;
  let (input, data) = take_while1(not_line_ending)(input)?;
  let (input, _) = line_ending(input)?;

  Ok((input, data))
}

fn message_header(input: &[u8]) -> IResult<&[u8], Header<'_>> {
  let (input, name) = take_while1(is_token)(input)?;
  let (input, _) = char(':')(input)?;
  let (input, value) = many1(message_header_value)(input)?;

  Ok((input, Header{ name, value }))
}

fn request(input: &[u8]) -> IResult<&[u8], (Request<'_>, Vec<Header<'_>>)> {
  let (input, req) = request_line(input)?;
  let (input, h) = many1(message_header)(input)?;
  let (input, _) = line_ending(input)?;

  Ok((input, (req, h)))
}


fn parse(data: &[u8]) -> Option<Vec<(Request<'_>, Vec<Header<'_>>)>> {
  let mut buf = &data[..];
  let mut v = Vec::new();
  loop {
    match request(buf) {
      Ok((b, r)) => {
        buf = b;
        v.push(r);

        if b.is_empty() {

          //println!("{}", i);
          break;
        }
      }
      Err(e) => {
        println!("error: {:?}", e);
        return None;
      },
    }
  }

  Some(v)
}

/*
#[bench]
fn small_test(b: &mut Bencher) {
  let data = include_bytes!("../../http-requests.txt");
  b.iter(||{
    parse(data)
  });
}

#[bench]
fn bigger_test(b: &mut Bencher) {
  let data = include_bytes!("../../bigger.txt");
  b.iter(||{
    parse(data)
  });
}
*/

fn one_test(c: &mut Criterion) {
  let data = &b"GET / HTTP/1.1
Host: www.reddit.com
User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10.8; rv:15.0) Gecko/20100101 Firefox/15.0.1
Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8
Accept-Language: en-us,en;q=0.5
Accept-Encoding: gzip, deflate
Connection: keep-alive

"[..];

  let mut http_group = c.benchmark_group("http");
  http_group.throughput(Throughput::Bytes(data.len() as u64));
  http_group.bench_with_input(
    BenchmarkId::new("parse", data.len()),
     data,
      |b, data| {
    b.iter(|| parse(data).unwrap());
  });

  http_group.finish();
}

/*
fn main() {
  let mut contents: Vec<u8> = Vec::new();

  {
    use std::io::Read;

    let mut file = File::open(env::args().nth(1).expect("File to read")).expect("Failed to open file");

    let _ = file.read_to_end(&mut contents).unwrap();
  }

  let buf = &contents[..];
  loop {
    parse(buf);
  }
}
*/

criterion_group!(http, one_test);
criterion_main!(http);
