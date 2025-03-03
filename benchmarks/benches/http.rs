#![cfg_attr(rustfmt, rustfmt_skip)]

#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use codspeed_criterion_compat::*;
use nom::{IResult, bytes::{tag, take_while1}, character:: char, multi::many, OutputMode, Parser, PResult, error::Error, Mode, sequence::{preceded, delimited, separated_pair, terminated, pair}, OutputM, Emit, Complete};

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
  c.is_ascii_digit() || c == b'.'
}

fn line_ending<'a>() -> impl Parser<&'a[u8], Output=&'a[u8], Error=Error<&'a[u8]>>  {
  tag("\n").or(tag("\r\n"))
}

fn request_line<'a>()-> impl Parser<&'a[u8], Output=Request<'a>, Error=Error<&'a[u8]>> {
  (take_while1(is_token),  preceded(take_while1(is_space), take_while1(is_not_space)), delimited(take_while1(is_space), http_version(), line_ending()))
  .map(|(method, uri, version)| Request {method, uri, version})
}

fn http_version<'a>() -> impl Parser<&'a[u8], Output=&'a[u8], Error=Error<&'a[u8]>> {

  preceded(tag("HTTP/"), take_while1(is_version))
}

fn message_header_value<'a>() -> impl Parser<&'a[u8], Output=&'a[u8], Error=Error<&'a[u8]>> {

  delimited(take_while1(is_horizontal_space),  take_while1(not_line_ending), line_ending())
}

fn message_header<'a>() ->  impl Parser<&'a[u8], Output=Header<'a>, Error=Error<&'a[u8]> >{
  separated_pair(take_while1(is_token), char(':'), many(1.., message_header_value()))
    .map(|(name, value)|Header{ name, value })
}

fn request<'a>() -> impl Parser<&'a[u8], Output=(Request<'a>, Vec<Header<'a>>), Error=Error<&'a[u8]> > {
  pair(request_line(), terminated(many(1.., message_header()), line_ending()))
}


fn parse(data: &[u8]) -> Option<Vec<(Request<'_>, Vec<Header<'_>>)>> {
  let mut buf = &data[..];
  let mut v = Vec::new();
  loop {
    match request().process::<OutputM<Emit, Emit, Complete>>(buf) {
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
