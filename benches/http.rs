#![feature(test)]
extern crate test;

#[macro_use]
extern crate nom;

use nom::IResult;
use std::env;
use std::fs::File;

#[derive(Debug)]
struct Request<'a> {
    method:  &'a [u8],
    uri:     &'a [u8],
    version: &'a [u8],
}

#[derive(Debug)]
struct Header<'a> {
    name:  &'a [u8],
    value: Vec<&'a [u8]>,
}

fn is_token(c: u8) -> bool {
    match c {
        128...255 => false,
        0...31    => false,
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

fn is_not_space(c: u8)        -> bool { c != b' ' }
fn is_horizontal_space(c: u8) -> bool { c == b' ' || c == b'\t' }

fn is_version(c: u8) -> bool {
    c >= b'0' && c <= b'9' || c == b'.'
}

named!(line_ending, alt!(tag!("\r\n") | tag!("\n")));

fn request_line<'a>(input: &'a [u8]) -> IResult<&'a[u8], Request<'a>> {
  do_parse!(input,
    method: take_while1!(is_token)     >>
            take_while1!(is_space)     >>
    url:    take_while1!(is_not_space) >>
            take_while1!(is_space)     >>
    version: http_version              >>
    line_ending                        >>

    (Request {
        method: method,
        uri:    url,
        version: version,
    }))
}

named!(http_version, do_parse!(
    tag!("HTTP/")                     >>
    version: take_while1!(is_version) >>

    (version)));

named!(message_header_value, do_parse!(
          take_while1!(is_horizontal_space) >>
    data: take_while1!(not_line_ending)     >>
    line_ending                             >>

    (data)));

fn message_header<'a>(input: &'a [u8]) -> IResult<&'a[u8], Header<'a>> {
  do_parse!(input,
    name:   take_while1!(is_token)       >>
            char!(':')                   >>
    values: many1!(message_header_value) >>

    (Header {
        name: name,
        value: values,
    }))
}

fn request<'a>(input: &'a [u8]) -> IResult<&'a[u8], (Request<'a>, Vec<Header<'a>>)> {
  do_parse!(input,
    req: request_line           >>
    h:   many1!(message_header) >>
         line_ending            >>

    (req, h))
}


fn parse(data:&[u8]) -> Option<Vec<(Request, Vec<Header>)>> {
  let mut buf = &data[..];
  let mut v = Vec::new();
  loop {
    match request(buf) {
      IResult::Done(b, r) => {
        buf = b;
        v.push(r);

        if b.is_empty() {

    //println!("{}", i);
          break;
        }
      },
      IResult::Error(_) => return None/*panic!("{:?}", e)*/,
      IResult::Incomplete(_) => return None/*panic!("Incomplete!")*/,
    }
  }

  Some(v)
}

use test::Bencher;

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

#[bench]
fn one_test(b: &mut Bencher) {
  let data = &b"GET / HTTP/1.1
Host: www.reddit.com
User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10.8; rv:15.0) Gecko/20100101 Firefox/15.0.1
Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8
Accept-Language: en-us,en;q=0.5
Accept-Encoding: gzip, deflate
Connection: keep-alive"[..];
  b.iter(||{
    parse(data)
  });
}

fn main() {
    let mut contents: Vec<u8> = Vec::new();

    {
        use std::io::Read;

        let mut file = File::open(env::args().nth(1).expect("File to read")).ok().expect("Failed to open file");

        let _ = file.read_to_end(&mut contents).unwrap();
    }
    
    let buf = &contents[..];
    loop { parse(buf); }
}

