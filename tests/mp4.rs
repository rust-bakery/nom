#[macro_use]
extern crate nom;
//extern crate serialize;

use nom::{IResult,FlatMapper,Mapper,Producer,ProducerState,FileProducer};
use nom::IResult::*;

use std::str;
use std::collections::HashMap;
//use serialize::hex::ToHex;

pub trait HexDisplay {
      /// Converts the value of `self` to a hex value, returning the owned
      ///     /// string.
  fn to_hex(&self, chunk_size: usize) -> String;
}

static CHARS: &'static[u8] = b"0123456789abcdef";

impl HexDisplay for [u8] {
    fn to_hex(&self, chunk_size: usize) -> String {
      let mut v = Vec::with_capacity(self.len() * 3);
      for chunk in self.chunks(chunk_size) {
        for &byte in chunk {
          v.push(CHARS[(byte >> 4) as usize]);
          v.push(CHARS[(byte & 0xf) as usize]);
          v.push(' ' as u8);
        }
        if chunk_size > chunk.len() {
          for i in 0..(chunk_size - chunk.len()) {
            v.push(' ' as u8);
            v.push(' ' as u8);
            v.push(' ' as u8);
          }
        }
        v.push('\t' as u8);

        for &byte in chunk {
          if (byte >=32 && byte <= 126) || byte >= 128 {
            v.push(byte);
          } else {
            v.push('.' as u8);
          }
        }
        v.push('\n' as u8);
      }

      unsafe {
        String::from_utf8_unchecked(v)
      }
    }
}

#[derive(PartialEq,Eq,Debug)]
struct Brand<'a> {
  major:   &'a str,
  version: &'a [u8]
}
take!(offset 4);
tag!(ftyp    "ftyp".as_bytes());

fn major_brand(input:&[u8]) -> IResult<&[u8],&str> {
  take!(major_brand_bytes 4);
  major_brand_bytes(input).map_res(str::from_utf8)
}
take!(major_brand_version 4);

fn brand<'a>(input: &'a[u8]) -> IResult<&'a [u8], Brand<'a> > {
  chaining_parser!(input, ||{Brand{major: m, version:v}}, m: major_brand, v: major_brand_version,)
}

o!(begin <&[u8], Brand>  offset ~ ftyp ~ [ brand ]);


fn parse_mp4_file(filename: &str) {
  FileProducer::new(filename, 100).map(|producer: FileProducer| {
    let mut p = producer;
    match p.produce() {
      ProducerState::Data(bytes) => {
        println!("bytes:\n{}", bytes.to_hex(8));
        match begin(bytes) {
          Done(i, o) => {
            //println!("parsed: {:?}\n{}", o, i.to_hex(8))
            println!("parsed: {:?}\n", o)
          },
          a          => println!("error: {:?}", a)
        }
      },
      _                          => println!("got error")
    }
    /*//p.push(|par| {println!("parsed file: {}", par); par});
    //p.push(|par| par.flat_map(print));
    fn pr<'a,'b,'c>(data: &[u8]) -> IResult<'b,&[u8], &[u8]> {
      println!("bytes: {:?}", &data[0..20]);
      //Done("".as_bytes(), data).map_res(str::from_utf8);
      Done("".as_bytes(),"".as_bytes())
    }
    pusher!(ps, pr);
    ps(&mut p);
    */
    assert!(false);
  });

}
#[test]
fn file_test() {
  parse_mp4_file("small.mp4");
}
#[test]
fn bunny_test() {
  parse_mp4_file("bigbuckbunny.mp4");
}
