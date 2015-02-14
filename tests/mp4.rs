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
      let mut i = 0;
      for chunk in self.chunks(chunk_size) {
        let s = format!("{:08x}", i);
        let s2: &str = &s;
        for &ch in s.as_bytes().iter() {
          v.push(ch);
        }
        v.push('\t' as u8);

        i = i + chunk_size;

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

fn mp4_box(input:&[u8]) -> IResult<&[u8], &[u8]> {

  take!(offset_parser 4);
  match offset_parser(input) {
    Done(i, offset_bytes) => {
      let offset:u32 = (offset_bytes[3] as u32) + (offset_bytes[2] as u32) * 0x100 + (offset_bytes[1] as u32) * 0x10000 + (offset_bytes[0] as u32) * 0x1000000;
      let sz: usize = offset as usize;
      if i.len() >= sz {
        return Done(&i[(sz-4)..], &i[0..(sz-4)])
      } else {
        return Incomplete(0)
      }
    },
    e => e
  }
}

#[derive(PartialEq,Eq,Debug)]
struct FileType<'a> {
  major_brand:         &'a str,
  major_brand_version: &'a [u8],
  compatible_brands:   Vec<&'a str>
}

#[derive(PartialEq,Eq,Debug)]
enum MP4Box<'a> {
  Ftyp(FileType<'a>),
  Moov,
  Free
}

take!(offset 4);
tag!(ftyp    "ftyp".as_bytes());

fn brand_name(input:&[u8]) -> IResult<&[u8],&str> {
  take!(major_brand_bytes 4);
  major_brand_bytes(input).map_res(str::from_utf8)
}
take!(major_brand_version 4);
many0!(compatible_brands<&[u8],&str> brand_name);

fn filetype_parser<'a>(input: &'a[u8]) -> IResult<&'a [u8], FileType<'a> > {
  chaining_parser!(input, ||{FileType{major_brand: m, major_brand_version:v, compatible_brands: c}},
    m: brand_name,
    v: major_brand_version,
    c: compatible_brands,)
}

o!(filetype <&[u8], FileType>  ftyp ~ [ filetype_parser ]);

fn filetype_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  //FIXME: flat_map should work here
  //mp4_box(input).flat_map(filetype)
  match mp4_box(input) {
    Done(i, o) => {
      match filetype(o) {
        Done(i2, o2) => {
          Done(i, MP4Box::Ftyp(o2))
        },
        Error(a) => Error(a),
        Incomplete(a) => Incomplete(a)
      }
    },
    Error(a) => Error(a),
    Incomplete(a) => Incomplete(a)
  }
}

tag!(free    "ftyp".as_bytes());
fn free_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  match mp4_box(input) {
    Done(i, o) => {
      match free(o) {
        Done(i2, o2) => {
          Done(i, MP4Box::Free)
        },
        a => Error(0)
      }
    },
    a => Error(0)
  }
}

alt!(box_parser<&[u8], MP4Box>, filetype_box | free_box);

fn parse_mp4_file(filename: &str) {
  FileProducer::new(filename, 150).map(|producer: FileProducer| {
    let mut p = producer;
    match p.produce() {
      ProducerState::Data(bytes) => {
        println!("bytes:\n{}", bytes.to_hex(8));
        match box_parser(bytes) {
          Done(i, o) => {
            match o {
              MP4Box::Ftyp(f) => println!("parsed ftyp: {:?}", f),
              MP4Box::Moov    => println!("found moov box"),
              MP4Box::Free    => println!("found free box")
            }
            println!("remaining:\n{}", i.to_hex(8))
          },
          a => println!("error: {:?}", a)
        }
      },
      _ => println!("got error")
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
