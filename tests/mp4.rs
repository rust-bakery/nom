#[macro_use]
extern crate nom;

use nom::{IResult,FlatMapper,Mapper,Producer,ProducerState,FileProducer,HexDisplay};
use nom::IResult::*;

use std::str;
use std::collections::HashMap;


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

tag!(free    "free".as_bytes());
fn free_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  match mp4_box(input) {
    Done(i, o) => {
      match free(o) {
        Done(i2, o2) => {
          Done(i, MP4Box::Free)
        },
        Error(a) => Error(a),
        Incomplete(a) => Incomplete(a)
      }
    },
    Error(a) => Error(a),
    Incomplete(a) => Incomplete(a)
  }
}

alt!(box_parser<&[u8], MP4Box>, filetype_box | free_box);

fn data_interpreter(bytes:&[u8]) -> IResult<&[u8], ()> {
  println!("bytes:\n{}", bytes.to_hex(8));
  match box_parser(bytes) {
    Done(i, o) => {
      match o {
        MP4Box::Ftyp(f) => println!("parsed ftyp: {:?}", f),
        MP4Box::Moov    => println!("found moov box"),
        MP4Box::Free    => println!("found free box")
      }
      println!("remaining:\n{}", i.to_hex(8));
      Done(i,())
    },
    Error(a) => {
      println!("error: {:?}", a);
      Error(a)
    },
    Incomplete(a) => {
      println!("incomplete: {:?}", a);
      Incomplete(a)
    }
  }
}
fn parse_mp4_file(filename: &str) {
  FileProducer::new(filename, 150).map(|producer: FileProducer| {
    let mut p = producer;
    /*match p.produce() {
      ProducerState::Data(bytes) => {
      },
      _ => println!("got error")
    }*/
    pusher!(ps, data_interpreter);
    ps(&mut p);
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
