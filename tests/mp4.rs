#[macro_use]
extern crate nom;

use nom::{IResult,FlatMapper,Mapper,Mapper2,Producer,ProducerState,FileProducer,HexDisplay};
use nom::IResult::*;

use std::str;
use std::collections::HashMap;


fn mp4_box(input:&[u8]) -> IResult<&[u8], &[u8]> {

  take!(offset_parser 4);
  match offset_parser(input) {
    Done(i, offset_bytes) => {
      let offset:u32 = (offset_bytes[3] as u32) + (offset_bytes[2] as u32) * 0x100 + (offset_bytes[1] as u32) * 0x10000 + (offset_bytes[0] as u32) * 0x1000000;
      let sz: usize = offset as usize;
      //println!("box size: {} -> {}", offset_bytes.to_hex(8), sz);
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
pub enum MoovBox {
  Mdra,
  Dref,
  Cmov,
  Rmra,
  Iods,
  Mvhd,
  Clip,
  Trak,
  Udta
}

#[derive(PartialEq,Eq,Debug)]
enum MP4Box<'a> {
  Ftyp(FileType<'a>),
  Moov(Vec<MoovBox>),
  Mdat,
  Free,
  Skip,
  Wide,
  Unknown
}

take!(offset 4);
tag!(ftyp    "ftyp".as_bytes());

fn brand_name(input:&[u8]) -> IResult<&[u8],&str> {
  take!(major_brand_bytes 4);
  major_brand_bytes(input).map_res(str::from_utf8)
}
take!(major_brand_version 4);
many0!(compatible_brands<&[u8], &str> brand_name);

fn filetype_parser<'a>(input: &'a[u8]) -> IResult<&'a [u8], FileType<'a> > {
  chaining_parser!(input, ||{FileType{major_brand: m, major_brand_version:v, compatible_brands: c}},
    m: brand_name,
    v: major_brand_version,
    c: compatible_brands,)
}

o!(filetype <&[u8], FileType>  ftyp ~ [ filetype_parser ]);

fn filetype_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  match filetype(input) {
    Error(a)      => Error(a),
    Incomplete(a) => Incomplete(a),
    Done(i, o)    => {
      Done(i, MP4Box::Ftyp(o))
    }
  }
}

tag!(moov_tag "moov".as_bytes());

tag!(mdra    "mdra".as_bytes());
fn moov_mdra(input:&[u8]) -> IResult<&[u8], MoovBox> {
  mdra(input).map(|o| MoovBox::Mdra)
}

tag!(dref    "dref".as_bytes());
fn moov_dref(input:&[u8]) -> IResult<&[u8], MoovBox> {
  dref(input).map(|o| MoovBox::Dref)
}

tag!(cmov    "cmov".as_bytes());
fn moov_cmov(input:&[u8]) -> IResult<&[u8], MoovBox> {
  cmov(input).map(|o| MoovBox::Cmov)
}

tag!(rmra    "rmra".as_bytes());
fn moov_rmra(input:&[u8]) -> IResult<&[u8], MoovBox> {
  rmra(input).map(|o| MoovBox::Rmra)
}

tag!(iods    "iods".as_bytes());
fn moov_iods(input:&[u8]) -> IResult<&[u8], MoovBox> {
  iods(input).map(|o| MoovBox::Iods)
}

tag!(mvhd    "mvhd".as_bytes());
fn moov_mvhd(input:&[u8]) -> IResult<&[u8], MoovBox> {
  mvhd(input).map(|o| MoovBox::Mvhd)
}

tag!(clip    "clip".as_bytes());
fn moov_clip(input:&[u8]) -> IResult<&[u8], MoovBox> {
  clip(input).map(|o| MoovBox::Clip)
}

tag!(trak    "trak".as_bytes());
fn moov_trak(input:&[u8]) -> IResult<&[u8], MoovBox> {
  trak(input).map(|o| MoovBox::Trak)
}

tag!(udta   "udta".as_bytes());
fn moov_udta(input:&[u8]) -> IResult<&[u8], MoovBox> {
  udta(input).map(|o| MoovBox::Udta)
}

alt!(moov_internal<&[u8], MoovBox>, moov_mdra | moov_dref | moov_cmov |
     moov_rmra | moov_iods | moov_mvhd | moov_clip | moov_trak | moov_udta);


fn moov(input:&[u8]) -> IResult<&[u8], MoovBox> {
  match mp4_box(input) {
    Error(a)      => Error(a),
    Incomplete(a) => Incomplete(a),
    Done(i, o)    => {
      match moov_internal(o) {
        Error(a)      => Error(a),
        Incomplete(a) => Incomplete(a),
        Done(i2, o2)  => {
          Done(i, o2)
        }

      }
    }
  }
}

many0!(moov_many<&[u8],MoovBox> moov);

o!(moov_box_internal <&[u8], Vec<MoovBox> >  moov_tag ~ [ moov_many ]);
fn moov_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  match moov_box_internal(input) {
    Error(a)      => Error(a),
    Incomplete(a) => Incomplete(a),
    Done(i, o)  => {
      Done(i, MP4Box::Moov(o))
    }
  }
}

tag!(mdat    "mdat".as_bytes());
fn mdat_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  match mdat(input) {
    Error(a)      => Error(a),
    Incomplete(a) => Incomplete(a),
    Done(i, _)    => {
      Done(i, MP4Box::Mdat)
    }
  }
}
tag!(free    "free".as_bytes());
fn free_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  match free(input) {
    Error(a)      => Error(a),
    Incomplete(a) => Incomplete(a),
    Done(i, _)    => {
      Done(i, MP4Box::Free)
    }
  }
}

tag!(skip    "skip".as_bytes());
fn skip_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  match free(input) {
    Error(a)      => Error(a),
    Incomplete(a) => Incomplete(a),
    Done(i, _)    => {
      Done(i, MP4Box::Skip)
    }
  }
}

tag!(wide    "wide".as_bytes());
fn wide_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  match free(input) {
    Error(a)      => Error(a),
    Incomplete(a) => Incomplete(a),
    Done(i, _)    => {
      Done(i, MP4Box::Wide)
    }
  }
}

fn unknown_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  println!("calling UNKNOWN");
  Done(input, MP4Box::Unknown)
}

alt!(box_parser_internal<&[u8], MP4Box>, filetype_box | moov_box | mdat_box | free_box | skip_box | wide_box | unknown_box);
fn box_parser(input:&[u8]) -> IResult<&[u8], MP4Box> {
  match mp4_box(input) {
    Error(a)      => Error(a),
    Incomplete(a) => Incomplete(a),
    Done(i, o)    => {
      match box_parser_internal(o) {
        Error(a)      => Error(a),
        Incomplete(a) => Incomplete(a),
        Done(i2, o2)  => {
          Done(i, o2)
        }
      }
    }
  }
}


fn data_interpreter(bytes:&[u8]) -> IResult<&[u8], ()> {
  //println!("bytes:\n{}", bytes.to_hex(8));
  match box_parser(bytes) {
    Done(i, o) => {
      match o {
        MP4Box::Ftyp(f) => println!("-> FTYP: {:?}", f),
        MP4Box::Moov(m) => {println!("-> MOOV: {:?}", m); println!("remaining:\n{}", i.to_hex(8))},
        MP4Box::Mdat    => println!("-> MDAT"),
        MP4Box::Free    => println!("-> FREE"),
        MP4Box::Skip    => println!("-> SKIP"),
        MP4Box::Wide    => println!("-> WIDE"),
        MP4Box::Unknown => println!("-> UNKNOWN")
      }
      //println!("remaining:\n{}", i.to_hex(8));
      Done(i,())
    },
    Error(a) => {
      println!("mp4 parsing error: {:?}", a);
      Error(a)
    },
    Incomplete(a) => {
      //println!("incomplete: {:?}", a);
      Incomplete(a)
    }
  }
}

fn multiple_data_interpreter(bytes:&[u8]) -> IResult<&[u8], ()> {
  match data_interpreter(bytes) {
    Error(a)      => Error(a),
    Incomplete(a) => Incomplete(a),
    Done(i, ())   => {
      println!("NEXT BOX");
      match data_interpreter(i) {
        Error(a)      => Error(a),
        Incomplete(a) => Incomplete(a),
        Done(i2,())   => {
          println!("NEXT BOX 2");
          match data_interpreter(i2) {
            Error(a)      => Error(a),
            Incomplete(a) => Incomplete(a),
            Done(i3,())   => {
              println!("NEXT BOX 3");
              match data_interpreter(i3) {
                Error(a)      => Error(a),
                Incomplete(a) => Incomplete(a),
                Done(i4,())   => {
                  println!("NEXT BOX 4");
                  let res = data_interpreter(i4);
                  println!("res4: {:?}", res);
                  res
                }
              }
            }
          }
        }
      }
    },
  }
}

fn parse_mp4_file(filename: &str) {
  FileProducer::new(filename, 40000).map(|producer: FileProducer| {
    let mut p = producer;
    match p.produce() {
      ProducerState::Data(bytes) => {
        multiple_data_interpreter(bytes);
      },
      _ => println!("got error")
    }
    /*
    pusher!(ps, data_interpreter);
    ps(&mut p);
    */
    //assert!(false);
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
