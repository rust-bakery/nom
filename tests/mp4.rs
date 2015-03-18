#[macro_use]
extern crate nom;

use nom::{HexDisplay,Needed,IResult,FlatMapOpt,Functor,FileProducer,be_u16,be_u32,be_u64,be_f32};
use nom::{Consumer,ConsumerState};
use nom::IResult::*;

use std::str;
use std::io::SeekFrom;

fn mp4_box(input:&[u8]) -> IResult<&[u8], &[u8]> {
  match be_u32(input) {
    Done(i, offset) => {
      let sz: usize = offset as usize;
      if i.len() >= sz - 4 {
        return Done(&i[(sz-4)..], &i[0..(sz-4)])
      } else {
        return Incomplete(Needed::Size(4 + offset as u32))
      }
    }
    Error(e)      => Error(e),
    Incomplete(e) => Incomplete(e)
  }
}

#[derive(PartialEq,Eq,Debug)]
struct FileType<'a> {
  major_brand:         &'a str,
  major_brand_version: &'a [u8],
  compatible_brands:   Vec<&'a str>
}

#[allow(non_snake_case)]
#[derive(Debug)]
pub struct Mvhd32 {
  version_flags: u32, // actually:
  // version: u8,
  // flags: u24       // 3 bytes
  created_date:  u32,
  modified_date: u32,
  scale:         u32,
  duration:      u32,
  speed:         f32,
  volume:        u16, // actually a 2 bytes decimal
  /* 10 bytes reserved */
  scaleA:        f32,
  rotateB:       f32,
  angleU:        f32,
  rotateC:       f32,
  scaleD:        f32,
  angleV:        f32,
  positionX:     f32,
  positionY:     f32,
  scaleW:        f32,
  preview:       u64,
  poster:        u32,
  selection:     u64,
  current_time:  u32,
  track_id:      u32
}

#[allow(non_snake_case)]
#[derive(Debug)]
pub struct Mvhd64 {
  version_flags: u32, // actually:
  // version: u8,
  // flags: u24       // 3 bytes
  created_date:  u64,
  modified_date: u64,
  scale:         u32,
  duration:      u64,
  speed:         f32,
  volume:        u16, // actually a 2 bytes decimal
  /* 10 bytes reserved */
  scaleA:        f32,
  rotateB:       f32,
  angleU:        f32,
  rotateC:       f32,
  scaleD:        f32,
  angleV:        f32,
  positionX:     f32,
  positionY:     f32,
  scaleW:        f32,
  preview:       u64,
  poster:        u32,
  selection:     u64,
  current_time:  u32,
  track_id:      u32
}
take!(ten_bytes 10);

#[allow(non_snake_case)]
chain!(mvhd32 <&[u8], MvhdBox>,
  version_flags: be_u32 ~
  created_date:  be_u32 ~
  modified_date: be_u32 ~
  scale:         be_u32 ~
  duration:      be_u32 ~
  speed:         be_f32 ~
  volume:        be_u16 ~ // actually a 2 bytes decimal
              ten_bytes ~
  scaleA:        be_f32 ~
  rotateB:       be_f32 ~
  angleU:        be_f32 ~
  rotateC:       be_f32 ~
  scaleD:        be_f32 ~
  angleV:        be_f32 ~
  positionX:     be_f32 ~
  positionY:     be_f32 ~
  scaleW:        be_f32 ~
  preview:       be_u64 ~
  poster:        be_u32 ~
  selection:     be_u64 ~
  current_time:  be_u32 ~
  track_id:      be_u32,
  ||{
    MvhdBox::M32(Mvhd32 {
      version_flags: version_flags,
      created_date:  created_date,
      modified_date: modified_date,
      scale:         scale,
      duration:      duration,
      speed:         speed,
      volume:        volume,
      scaleA:        scaleA,
      rotateB:       rotateB,
      angleU:        angleU,
      rotateC:       rotateC,
      scaleD:        scaleD,
      angleV:        angleV,
      positionX:     positionX,
      positionY:     positionY,
      scaleW:        scaleW,
      preview:       preview,
      poster:        poster,
      selection:     selection,
      current_time:  current_time,
      track_id:      track_id
    })
  }
);

#[allow(non_snake_case)]
chain!(mvhd64 <&[u8], MvhdBox>,
  version_flags: be_u32 ~
  created_date:  be_u64 ~
  modified_date: be_u64 ~
  scale:         be_u32 ~
  duration:      be_u64 ~
  speed:         be_f32 ~
  volume:        be_u16 ~ // actually a 2 bytes decimal
              ten_bytes ~
  scaleA:        be_f32 ~
  rotateB:       be_f32 ~
  angleU:        be_f32 ~
  rotateC:       be_f32 ~
  scaleD:        be_f32 ~
  angleV:        be_f32 ~
  positionX:     be_f32 ~
  positionY:     be_f32 ~
  scaleW:        be_f32 ~
  preview:       be_u64 ~
  poster:        be_u32 ~
  selection:     be_u64 ~
  current_time:  be_u32 ~
  track_id:      be_u32,
  ||{
    MvhdBox::M64(Mvhd64 {
      version_flags: version_flags,
      created_date:  created_date,
      modified_date: modified_date,
      scale:         scale,
      duration:      duration,
      speed:         speed,
      volume:        volume,
      scaleA:        scaleA,
      rotateB:       rotateB,
      angleU:        angleU,
      rotateC:       rotateC,
      scaleD:        scaleD,
      angleV:        angleV,
      positionX:     positionX,
      positionY:     positionY,
      scaleW:        scaleW,
      preview:       preview,
      poster:        poster,
      selection:     selection,
      current_time:  current_time,
      track_id:      track_id
    })
  }
);

#[derive(Debug)]
pub enum MvhdBox {
  M32(Mvhd32),
  M64(Mvhd64)
}

#[derive(Debug)]
pub enum MoovBox {
  Mdra,
  Dref,
  Cmov,
  Rmra,
  Iods,
  Mvhd(MvhdBox),
  Clip,
  Trak,
  Udta
}

#[derive(Debug)]
enum MP4BoxType {
  Ftyp,
  Moov,
  Mdat,
  Free,
  Skip,
  Wide,
  Mdra,
  Dref,
  Cmov,
  Rmra,
  Iods,
  Mvhd,
  Clip,
  Trak,
  Udta,
  Unknown
}

#[derive(Debug)]
struct MP4BoxHeader {
  length: u32,
  tag:    MP4BoxType
}

take!(offset 4);
tag!(ftyp    "ftyp");

fn brand_name(input:&[u8]) -> IResult<&[u8],&str> {
  take!(major_brand_bytes 4);
  major_brand_bytes(input).map_res(str::from_utf8)
}
take!(major_brand_version 4);
named!(compatible_brands<&[u8], Vec<&str> >, many0!(brand_name));

fn filetype_parser<'a>(input: &'a[u8]) -> IResult<&'a [u8], FileType<'a> > {
  chaining_parser!(input,
    m: brand_name          ~
    v: take!(4)            ~
    c: compatible_brands   ,
    ||{FileType{major_brand: m, major_brand_version:v, compatible_brands: c}})
}

fn filetype_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  ftyp(input).map(|_| MP4BoxType::Ftyp)
}

tag!(moov_tag "moov");

tag!(mdra    "mdra");
fn moov_mdra_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  mdra(input).map(|_| MP4BoxType::Mdra)
}

tag!(dref    "dref");
fn moov_dref_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  dref(input).map(|_| MP4BoxType::Dref)
}

tag!(cmov    "cmov");
fn moov_cmov_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  cmov(input).map(|_| MP4BoxType::Cmov)
}

tag!(rmra    "rmra");
fn moov_rmra_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  rmra(input).map(|_| MP4BoxType::Rmra)
}

tag!(iods    "iods");
fn moov_iods_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  iods(input).map(|_| MP4BoxType::Iods)
}

fn mvhd_box(input:&[u8]) -> IResult<&[u8],MvhdBox> {
  if input.len() < 100 {
    Incomplete(Needed::Size(100))
  } else if input.len() == 100 {
    mvhd32(input)
  } else if input.len() == 112 {
    mvhd64(input)
  } else {
    Error(0)
  }
}

tag!(mvhd    "mvhd");
fn moov_mvhd_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  mvhd(input).map(|_| MP4BoxType::Mvhd)
}

tag!(clip    "clip");
fn moov_clip_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  clip(input).map(|_| MP4BoxType::Clip)
}

tag!(trak    "trak");
fn moov_trak_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  trak(input).map(|_| MP4BoxType::Trak)
}

tag!(udta   "udta");
fn moov_udta_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  udta(input).map(|_| MP4BoxType::Udta)
}

fn moov_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  moov_tag(input).map(|_| MP4BoxType::Moov)
}

tag!(mdat    "mdat");
fn mdat_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  mdat(input).map(|_| MP4BoxType::Mdat)
}
tag!(free    "free");
fn free_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  free(input).map(|_| MP4BoxType::Free)
}

tag!(skip    "skip");
fn skip_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  skip(input).map(|_| MP4BoxType::Skip)
}

tag!(wide    "wide");
fn wide_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  wide(input).map(|_| MP4BoxType::Wide)
}

fn unknown_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  Done(input, MP4BoxType::Unknown)
}

enum MP4State {
  Main,
  Moov,
  Mvhd
}

pub struct MP4Consumer {
  state:      MP4State,
  moov_bytes: usize
}

impl MP4Consumer {
  fn new() -> MP4Consumer {
    MP4Consumer { state: MP4State::Main, moov_bytes: 0 }
  }
}

alt!(box_type<&[u8], MP4BoxType>, filetype_box_type | moov_box_type | mdat_box_type | free_box_type | skip_box_type
     | wide_box_type | unknown_box_type);

alt!(moov_type<&[u8], MP4BoxType>, moov_mdra_type | moov_dref_type | moov_cmov_type | moov_rmra_type | moov_iods_type |
     moov_mvhd_type | moov_clip_type | moov_trak_type | moov_udta_type);

chain!(box_header<&[u8],MP4BoxHeader>,
    length: be_u32 ~
    tag: box_type  ,
    || { MP4BoxHeader{ length: length, tag: tag} }
);

chain!(moov_header<&[u8],MP4BoxHeader>,
    length: be_u32 ~
    tag: moov_type  ,
    || { MP4BoxHeader{ length: length, tag: tag} }
);

impl Consumer for MP4Consumer {
  fn consume(&mut self, input: &[u8]) -> ConsumerState {
    match self.state {
      MP4State::Main => {
        //println!("\nparsing box header:\n{}", input.to_hex(8));
        match box_header(input) {
          Done(i, header) => {
            match header.tag {
              MP4BoxType::Ftyp    => {
                println!("-> FTYP");
                match filetype_parser(&i[0..(header.length as usize - 8)]) {
                  Done(i2, filetype_header) => {
                    println!("filetype header: {:?}", filetype_header);
                    return ConsumerState::Await(header.length as usize, header.length as usize - 8);
                  }
                  Error(a) => {
                    println!("ftyp parsing error: {:?}", a);
                    assert!(false);
                    return ConsumerState::ConsumerError(a);
                  },
                  Incomplete(a) => {
                    println!("ftyp incomplete -> await: {}", input.len());
                    return ConsumerState::Await(0, input.len() + 100);
                  }
                }
              },
              MP4BoxType::Moov    => {
                println!("-> MOOV");
                self.state = MP4State::Moov;
                self.moov_bytes = header.length as usize - 8;
                return ConsumerState::Await(input.len() - i.len(), header.length as usize);
              },
              MP4BoxType::Mdat    => println!("-> MDAT"),
              MP4BoxType::Free    => println!("-> FREE"),
              MP4BoxType::Skip    => println!("-> SKIP"),
              MP4BoxType::Wide    => println!("-> WIDE"),
              MP4BoxType::Unknown => {
                println!("-> UNKNOWN");
                println!("bytes:\n{}", (input).to_hex(8));
              },
              _                   => { println!("invalid"); return ConsumerState::ConsumerError(0)}
            }
            // current producer position is at input.len()
            // I consumed input.len() - i.len() = 8
            // I want to advance from header.length()
            // offset to my new position: -input.len() + (input.len() - i.len()) + header.len() == header.len() - i.len()
            return ConsumerState::Seek(input.len() - i.len(), SeekFrom::Current((header.length as usize - i.len() as usize - 8) as i64), 100);
          },
          Error(a) => {
            println!("mp4 parsing error: {:?}", a);
            assert!(false);
            return ConsumerState::ConsumerError(a);
          },
          Incomplete(a) => {
            // FIXME: incomplete should send the required size
            println!("mp4 incomplete -> await: {}", input.len());
            return ConsumerState::Await(0, input.len() + 100);
          }
        }
      },
      MP4State::Moov => {
        //println!("\nparsing moov box(remaining {} bytes):\n{}", self.moov_bytes, input.to_hex(8));
        if self.moov_bytes == 0 {
          //println!("finished parsing moov atom, continuing with main parser");
          self.state = MP4State::Main;
          return ConsumerState::Await(0, input.len());
        }
        match moov_header(input) {
          Done(i, header) => {
            match header.tag {
              MP4BoxType::Mvhd    => {
                println!("-> MVHD");
                self.state = MP4State::Mvhd;
                // TODO: check for overflow here
                self.moov_bytes = self.moov_bytes - (input.len() - i.len());
                return ConsumerState::Await(input.len() - i.len(), header.length as usize - 8);
              },
              MP4BoxType::Wide    => println!("-> WIDE"),
              MP4BoxType::Mdra    => println!("-> MDRA"),
              MP4BoxType::Dref    => println!("-> DREF"),
              MP4BoxType::Cmov    => println!("-> CMOV"),
              MP4BoxType::Rmra    => println!("-> RMRA"),
              MP4BoxType::Iods    => println!("-> IODS"),
              MP4BoxType::Clip    => println!("-> CLIP"),
              MP4BoxType::Trak    => println!("-> TRAK"),
              MP4BoxType::Udta    => println!("-> UDTA"),
              MP4BoxType::Unknown => println!("-> MOOV UNKNOWN"),
              _                   => { println!("invalid header here: {:?}", header.tag); return ConsumerState::ConsumerError(0)}
            }
            // TODO: check for overflow here
            self.moov_bytes = self.moov_bytes - header.length as usize;
            return ConsumerState::Seek(input.len() - i.len(), SeekFrom::Current((header.length as usize - i.len() as usize - 8) as i64), 100);
          },
          Error(a) => {
            println!("moov parsing error: {:?}", a);
            assert!(false);
            return ConsumerState::ConsumerError(a);
          },
          Incomplete(a) => {
            println!("moov incomplete -> await: {}", input.len());
            return ConsumerState::Await(0, input.len() + 100);
          }
        }
      },
      MP4State::Mvhd => {
        //println!("parsing mvhd box(remaining moov bytes:{}):\n{}", self.moov_bytes, input.to_hex(8));
        match mvhd_box(input) {
          Done(i, movie_header) => {
            println!("correctly parsed movie header: {:?}", movie_header);
            self.state = MP4State::Moov;
            //TODO: check for overflow here
            self.moov_bytes = self.moov_bytes - (input.len() - i.len());
            return ConsumerState::Await(input.len() - i.len(), 100);
          },
          Error(a) => {
            println!("mvhd parsing error: {:?}", a);
            assert!(false);
            return ConsumerState::ConsumerError(a);
          },
          Incomplete(a) => {
            println!("mvhd incomplete -> await: {}", input.len());
            return ConsumerState::Await(0, input.len() + 100);
          }
        }
      }
    }
  }

  fn end(&mut self) {
    println!("finish!");
  }
}

fn explore_mp4_file(filename: &str) {
  FileProducer::new(filename, 400).map(|producer: FileProducer| {
    println!("file producer created for {}", filename);
    let mut p = producer;
    let mut c = MP4Consumer{state: MP4State::Main, moov_bytes: 0};
    c.run(&mut p);

    //assert!(false);
  });
}

/*
#[test]
fn file_test() {
  explore_mp4_file("./small.mp4");
}


#[test]
fn bunny_test() {
  //explore_mp4_file("bigbuckbunny.mp4");
}
*/


