#[macro_use]
extern crate nom;

use nom::{HexDisplay,IResult,FlatMap,FlatMapOpt,Functor,Producer,ProducerState,FileProducer,be_u16,be_u32,be_u64,be_f32,be_f64};
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
        return Incomplete(1234)
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
enum MP4Box<'a> {
  Ftyp(FileType<'a>),
  Moov(Vec<MoovBox>),
  Mdat,
  Free,
  Skip,
  Wide,
  Unknown
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
tag!(ftyp    "ftyp".as_bytes());

fn brand_name(input:&[u8]) -> IResult<&[u8],&str> {
  take!(major_brand_bytes 4);
  major_brand_bytes(input).map_res(str::from_utf8)
}
take!(major_brand_version 4);
many0!(compatible_brands<&[u8], &str> brand_name);

fn filetype_parser<'a>(input: &'a[u8]) -> IResult<&'a [u8], FileType<'a> > {
  chaining_parser!(input,
    m: brand_name          ~
    v: major_brand_version ~
    c: compatible_brands   ,
    ||{FileType{major_brand: m, major_brand_version:v, compatible_brands: c}})
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

fn filetype_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  ftyp(input).map(|_| MP4BoxType::Ftyp)
}

tag!(moov_tag "moov".as_bytes());

tag!(mdra    "mdra".as_bytes());
fn moov_mdra(input:&[u8]) -> IResult<&[u8], MoovBox> {
  mdra(input).map(|_| MoovBox::Mdra)
}
fn moov_mdra_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  mdra(input).map(|_| MP4BoxType::Mdra)
}

tag!(dref    "dref".as_bytes());
fn moov_dref(input:&[u8]) -> IResult<&[u8], MoovBox> {
  dref(input).map(|_| MoovBox::Dref)
}
fn moov_dref_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  dref(input).map(|_| MP4BoxType::Dref)
}

tag!(cmov    "cmov".as_bytes());
fn moov_cmov(input:&[u8]) -> IResult<&[u8], MoovBox> {
  cmov(input).map(|_| MoovBox::Cmov)
}
fn moov_cmov_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  cmov(input).map(|_| MP4BoxType::Cmov)
}

tag!(rmra    "rmra".as_bytes());
fn moov_rmra(input:&[u8]) -> IResult<&[u8], MoovBox> {
  rmra(input).map(|_| MoovBox::Rmra)
}
fn moov_rmra_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  rmra(input).map(|_| MP4BoxType::Rmra)
}

tag!(iods    "iods".as_bytes());
fn moov_iods(input:&[u8]) -> IResult<&[u8], MoovBox> {
  iods(input).map(|_| MoovBox::Iods)
}
fn moov_iods_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  iods(input).map(|_| MP4BoxType::Iods)
}

fn mvhd_box(input:&[u8]) -> IResult<&[u8],MvhdBox> {
  if input.len() < 100 {
    Incomplete(0)
  } else if input.len() == 100 {
    mvhd32(input)
  } else if input.len() == 112 {
    mvhd64(input)
  } else {
    Error(0)
  }
}

tag!(mvhd    "mvhd".as_bytes());
chain!(moov_mvhd<&[u8],MoovBox>,
    mvhd              ~
    content: mvhd_box ,
    || { MoovBox::Mvhd(content) }
);
fn moov_mvhd_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  mvhd(input).map(|_| MP4BoxType::Mvhd)
}

tag!(clip    "clip".as_bytes());
fn moov_clip(input:&[u8]) -> IResult<&[u8], MoovBox> {
  clip(input).map(|_| MoovBox::Clip)
}
fn moov_clip_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  clip(input).map(|_| MP4BoxType::Clip)
}

tag!(trak    "trak".as_bytes());
fn moov_trak(input:&[u8]) -> IResult<&[u8], MoovBox> {
  trak(input).map(|_| MoovBox::Trak)
}
fn moov_trak_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  trak(input).map(|_| MP4BoxType::Trak)
}

tag!(udta   "udta".as_bytes());
fn moov_udta(input:&[u8]) -> IResult<&[u8], MoovBox> {
  udta(input).map(|_| MoovBox::Udta)
}
fn moov_udta_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  udta(input).map(|_| MP4BoxType::Udta)
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
fn moov_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  moov_tag(input).map(|_| MP4BoxType::Moov)
}

tag!(mdat    "mdat".as_bytes());
fn mdat_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  mdat(input).map(|_| MP4Box::Mdat)
}
fn mdat_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  mdat(input).map(|_| MP4BoxType::Mdat)
}
tag!(free    "free".as_bytes());
fn free_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  free(input).map(|_| MP4Box::Free)
}
fn free_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  free(input).map(|_| MP4BoxType::Free)
}

tag!(skip    "skip".as_bytes());
fn skip_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  skip(input).map(|_| MP4Box::Skip)
}
fn skip_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  skip(input).map(|_| MP4BoxType::Skip)
}

tag!(wide    "wide".as_bytes());
fn wide_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  wide(input).map(|_| MP4Box::Wide)
}
fn wide_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  wide(input).map(|_| MP4BoxType::Wide)
}

fn unknown_box(input:&[u8]) -> IResult<&[u8], MP4Box> {
  println!("calling UNKNOWN");
  Done(input, MP4Box::Unknown)
}
fn unknown_box_type(input:&[u8]) -> IResult<&[u8], MP4BoxType> {
  Done(input, MP4BoxType::Unknown)
}

alt!(box_parser_internal<&[u8], MP4Box>, filetype_box | moov_box | mdat_box | free_box | skip_box | wide_box | unknown_box);
fn box_parser(input:&[u8]) -> IResult<&[u8], MP4Box> {
  mp4_box(input).flat_map(box_parser_internal)
}

fn data_interpreter(bytes:&[u8]) -> IResult<&[u8], ()> {
  //println!("bytes:\n{}", bytes.to_hex(8));
  //println!("bytes length: {}", bytes.len());
  match box_parser(bytes) {
    Done(i, o) => {
      match o {
        MP4Box::Ftyp(f) => println!("-> FTYP: {:?}", f),
        MP4Box::Moov(m) => {println!("-> MOOV: {:?}", m); /*println!("remaining:\n{}", i.to_hex(8))*/},
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
      assert!(false);
      Error(a)
    },
    Incomplete(a) => {
      println!("mp4 incomplete: {:?}", a);
      Incomplete(a)
    }
  }
}

many0!(full_data_interpreter<&[u8],()> data_interpreter);

fn parse_mp4_file(filename: &str) {
  FileProducer::new(filename, 400000).map(|producer: FileProducer| {
    println!("file producer created for {}", filename);
    let mut p = producer;
    pusher!(ps, full_data_interpreter);
    ps(&mut p);

    //assert!(false);
  });

}

enum MP4State {
  Main,
  Moov,
  Mvhd
}

pub struct MP4Consumer {
  counter:    usize,
  state:      MP4State,
  moov_bytes: usize
}

impl MP4Consumer {
  fn new() -> MP4Consumer {
    MP4Consumer { counter: 0, state: MP4State::Main, moov_bytes: 0 }
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
    self.counter = self.counter + input.len();
    //println!("counter: {}", self.counter);
    println!("size: {}", input.len());
    //println!("idx:{}\nbytes: {}", idx, (&input[idx..]).to_hex(8));
    match self.state {
      MP4State::Main => {
        //println!("\nparsing box header:\n{}", input.to_hex(8));
        println!("\nparsing box header");
        match box_header(input) {
          Done(i, header) => {
            println!("length: {} bytes (0x{:08x})", header.length, header.length);
            match header.tag {
              MP4BoxType::Ftyp    => println!("-> FTYP"),
              MP4BoxType::Moov    => {
                println!("-> MOOV");
                //println!("remaining:\n{}", i.to_hex(8));

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
            //return ConsumerState::Await(SeekFrom::Current(0), input.len() - idx);
            return ConsumerState::Await(0, input.len() + 100);
          }
        }
      },
      MP4State::Moov => {
        //println!("\nparsing moov box(remaining {} bytes):\n{}", self.moov_bytes, input.to_hex(8));
        println!("\nparsing moov box: remaining {} bytes:", self.moov_bytes);
        if self.moov_bytes < 0 {
          println!("negative remaining moov bytes, the count is wrong");
          return ConsumerState::ConsumerError(0);
        }
        if self.moov_bytes == 0 {
          println!("finished parsing moov atom, continuing with main parser");
          self.state = MP4State::Main;
          return ConsumerState::Await(0, input.len());
        }
        match moov_header(input) {
          Done(i, header) => {
            println!("length: {} bytes (0x{:08x})", header.length, header.length);
            match header.tag {
              MP4BoxType::Wide    => println!("-> WIDE"),
              MP4BoxType::Mdra    => println!("-> MDRA"),
              MP4BoxType::Dref    => println!("-> DREF"),
              MP4BoxType::Cmov    => println!("-> CMOV"),
              MP4BoxType::Rmra    => println!("-> RMRA"),
              MP4BoxType::Iods    => println!("-> IODS"),
              MP4BoxType::Mvhd    => {
                println!("-> MVHD");
                self.state = MP4State::Mvhd;
                self.moov_bytes = self.moov_bytes - (input.len() - i.len());
                // FIXME why -8 ?
                return ConsumerState::Await(input.len() - i.len(), header.length as usize - 8);
              },
              MP4BoxType::Clip    => println!("-> CLIP"),
              MP4BoxType::Trak    => println!("-> TRAK"),
              MP4BoxType::Udta    => println!("-> UDTA"),
              MP4BoxType::Unknown => println!("-> MOOV UNKNOWN"),
              _                   => { println!("invalid header here: {:?}", header.tag); return ConsumerState::ConsumerError(0)}
            }
            //self.moov_bytes = self.moov_bytes - (header.length as usize - i.len() as usize);
            self.moov_bytes = self.moov_bytes - header.length as usize;
            println!("after removing {} bytes, I now have {} moov bytes remaining", header.length as usize,
            self.moov_bytes);
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
        println!("parsing mvhd box(remaining moov bytes:{})", self.moov_bytes);
        match mvhd_box(input) {
          Error(a) => {
            println!("mvhd parsing error: {:?}", a);
            assert!(false);
            return ConsumerState::ConsumerError(a);
          },
          Incomplete(a) => {
            println!("mvhd incomplete -> await: {}", input.len());
            return ConsumerState::Await(0, input.len() + 100);
            //return ConsumerState::Await(input.len() - idx);
          },
          Done(i, movie_header) => {
            println!("correctly parsed movie header: {:?}", movie_header);
            self.state = MP4State::Moov;
            self.moov_bytes = self.moov_bytes - (input.len() - i.len());
            return ConsumerState::Await(input.len() - i.len(), 100);
          }
        }
      }
    }
  }

  fn end(&mut self) {
    println!("finish!");
    println!("counter: {}", self.counter);
  }
}

fn explore_mp4_file(filename: &str) {
  FileProducer::new(filename, 400).map(|producer: FileProducer| {
    println!("file producer created for {}", filename);
    let mut p = producer;
    let mut c = MP4Consumer{counter: 0, state: MP4State::Main, moov_bytes: 0};
    c.run(&mut p);

    //assert!(false);
  });
}

/*
#[test]
fn file_test() {
  //parse_mp4_file("./small.mp4");
  explore_mp4_file("./small.mp4");
}


#[test]
fn bunny_test() {
  //parse_mp4_file("bigbuckbunny.mp4");
  explore_mp4_file("bigbuckbunny.mp4");
}
*/


