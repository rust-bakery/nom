
pub trait HexDisplay {
  fn offset(&self, second:&[u8]) -> usize;

  /// Converts the value of `self` to a hex value, returning the owned
  /// string.
  fn to_hex(&self, chunk_size: usize) -> String;

  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String;
}

static CHARS: &'static[u8] = b"0123456789abcdef";


impl HexDisplay for [u8] {
  fn offset(&self, second:&[u8]) -> usize {
    let fst = self.as_ptr();
    let snd = second.as_ptr();

    snd as usize - fst as usize
  }

  #[allow(unused_variables)]
  fn to_hex(&self, chunk_size: usize) -> String {
    self.to_hex_from(chunk_size, 0)
  }

  #[allow(unused_variables)]
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
    let mut v = Vec::with_capacity(self.len() * 3);
    let mut i = from;
    for chunk in self.chunks(chunk_size) {
      let s = format!("{:08x}", i);
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
        for j in 0..(chunk_size - chunk.len()) {
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

#[macro_export]
macro_rules! dbg (
  ($i: expr, $submac:ident!( $($args:tt)* )) => (
    {
      let l = line!();
      match $submac!($i, $($args)*) {
        IResult::Error(a) => {
          println!("Error({:?}) at l.{} by ' {} '", a, l, stringify!($submac!($($args)*)));
          IResult::Error(a)
        },
        IResult::Incomplete(a) => {
          println!("Incomplete({:?}) at {} by ' {} '", a, l, stringify!($submac!($($args)*)));
          IResult::Incomplete(a)
        },
        a => a
      }
    }
  );
);

#[macro_export]
macro_rules! dbg_dmp (
  ($i: expr, $submac:ident!( $($args:tt)* )) => (
    {
      let l = line!();
      match $submac!($i, $($args)*) {
        IResult::Error(a) => {
          println!("Error({:?}) at l.{} by ' {} '\n{}", a, l, stringify!($submac!($($args)*)), $i.to_hex(8));
          IResult::Error(a)
        },
        IResult::Incomplete(a) => {
          println!("Incomplete({:?}) at {} by ' {} '\n{}", a, l, stringify!($submac!($($args)*)), $i.to_hex(8));
          IResult::Incomplete(a)
        },
        a => a
      }
    }
  );
);

pub trait AsBytes {
  fn as_bytes(&self) -> &[u8];
}

impl<'a> AsBytes for &'a str {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    str::as_bytes(self)
  }
}

impl AsBytes for str {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    str::as_bytes(self)
  }
}

impl<'a> AsBytes for &'a [u8] {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    *self
  }
}

impl AsBytes for [u8] {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    self
  }
}
