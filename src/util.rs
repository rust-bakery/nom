#[cfg(feature = "alloc")]
use lib::std::vec::Vec;

#[cfg(feature = "std")]
pub trait HexDisplay {
  /// Converts the value of `self` to a hex dump, returning the owned
  /// string.
  fn to_hex(&self, chunk_size: usize) -> String;

  /// Converts the value of `self` to a hex dump beginning at `from` address, returning the owned
  /// string.
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String;
}

#[cfg(feature = "std")]
static CHARS: &'static [u8] = b"0123456789abcdef";

#[cfg(feature = "std")]
impl HexDisplay for [u8] {
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
      v.push(b'\t');

      i += chunk_size;

      for &byte in chunk {
        v.push(CHARS[(byte >> 4) as usize]);
        v.push(CHARS[(byte & 0xf) as usize]);
        v.push(b' ');
      }
      if chunk_size > chunk.len() {
        for j in 0..(chunk_size - chunk.len()) {
          v.push(b' ');
          v.push(b' ');
          v.push(b' ');
        }
      }
      v.push(b'\t');

      for &byte in chunk {
        if (byte >= 32 && byte <= 126) || byte >= 128 {
          v.push(byte);
        } else {
          v.push(b'.');
        }
      }
      v.push(b'\n');
    }

    String::from_utf8_lossy(&v[..]).into_owned()
  }
}

#[cfg(feature = "std")]
impl HexDisplay for str {
  #[allow(unused_variables)]
  fn to_hex(&self, chunk_size: usize) -> String {
    self.to_hex_from(chunk_size, 0)
  }

  #[allow(unused_variables)]
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
    self.as_bytes().to_hex_from(chunk_size, from)
  }
}

#[doc(hidden)]
#[macro_export]
macro_rules! nom_line (
  () => (line!());
);

#[doc(hidden)]
#[macro_export]
macro_rules! nom_println (
  ($($args:tt)*) => (println!($($args)*));
);

#[doc(hidden)]
#[macro_export]
macro_rules! nom_stringify (
  ($($args:tt)*) => (stringify!($($args)*));
);


/// Prints a message if the parser fails
///
/// The message prints the `Error` or `Incomplete`
/// and the parser's calling code
///
/// ```
/// # #[macro_use] extern crate nom;
/// # fn main() {
///    named!(f, dbg!( tag!( "abcd" ) ) );
///
///    let a = &b"efgh"[..];
///
///    // Will print the following message:
///    // Error(Position(0, [101, 102, 103, 104])) at l.5 by ' tag ! ( "abcd" ) '
///    f(a);
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! dbg (
  ($i: expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::lib::std::result::Result::*;
      let l = nom_line!();
      match $submac!($i, $($args)*) {
        Err(e) => {
          nom_println!("Err({:?}) at l.{} by ' {} '", e, l, nom_stringify!($submac!($($args)*)));
          Err(e)
        },
        a => a,
      }
    }
  );

  ($i:expr, $f:ident) => (
      dbg!($i, call!($f));
  );
);

/// Prints a message and the input if the parser fails
///
/// The message prints the `Error` or `Incomplete`
/// and the parser's calling code.
///
/// It also displays the input in hexdump format
///
/// ```ignore
/// # #[macro_use] extern crate nom;
/// # fn main() {
///    named!(f, dbg_dmp!( tag!( "abcd" ) ) );
///
///    let a = &b"efghijkl"[..];
///
///    // Will print the following message:
///    // Error(Position(0, [101, 102, 103, 104, 105, 106, 107, 108])) at l.5 by ' tag ! ( "abcd" ) '
///    // 00000000        65 66 67 68 69 6a 6b 6c         efghijkl
///    f(a);
/// # }
#[macro_export(local_inner_macros)]
#[cfg(feature = "std")]
macro_rules! dbg_dmp (
  ($i: expr, $submac:ident!( $($args:tt)* )) => (
    {
      use $crate::HexDisplay;
      let l = nom_line!();
      match $submac!($i, $($args)*) {
        Err(e) => {
          nom_println!("Error({:?}) at l.{} by ' {} '\n{}", e, l, nom_stringify!($submac!($($args)*)), $i.to_hex(8));
          Err(e)
        },
        a => a,
      }
    }
  );

  ($i:expr, $f:ident) => (
      dbg_dmp!($i, call!($f));
  );
);

/*FIXME: convert functions to new error management
pub fn error_to_list<P: Clone, E: Clone>(e: &Context<P, E>) -> Vec<(P, ErrorKind<E>)> {
  match e {
    &Context::Code(ref i, ref err) => {
      let mut v = Vec::new();
      v.push((i.clone(), err.clone()));
      return v;
    }
    &Context::List(ref v) => {
      let mut v2 = v.clone();
      v2.reverse();
      v2
    }
  }
}

pub fn compare_error_paths<P: Clone + PartialEq, E: Clone + PartialEq>(e1: &Context<P, E>, e2: &Context<P, E>) -> bool {
  error_to_list(e1) == error_to_list(e2)
}

#[cfg(feature = "std")]
use lib::std::hash::Hash;

#[cfg(feature = "std")]
pub fn add_error_pattern<'a, I: Clone + Hash + Eq, O, E: Clone + Hash + Eq>(
  h: &mut HashMap<Vec<(I, ErrorKind<E>)>, &'a str>,
  res: IResult<I, O, E>,
  message: &'a str,
) -> bool {
  match res {
    Err(Err::Error(e)) | Err(Err::Failure(e)) => {
      h.insert(error_to_list(&e), message);
      true
    }
    _ => false,
  }
}

pub fn slice_to_offsets(input: &[u8], s: &[u8]) -> (usize, usize) {
  let start = input.as_ptr();
  let off1 = s.as_ptr() as usize - start as usize;
  let off2 = off1 + s.len();
  (off1, off2)
}

#[cfg(feature = "std")]
pub fn prepare_errors<O, E: Clone>(input: &[u8], res: IResult<&[u8], O, E>) -> Option<Vec<(ErrorKind<E>, usize, usize)>> {
  if let Err(Err::Error(e)) = res {
    let mut v: Vec<(ErrorKind<E>, usize, usize)> = Vec::new();

    match e {
      Context::Code(p, kind) => {
        let (o1, o2) = slice_to_offsets(input, p);
        v.push((kind, o1, o2));
      }
      Context::List(mut l) => {
        for (p, kind) in l.drain(..) {
          let (o1, o2) = slice_to_offsets(input, p);
          v.push((kind, o1, o2));
        }

        v.reverse()
      }
    }

    v.sort_by(|a, b| a.1.cmp(&b.1));
    Some(v)
  } else {
    None
  }
}

#[cfg(feature = "std")]
pub fn print_error<O, E: Clone>(input: &[u8], res: IResult<&[u8], O, E>) {
  if let Some(v) = prepare_errors(input, res) {
    let colors = generate_colors(&v);
    println!("parser codes: {}", print_codes(&colors, &HashMap::new()));
    println!("{}", print_offsets(input, 0, &v));
  } else {
    println!("not an error");
  }
}

#[cfg(feature = "std")]
pub fn generate_colors<E>(v: &[(ErrorKind<E>, usize, usize)]) -> HashMap<u32, u8> {
  let mut h: HashMap<u32, u8> = HashMap::new();
  let mut color = 0;

  for &(ref c, _, _) in v.iter() {
    h.insert(error_to_u32(c), color + 31);
    color = color + 1 % 7;
  }

  h
}

pub fn code_from_offset(v: &[(ErrorKind, usize, usize)], offset: usize) -> Option<u32> {
  let mut acc: Option<(u32, usize, usize)> = None;
  for &(ref ek, s, e) in v.iter() {
    let c = error_to_u32(ek);
    if s <= offset && offset <= e {
      if let Some((_, start, end)) = acc {
        if start <= s && e <= end {
          acc = Some((c, s, e));
        }
      } else {
        acc = Some((c, s, e));
      }
    }
  }
  if let Some((code, _, _)) = acc {
    return Some(code);
  } else {
    return None;
  }
}

#[cfg(feature = "alloc")]
pub fn reset_color(v: &mut Vec<u8>) {
  v.push(0x1B);
  v.push(b'[');
  v.push(0);
  v.push(b'm');
}

#[cfg(feature = "alloc")]
pub fn write_color(v: &mut Vec<u8>, color: u8) {
  v.push(0x1B);
  v.push(b'[');
  v.push(1);
  v.push(b';');
  let s = color.to_string();
  let bytes = s.as_bytes();
  v.extend(bytes.iter().cloned());
  v.push(b'm');
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "cargo-clippy", allow(implicit_hasher))]
pub fn print_codes(colors: &HashMap<u32, u8>, names: &HashMap<u32, &str>) -> String {
  let mut v = Vec::new();
  for (code, &color) in colors {
    if let Some(&s) = names.get(code) {
      let bytes = s.as_bytes();
      write_color(&mut v, color);
      v.extend(bytes.iter().cloned());
    } else {
      let s = code.to_string();
      let bytes = s.as_bytes();
      write_color(&mut v, color);
      v.extend(bytes.iter().cloned());
    }
    reset_color(&mut v);
    v.push(b' ');
  }
  reset_color(&mut v);

  String::from_utf8_lossy(&v[..]).into_owned()
}

#[cfg(feature = "std")]
pub fn print_offsets<E>(input: &[u8], from: usize, offsets: &[(ErrorKind<E>, usize, usize)]) -> String {
  let mut v = Vec::with_capacity(input.len() * 3);
  let mut i = from;
  let chunk_size = 8;
  let mut current_code: Option<u32> = None;
  let mut current_code2: Option<u32> = None;

  let colors = generate_colors(&offsets);

  for chunk in input.chunks(chunk_size) {
    let s = format!("{:08x}", i);
    for &ch in s.as_bytes().iter() {
      v.push(ch);
    }
    v.push(b'\t');

    let mut k = i;
    let mut l = i;
    for &byte in chunk {
      if let Some(code) = code_from_offset(&offsets, k) {
        if let Some(current) = current_code {
          if current != code {
            reset_color(&mut v);
            current_code = Some(code);
            if let Some(&color) = colors.get(&code) {
              write_color(&mut v, color);
            }
          }
        } else {
          current_code = Some(code);
          if let Some(&color) = colors.get(&code) {
            write_color(&mut v, color);
          }
        }
      }
      v.push(CHARS[(byte >> 4) as usize]);
      v.push(CHARS[(byte & 0xf) as usize]);
      v.push(b' ');
      k = k + 1;
    }

    reset_color(&mut v);

    if chunk_size > chunk.len() {
      for _ in 0..(chunk_size - chunk.len()) {
        v.push(b' ');
        v.push(b' ');
        v.push(b' ');
      }
    }
    v.push(b'\t');

    for &byte in chunk {
      if let Some(code) = code_from_offset(&offsets, l) {
        if let Some(current) = current_code2 {
          if current != code {
            reset_color(&mut v);
            current_code2 = Some(code);
            if let Some(&color) = colors.get(&code) {
              write_color(&mut v, color);
            }
          }
        } else {
          current_code2 = Some(code);
          if let Some(&color) = colors.get(&code) {
            write_color(&mut v, color);
          }
        }
      }
      if (byte >= 32 && byte <= 126) || byte >= 128 {
        v.push(byte);
      } else {
        v.push(b'.');
      }
      l = l + 1;
    }
    reset_color(&mut v);

    v.push(b'\n');
    i = i + chunk_size;
  }

  String::from_utf8_lossy(&v[..]).into_owned()
}
  */
