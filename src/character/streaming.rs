//! character specific parsers and combinators, streaming version
//!
//! functions recognizing specific characters

use internal::{Err, IResult, Needed};
use error::ParseError;
use ::lib::std::ops::{Range, RangeFrom, RangeTo};
use traits::{AsChar, FindToken, InputIter, InputLength, InputTakeAtPosition, Slice};
use traits::{Compare, CompareResult};

use error::ErrorKind;

pub fn char<I, Error: ParseError<I>>(c: char) -> impl Fn(I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar,
{
  move |i: I| match (i).iter_elements().next().map(|t| {
    let b = t.as_char() == c;
    (&c, b)
  }) {
    None => Err(Err::Incomplete(Needed::Size(1))),
    Some((_, false)) => {
      //let e: ErrorKind = ErrorKind::Char;
      Err(Err::Error(Error::from_char(i, c)))
    }
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
  }
}


pub fn one_of<I, T, Error: ParseError<I>>(list: T) -> impl Fn(I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar + Copy,
  T: FindToken<<I as InputIter>::Item>,
{
  move |i: I| match (i).iter_elements().next().map(|c| (c, list.find_token(c))) {
    None => Err(Err::Incomplete(Needed::Size(1))),
    Some((_, false)) => Err(Err::Error(Error::from_error_kind(i, ErrorKind::OneOf))),
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
  }
}

pub fn none_of<I, T, Error: ParseError<I>>(list: T) -> impl Fn(I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar + Copy,
  T: FindToken<<I as InputIter>::Item>,
{
  move |i: I| match (i).iter_elements().next().map(|c| (c, !list.find_token(c))) {
    None => Err(Err::Incomplete(Needed::Size(1))),
    Some((_, false)) => Err(Err::Error(Error::from_error_kind(i, ErrorKind::NoneOf))),
    Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
  }
}

pub fn crlf<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter,
  T: Compare<&'static str>,
{
  match input.compare("\r\n") {
    //FIXME: is this the right index?
    CompareResult::Ok => Ok((input.slice(2..), input.slice(0..2))),
    CompareResult::Incomplete => Err(Err::Incomplete(Needed::Size(2))),
    CompareResult::Error => {
      let e: ErrorKind = ErrorKind::CrLf;
      Err(Err::Error(E::from_error_kind(input, e)))
    }
  }
}

// FIXME: when rust-lang/rust#17436 is fixed, macros will be able to export
// public methods
pub fn not_line_ending<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength,
  T: Compare<&'static str>,
  <T as InputIter>::Item: AsChar,
  <T as InputIter>::RawItem: AsChar,
{
  match input.position(|item| {
    let c = item.as_char();
    c == '\r' || c == '\n'
  }) {
    None => {
      Err(Err::Incomplete(Needed::Unknown))
    }
    Some(index) => {
      let mut it = input.slice(index..).iter_elements();
      let nth = it.next().unwrap().as_char();
      if nth == '\r' {
        let sliced = input.slice(index..);
        let comp = sliced.compare("\r\n");
        match comp {
          //FIXME: calculate the right index
          CompareResult::Incomplete => Err(Err::Incomplete(Needed::Unknown)),
          CompareResult::Error => {
            let e: ErrorKind = ErrorKind::Tag;
            Err(Err::Error(E::from_error_kind(input, e)))
          }
          CompareResult::Ok => Ok((input.slice(index..), input.slice(..index))),
        }
      } else {
        Ok((input.slice(index..), input.slice(..index)))
      }
    }
  }
}

/// Recognizes an end of line (both '\n' and '\r\n')
pub fn line_ending<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength,
  T: Compare<&'static str>,
{
  match input.compare("\n") {
    CompareResult::Ok => Ok((input.slice(1..), input.slice(0..1))),
    CompareResult::Incomplete => Err(Err::Incomplete(Needed::Size(1))),
    CompareResult::Error => {
      match input.compare("\r\n") {
        //FIXME: is this the right index?
        CompareResult::Ok => Ok((input.slice(2..), input.slice(0..2))),
        CompareResult::Incomplete => Err(Err::Incomplete(Needed::Size(2))),
        CompareResult::Error => Err(Err::Error(E::from_error_kind(input, ErrorKind::CrLf))),
      }
    }
  }
}

pub fn eol<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: Slice<Range<usize>> + Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
  T: InputIter + InputLength,
  T: Compare<&'static str>,
{
  line_ending(input)
}

/// matches a newline character '\\n'
pub fn newline<I, Error: ParseError<I>>(input: I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar,
{
  char('\n')(input)
}

/// matches a tab character '\t'
pub fn tab<I, Error: ParseError<I>>(input: I) -> IResult<I, char, Error>
where
  I: Slice<RangeFrom<usize>> + InputIter,
  <I as InputIter>::Item: AsChar,
{
  char('\t')(input)
}

/// matches one byte as a character. Note that the input type will
/// accept a `str`, but not a `&[u8]`, unlike many other nom parsers.
///
/// # Example
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::{character::streaming::anychar, error::ErrorKind};
/// # fn main() {
/// assert_eq!(anychar::<_,(&str, ErrorKind)>("abc"), Ok(("bc",'a')));
/// # }
/// ```
pub fn anychar<T, E: ParseError<T>>(input: T) -> IResult<T, char, E>
where
  T: InputIter + InputLength + Slice<RangeFrom<usize>>,
  <T as InputIter>::Item: AsChar,
{
  let mut it = input.iter_indices();
  match it.next() {
    None => Err(Err::Incomplete(Needed::Size(1))),
    Some((_, c)) => match it.next() {
      None => Ok((input.slice(input.input_len()..), c.as_char())),
      Some((idx, _)) => Ok((input.slice(idx..), c.as_char())),
    },
  }
}

/// Recognizes one or more lowercase and uppercase alphabetic characters.
/// For ASCII strings: a-zA-Z
/// For UTF8 strings, any alphabetic code point (ie, not only the ASCII ones)
pub fn alpha<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  alpha1(input)
}

/// Recognizes zero or more lowercase and uppercase alphabetic characters.
/// For ASCII strings: a-zA-Z
/// For UTF8 strings, any alphabetic code point (ie, not only the ASCII ones)
pub fn alpha0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position(|item| !item.is_alpha())
}

/// Recognizes one or more lowercase and uppercase alphabetic characters
/// For ASCII strings: a-zA-Z
/// For UTF8 strings, any alphabetic code point (ie, not only the ASCII ones)
pub fn alpha1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1(|item| !item.is_alpha(), ErrorKind::Alpha)
}

/// Recognizes one or more numerical characters: 0-9
pub fn digit<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  digit1(input)
}

/// Recognizes zero or more numerical characters: 0-9
pub fn digit0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position(|item| !item.is_dec_digit())
}

/// Recognizes one or more numerical characters: 0-9
pub fn digit1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1(|item| !item.is_dec_digit(), ErrorKind::Digit)
}

/// Recognizes one or more hexadecimal numerical characters: 0-9, A-F, a-f
pub fn hex_digit<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  hex_digit1(input)
}

/// Recognizes zero or more hexadecimal numerical characters: 0-9, A-F, a-f
pub fn hex_digit0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position(|item| !item.is_hex_digit())
}
/// Recognizes one or more hexadecimal numerical characters: 0-9, A-F, a-f
pub fn hex_digit1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1(|item| !item.is_hex_digit(), ErrorKind::HexDigit)
}

/// Recognizes one or more octal characters: 0-7
pub fn oct_digit<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  oct_digit1(input)
}

/// Recognizes zero or more octal characters: 0-7
pub fn oct_digit0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position(|item| !item.is_oct_digit())
}

/// Recognizes one or more octal characters: 0-7
pub fn oct_digit1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1(|item| !item.is_oct_digit(), ErrorKind::OctDigit)
}

/// Recognizes one or more numerical and alphabetic characters
/// For ASCII strings: 0-9a-zA-Z
/// For UTF8 strings, 0-9 and any alphabetic code point (ie, not only the ASCII ones)
pub fn alphanumeric<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  alphanumeric1(input)
}

/// Recognizes zero or more numerical and alphabetic characters.
/// For ASCII strings: 0-9a-zA-Z
/// For UTF8 strings, 0-9 and any alphabetic code point (ie, not only the ASCII ones)
pub fn alphanumeric0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position(|item| !item.is_alphanum())
}
/// Recognizes one or more numerical and alphabetic characters.
/// For ASCII strings: 0-9a-zA-Z
/// For UTF8 strings, 0-9 and any alphabetic code point (ie, not only the ASCII ones)
pub fn alphanumeric1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar,
{
  input.split_at_position1(|item| !item.is_alphanum(), ErrorKind::AlphaNumeric)
}

/// Recognizes one or more spaces and tabs
pub fn space<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  space1(input)
}

/// Recognizes zero or more spaces and tabs
pub fn space0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position(|item| {
    let c = item.clone().as_char();
    !(c == ' ' || c == '\t')
  })
}
/// Recognizes one or more spaces and tabs
pub fn space1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position1(
    |item| {
      let c = item.clone().as_char();
      !(c == ' ' || c == '\t')
    },
    ErrorKind::Space,
  )
}

/// Recognizes one or more spaces, tabs, carriage returns and line feeds
pub fn multispace<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  multispace1(input)
}

/// Recognizes zero or more spaces, tabs, carriage returns and line feeds
pub fn multispace0<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position(|item| {
    let c = item.clone().as_char();
    !(c == ' ' || c == '\t' || c == '\r' || c == '\n')
  })
}
/// Recognizes one or more spaces, tabs, carriage returns and line feeds
pub fn multispace1<T, E: ParseError<T>>(input: T) -> IResult<T, T, E>
where
  T: InputTakeAtPosition,
  <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
  input.split_at_position1(
    |item| {
      let c = item.clone().as_char();
      !(c == ' ' || c == '\t' || c == '\r' || c == '\n')
    },
    ErrorKind::MultiSpace,
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use internal::{Err, Needed};
  use error::ErrorKind;

  macro_rules! assert_parse(
    ($left: expr, $right: expr) => {
      let res: $crate::IResult<_, _, (_, ErrorKind)> = $left;
      assert_eq!(res, $right);
    };
  );

  #[test]
  fn anychar_str() {
    use super::anychar;
    assert_eq!(anychar::<_, (&str, ErrorKind)>("Ә"), Ok(("", 'Ә')));
  }

  #[test]
  fn character() {
    let a: &[u8] = b"abcd";
    let b: &[u8] = b"1234";
    let c: &[u8] = b"a123";
    let d: &[u8] = "azé12".as_bytes();
    let e: &[u8] = b" ";
    let f: &[u8] = b" ;";
    //assert_eq!(alpha::<_, (_, ErrorKind)>(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_parse!(alpha(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      alpha(b),
      Err(Err::Error((b, ErrorKind::Alpha)))
    );
    assert_eq!(alpha::<_, (_, ErrorKind)>(c), Ok((&c[1..], &b"a"[..])));
    assert_eq!(alpha::<_, (_, ErrorKind)>(d), Ok(("é12".as_bytes(), &b"az"[..])));
    assert_eq!(
      digit(a),
      Err(Err::Error((a, ErrorKind::Digit)))
    );
    assert_eq!(digit::<_, (_, ErrorKind)>(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      digit(c),
      Err(Err::Error((c, ErrorKind::Digit)))
    );
    assert_eq!(
      digit(d),
      Err(Err::Error((d, ErrorKind::Digit)))
    );
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(c), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(d), Ok(("zé12".as_bytes(), &b"a"[..])));
    assert_eq!(
      hex_digit(e),
      Err(Err::Error((e, ErrorKind::HexDigit)))
    );
    assert_eq!(
      oct_digit(a),
      Err(Err::Error((a, ErrorKind::OctDigit)))
    );
    assert_eq!(oct_digit::<_, (_, ErrorKind)>(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      oct_digit(c),
      Err(Err::Error((c, ErrorKind::OctDigit)))
    );
    assert_eq!(
      oct_digit(d),
      Err(Err::Error((d, ErrorKind::OctDigit)))
    );
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(a), Err(Err::Incomplete(Needed::Size(1))));
    //assert_eq!(fix_error!(b,(), alphanumeric), Ok((empty, b)));
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(c), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(d), Ok(("é12".as_bytes(), &b"az"[..])));
    assert_eq!(space::<_, (_, ErrorKind)>(e), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(space::<_, (_, ErrorKind)>(f), Ok((&b";"[..], &b" "[..])));
  }

  #[cfg(feature = "alloc")]
  #[test]
  fn character_s() {
    let a = "abcd";
    let b = "1234";
    let c = "a123";
    let d = "azé12";
    let e = " ";
    assert_eq!(alpha::<_, (_, ErrorKind)>(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      alpha(b),
      Err(Err::Error((b, ErrorKind::Alpha)))
    );
    assert_eq!(alpha::<_, (_, ErrorKind)>(c), Ok((&c[1..], &"a"[..])));
    assert_eq!(alpha::<_, (_, ErrorKind)>(d), Ok(("12", &"azé"[..])));
    assert_eq!(
      digit(a),
      Err(Err::Error((a, ErrorKind::Digit)))
    );
    assert_eq!(digit::<_, (_, ErrorKind)>(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      digit(c),
      Err(Err::Error((c, ErrorKind::Digit)))
    );
    assert_eq!(
      digit(d),
      Err(Err::Error((d, ErrorKind::Digit)))
    );
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(a), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(c), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(hex_digit::<_, (_, ErrorKind)>(d), Ok(("zé12", &"a"[..])));
    assert_eq!(
      hex_digit(e),
      Err(Err::Error((e, ErrorKind::HexDigit)))
    );
    assert_eq!(
      oct_digit(a),
      Err(Err::Error((a, ErrorKind::OctDigit)))
    );
    assert_eq!(oct_digit::<_, (_, ErrorKind)>(b), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(
      oct_digit(c),
      Err(Err::Error((c, ErrorKind::OctDigit)))
    );
    assert_eq!(
      oct_digit(d),
      Err(Err::Error((d, ErrorKind::OctDigit)))
    );
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(a), Err(Err::Incomplete(Needed::Size(1))));
    //assert_eq!(fix_error!(b,(), alphanumeric), Ok((empty, b)));
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(c), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(alphanumeric::<_, (_, ErrorKind)>(d), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(space::<_, (_, ErrorKind)>(e), Err(Err::Incomplete(Needed::Size(1))));
  }

  use traits::Offset;
  #[test]
  fn offset() {
    let a = &b"abcd;"[..];
    let b = &b"1234;"[..];
    let c = &b"a123;"[..];
    let d = &b" \t;"[..];
    let e = &b" \t\r\n;"[..];
    let f = &b"123abcDEF;"[..];

    match alpha::<_, (_, ErrorKind)>(a) {
      Ok((i, _)) => {
        assert_eq!(a.offset(i) + i.len(), a.len());
      }
      _ => panic!("wrong return type in offset test for alpha"),
    }
    match digit::<_, (_, ErrorKind)>(b) {
      Ok((i, _)) => {
        assert_eq!(b.offset(i) + i.len(), b.len());
      }
      _ => panic!("wrong return type in offset test for digit"),
    }
    match alphanumeric::<_, (_, ErrorKind)>(c) {
      Ok((i, _)) => {
        assert_eq!(c.offset(i) + i.len(), c.len());
      }
      _ => panic!("wrong return type in offset test for alphanumeric"),
    }
    match space::<_, (_, ErrorKind)>(d) {
      Ok((i, _)) => {
        assert_eq!(d.offset(i) + i.len(), d.len());
      }
      _ => panic!("wrong return type in offset test for space"),
    }
    match multispace::<_, (_, ErrorKind)>(e) {
      Ok((i, _)) => {
        assert_eq!(e.offset(i) + i.len(), e.len());
      }
      _ => panic!("wrong return type in offset test for multispace"),
    }
    match hex_digit::<_, (_, ErrorKind)>(f) {
      Ok((i, _)) => {
        assert_eq!(f.offset(i) + i.len(), f.len());
      }
      _ => panic!("wrong return type in offset test for hex_digit"),
    }
    match oct_digit::<_, (_, ErrorKind)>(f) {
      Ok((i, _)) => {
        assert_eq!(f.offset(i) + i.len(), f.len());
      }
      _ => panic!("wrong return type in offset test for oct_digit"),
    }
  }

  #[test]
  fn is_not_line_ending_bytes() {
    let a: &[u8] = b"ab12cd\nefgh";
    assert_eq!(not_line_ending::<_, (_, ErrorKind)>(a), Ok((&b"\nefgh"[..], &b"ab12cd"[..])));

    let b: &[u8] = b"ab12cd\nefgh\nijkl";
    assert_eq!(
      not_line_ending::<_, (_, ErrorKind)>(b),
      Ok((&b"\nefgh\nijkl"[..], &b"ab12cd"[..]))
    );

    let c: &[u8] = b"ab12cd\r\nefgh\nijkl";
    assert_eq!(
      not_line_ending::<_, (_, ErrorKind)>(c),
      Ok((&b"\r\nefgh\nijkl"[..], &b"ab12cd"[..]))
    );

    let d: &[u8] = b"ab12cd";
    assert_eq!(not_line_ending::<_, (_, ErrorKind)>(d), Err(Err::Incomplete(Needed::Unknown)));
  }

  #[test]
  fn is_not_line_ending_str() {
    /*
    let a: &str = "ab12cd\nefgh";
    assert_eq!(not_line_ending(a), Ok((&"\nefgh"[..], &"ab12cd"[..])));

    let b: &str = "ab12cd\nefgh\nijkl";
    assert_eq!(not_line_ending(b), Ok((&"\nefgh\nijkl"[..], &"ab12cd"[..])));

    let c: &str = "ab12cd\r\nefgh\nijkl";
    assert_eq!(not_line_ending(c), Ok((&"\r\nefgh\nijkl"[..], &"ab12cd"[..])));

    let d = "βèƒôřè\nÂßÇáƒƭèř";
    assert_eq!(not_line_ending(d), Ok((&"\nÂßÇáƒƭèř"[..], &"βèƒôřè"[..])));

    let e = "βèƒôřè\r\nÂßÇáƒƭèř";
    assert_eq!(not_line_ending(e), Ok((&"\r\nÂßÇáƒƭèř"[..], &"βèƒôřè"[..])));
    */

    let f = "βèƒôřè\rÂßÇáƒƭèř";
    assert_eq!(
      not_line_ending(f),
      Err(Err::Error((f, ErrorKind::Tag)))
    );

    let g2: &str = "ab12cd";
    assert_eq!(not_line_ending::<_, (_, ErrorKind)>(g2), Err(Err::Incomplete(Needed::Unknown)));
  }

  #[test]
  fn hex_digit_test() {
    let i = &b"0123456789abcdefABCDEF;"[..];
    assert_parse!(hex_digit(i), Ok((&b";"[..], &i[..i.len() - 1])));

    let i = &b"g"[..];
    assert_parse!(
      hex_digit(i),
      Err(Err::Error(error_position!(i, ErrorKind::HexDigit)))
    );

    let i = &b"G"[..];
    assert_parse!(
      hex_digit(i),
      Err(Err::Error(error_position!(i, ErrorKind::HexDigit)))
    );

    assert!(::character::is_hex_digit(b'0'));
    assert!(::character::is_hex_digit(b'9'));
    assert!(::character::is_hex_digit(b'a'));
    assert!(::character::is_hex_digit(b'f'));
    assert!(::character::is_hex_digit(b'A'));
    assert!(::character::is_hex_digit(b'F'));
    assert!(!::character::is_hex_digit(b'g'));
    assert!(!::character::is_hex_digit(b'G'));
    assert!(!::character::is_hex_digit(b'/'));
    assert!(!::character::is_hex_digit(b':'));
    assert!(!::character::is_hex_digit(b'@'));
    assert!(!::character::is_hex_digit(b'\x60'));
  }

  #[test]
  fn oct_digit_test() {
    let i = &b"01234567;"[..];
    assert_parse!(oct_digit(i), Ok((&b";"[..], &i[..i.len() - 1])));

    let i = &b"8"[..];
    assert_parse!(
      oct_digit(i),
      Err(Err::Error(error_position!(i, ErrorKind::OctDigit)))
    );

    assert!(::character::is_oct_digit(b'0'));
    assert!(::character::is_oct_digit(b'7'));
    assert!(!::character::is_oct_digit(b'8'));
    assert!(!::character::is_oct_digit(b'9'));
    assert!(!::character::is_oct_digit(b'a'));
    assert!(!::character::is_oct_digit(b'A'));
    assert!(!::character::is_oct_digit(b'/'));
    assert!(!::character::is_oct_digit(b':'));
    assert!(!::character::is_oct_digit(b'@'));
    assert!(!::character::is_oct_digit(b'\x60'));
  }

  #[test]
  fn full_line_windows() {
    named!(
      take_full_line<(&[u8], &[u8])>,
      tuple!(not_line_ending, line_ending)
    );
    let input = b"abc\r\n";
    let output = take_full_line(input);
    assert_eq!(output, Ok((&b""[..], (&b"abc"[..], &b"\r\n"[..]))));
  }

  #[test]
  fn full_line_unix() {
    named!(
      take_full_line<(&[u8], &[u8])>,
      tuple!(not_line_ending, line_ending)
    );
    let input = b"abc\n";
    let output = take_full_line(input);
    assert_eq!(output, Ok((&b""[..], (&b"abc"[..], &b"\n"[..]))));
  }

  #[test]
  fn check_windows_lineending() {
    let input = b"\r\n";
    let output = line_ending(&input[..]);
    assert_parse!(output, Ok((&b""[..], &b"\r\n"[..])));
  }

  #[test]
  fn check_unix_lineending() {
    let input = b"\n";
    let output = line_ending(&input[..]);
    assert_parse!(output, Ok((&b""[..], &b"\n"[..])));
  }

  #[test]
  fn cr_lf() {
    assert_parse!(crlf(&b"\r\na"[..]), Ok((&b"a"[..], &b"\r\n"[..])));
    assert_parse!(crlf(&b"\r"[..]), Err(Err::Incomplete(Needed::Size(2))));
    assert_parse!(
      crlf(&b"\ra"[..]),
      Err(Err::Error(error_position!(&b"\ra"[..], ErrorKind::CrLf)))
    );

    assert_parse!(crlf("\r\na"), Ok(("a", "\r\n")));
    assert_parse!(crlf("\r"), Err(Err::Incomplete(Needed::Size(2))));
    assert_parse!(
      crlf("\ra"),
      Err(Err::Error(error_position!("\ra", ErrorKind::CrLf)))
    );
  }

  #[test]
  fn end_of_line() {
    assert_parse!(eol(&b"\na"[..]), Ok((&b"a"[..], &b"\n"[..])));
    assert_parse!(eol(&b"\r\na"[..]), Ok((&b"a"[..], &b"\r\n"[..])));
    assert_parse!(eol(&b"\r"[..]), Err(Err::Incomplete(Needed::Size(2))));
    assert_parse!(
      eol(&b"\ra"[..]),
      Err(Err::Error(error_position!(&b"\ra"[..], ErrorKind::CrLf)))
    );

    assert_parse!(eol("\na"), Ok(("a", "\n")));
    assert_parse!(eol("\r\na"), Ok(("a", "\r\n")));
    assert_parse!(eol("\r"), Err(Err::Incomplete(Needed::Size(2))));
    assert_parse!(
      eol("\ra"),
      Err(Err::Error(error_position!("\ra", ErrorKind::CrLf)))
    );
  }
}
