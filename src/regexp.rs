#[doc(hidden)]
#[macro_export]
macro_rules! regex (
  ($re: ident, $s:expr) => (
    lazy_static! {
      static ref $re: ::regex::Regex = ::regex::Regex::new($s).unwrap();
    }
  );
);

#[doc(hidden)]
#[macro_export]
macro_rules! regex_bytes (
  ($re: ident, $s:expr) => (
    lazy_static! {
      static ref $re: ::regex::bytes::Regex = ::regex::bytes::Regex::new($s).unwrap();
    }
  );
);


/// `re_match!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the whole input if a match is found
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_match (
  ($i:expr, $re:expr) => (
    {
      use $crate::InputLength;
      use $crate::Slice;
      let re = ::regex::Regex::new($re).unwrap();
      if re.is_match($i) {
        $crate::IResult::Done($i.slice($i.input_len()..), $i)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpMatch));
        res
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_match_static!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the whole input if a match is found. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_match_static (
  ($i:expr, $re:expr) => (
    {
      use $crate::InputLength;
      use $crate::Slice;
      regex!(RE, $re);
      if RE.is_match($i) {
        $crate::IResult::Done($i.slice($i.input_len()..), $i)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpMatch));
        res
      }
    }
  )
);

/// `re_bytes_match!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the whole input if a match is found
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_bytes_match (
  ($i:expr, $re:expr) => (
    {
      use $crate::InputLength;
      use $crate::Slice;
      let re = ::regex::bytes::Regex::new($re).unwrap();
      if re.is_match($i) {
        $crate::IResult::Done($i.slice($i.input_len()..), $i)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpMatch));
        res
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_bytes_match_static!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the whole input if a match is found. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_bytes_match_static (
  ($i:expr, $re:expr) => (
    {
      use $crate::InputLength;
      use $crate::Slice;
      regex_bytes!(RE, $re);
      if RE.is_match($i) {
        $crate::IResult::Done($i.slice($i.input_len()..), $i)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpMatch));
        res
      }
    }
  )
);

/// `re_find!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the first match
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_find (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      let re = ::regex::Regex::new($re).unwrap();
      if let Some(m) = re.find($i) {
        $crate::IResult::Done($i.slice(m.end()..), $i.slice(m.start()..m.end()))
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpFind));
        res
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_find_static!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the first match. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_find_static (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      regex!(RE, $re);
      if let Some(m) = RE.find($i) {
        $crate::IResult::Done($i.slice(m.end()..), $i.slice(m.start()..m.end()))
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpFind));
        res
      }
    }

  )
);

/// `re_bytes_find!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the first match
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_bytes_find (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      let re = ::regex::bytes::Regex::new($re).unwrap();
      if let Some(m) = re.find($i) {
        $crate::IResult::Done($i.slice(m.end()..), $i.slice(m.start()..m.end()))
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpFind));
        res
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_bytes_find!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the first match. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_bytes_find_static (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      regex_bytes!(RE, $re);
      if let Some(m) = RE.find($i) {
        $crate::IResult::Done($i.slice(m.end()..), $i.slice(m.start()..m.end()))
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpFind));
        res
      }
    }

  )
);

/// `re_matches!(regexp) => &[T] -> IResult<&[T], Vec<&[T]>>`
/// Returns all the matched parts
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_matches (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      let re = ::regex::Regex::new($re).unwrap();
      let v: Vec<&str> = re.find_iter($i).map(|m| $i.slice(m.start()..m.end())).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpMatches));
        res
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_matches_static!(regexp) => &[T] -> IResult<&[T], Vec<&[T]>>`
/// Returns all the matched parts. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_matches_static (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      regex!(RE, $re);
      let v: Vec<&str> = RE.find_iter($i).map(|m| $i.slice(m.start()..m.end())).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpMatches));
        res
      }
    }
  )
);

/// `re_bytes_matches!(regexp) => &[T] -> IResult<&[T], Vec<&[T]>>`
/// Returns all the matched parts
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_bytes_matches (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      let re = ::regex::bytes::Regex::new($re).unwrap();
      let v: Vec<&[u8]> = re.find_iter($i).map(|m| $i.slice(m.start()..m.end())).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpMatches));
        res
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_bytes_matches_static!(regexp) => &[T] -> IResult<&[T], Vec<&[T]>>`
/// Returns all the matched parts. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_bytes_matches_static (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      regex_bytes!(RE, $re);
      let v: Vec<&[u8]> = RE.find_iter($i).map(|m| $i.slice(m.start()..m.end())).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpMatches));
        res
      }
    }
  )
);

/// `re_capture!(regexp) => &[T] -> IResult<&[T], Vec<&[T]>>`
/// Returns the first capture group
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_capture (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      let re = ::regex::Regex::new($re).unwrap();
      if let Some(c) = re.captures($i) {
        let v:Vec<&str> = c.iter().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|m| $i.slice(m.start()..m.end())).collect();
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpCapture));
        res
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_capture_static!(regexp) => &[T] -> IResult<&[T], Vec<&[T]>>`
/// Returns the first capture group. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_capture_static (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      regex!(RE, $re);
      if let Some(c) = RE.captures($i) {
        let v:Vec<&str> = c.iter().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|m| $i.slice(m.start()..m.end())).collect();
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpCapture));
        res
      }
    }
  )
);

/// `re_bytes_capture!(regexp) => &[T] -> IResult<&[T], Vec<&[T]>>`
/// Returns the first capture group
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_bytes_capture (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      let re = ::regex::bytes::Regex::new($re).unwrap();
      if let Some(c) = re.captures($i) {
        let v:Vec<&[u8]> = c.iter().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|m| $i.slice(m.start()..m.end())).collect();
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpCapture));
        res
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_bytes_capture_static!(regexp) => &[T] -> IResult<&[T], Vec<&[T]>>`
/// Returns the first capture group. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_bytes_capture_static (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      regex_bytes!(RE, $re);
      if let Some(c) = RE.captures($i) {
        let v:Vec<&[u8]> = c.iter().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|m| $i.slice(m.start()..m.end())).collect();
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpCapture));
        res
      }
    }
  )
);

/// `re_captures!(regexp) => &[T] -> IResult<&[T], Vec<Vec<&[T]>>>`
/// Returns all the capture groups
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_captures (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      let re = ::regex::Regex::new($re).unwrap();
      let v:Vec<Vec<&str>> = re.captures_iter($i).map(|c| c.iter().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|m| $i.slice(m.start()..m.end())).collect()).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap().last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpCapture));
        res
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_captures_static!(regexp) => &[T] -> IResult<&[T], Vec<Vec<&[T]>>>`
/// Returns all the capture groups. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_captures_static (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      regex!(RE, $re);
      let v:Vec<Vec<&str>> = RE.captures_iter($i).map(|c| c.iter().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|m| $i.slice(m.start()..m.end())).collect()).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap().last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpCapture));
        res
      }
    }
  )
);

/// `re_bytes_captures!(regexp) => &[T] -> IResult<&[T], Vec<Vec<&[T]>>>`
/// Returns all the capture groups
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_bytes_captures (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      let re = ::regex::bytes::Regex::new($re).unwrap();
      let v:Vec<Vec<&[u8]>> = re.captures_iter($i).map(|c| c.iter().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|m| $i.slice(m.start()..m.end())).collect()).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap().last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpCapture));
        res
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_bytes_captures_static!(regexp) => &[T] -> IResult<&[T], Vec<Vec<&[T]>>>`
/// Returns all the capture groups. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_bytes_captures_static (
  ($i:expr, $re:expr) => (
    {
      use $crate::Slice;
      regex_bytes!(RE, $re);
      let v:Vec<Vec<&[u8]>> = RE.captures_iter($i).map(|c| c.iter().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|m| $i.slice(m.start()..m.end())).collect()).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap().last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done($i.slice(offset..), v)
      } else {
        let res: $crate::IResult<_,_> = $crate::IResult::Error(error_code!($crate::ErrorKind::RegexpCapture));
        res
      }
    }
  )
);
#[cfg(test)]
mod tests {
  use internal::IResult::*;
  use util::ErrorKind;

  #[test]
  fn re_match() {
    named!(rm<&str,&str>, re_match!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", "2015-09-07"));
    assert_eq!(rm("blah"), Error(error_code!(ErrorKind::RegexpMatch)));
    assert_eq!(rm("2015-09-07blah"), Done("", "2015-09-07blah"));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_match_static() {
    named!(rm<&str,&str>, re_match_static!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", "2015-09-07"));
    assert_eq!(rm("blah"), Error(error_code!(ErrorKind::RegexpMatch)));
    assert_eq!(rm("2015-09-07blah"), Done("", "2015-09-07blah"));
  }

  #[test]
  fn re_find() {
    named!(rm<&str,&str>, re_find!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", "2015-09-07"));
    assert_eq!(rm("blah"), Error(error_code!(ErrorKind::RegexpFind)));
    assert_eq!(rm("2015-09-07blah"), Done("blah", "2015-09-07"));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_find_static() {
    named!(rm<&str,&str>, re_find_static!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", "2015-09-07"));
    assert_eq!(rm("blah"), Error(error_code!(ErrorKind::RegexpFind)));
    assert_eq!(rm("2015-09-07blah"), Done("blah", "2015-09-07"));
  }

  #[test]
  fn re_matches() {
    named!(rm< &str,Vec<&str> >, re_matches!(r"\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", vec!["2015-09-07"]));
    assert_eq!(rm("blah"), Error(error_code!(ErrorKind::RegexpMatches)));
    assert_eq!(rm("aaa2015-09-07blah2015-09-09pouet"), Done("pouet", vec!["2015-09-07", "2015-09-09"]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_matches_static() {
    named!(rm< &str,Vec<&str> >, re_matches_static!(r"\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", vec!["2015-09-07"]));
    assert_eq!(rm("blah"), Error(error_code!(ErrorKind::RegexpMatches)));
    assert_eq!(rm("aaa2015-09-07blah2015-09-09pouet"), Done("pouet", vec!["2015-09-07", "2015-09-09"]));
  }

  #[test]
  fn re_capture() {
    named!(rm< &str,Vec<&str> >, re_capture!(r"([[:alpha:]]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm("blah nom 0.3.11pouet"), Done("pouet", vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]));
    assert_eq!(rm("blah"), Error(error_code!(ErrorKind::RegexpCapture)));
    assert_eq!(rm("hello nom 0.3.11 world regex 0.1.41"), Done(" world regex 0.1.41", vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_capture_static() {
    named!(rm< &str,Vec<&str> >, re_capture_static!(r"([[:alpha:]]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm("blah nom 0.3.11pouet"), Done("pouet", vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]));
    assert_eq!(rm("blah"), Error(error_code!(ErrorKind::RegexpCapture)));
    assert_eq!(rm("hello nom 0.3.11 world regex 0.1.41"), Done(" world regex 0.1.41", vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]));
  }

  #[test]
  fn re_captures() {
    named!(rm< &str,Vec<Vec<&str>> >, re_captures!(r"([[:alpha:]]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm("blah nom 0.3.11pouet"), Done("pouet", vec![vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]]));
    assert_eq!(rm("blah"), Error(error_code!(ErrorKind::RegexpCapture)));
    assert_eq!(rm("hello nom 0.3.11 world regex 0.1.41 aaa"), Done(" aaa", vec![
     vec!["nom 0.3.11",   "nom",   "0.3.11", "0", "3", "11"],
     vec!["regex 0.1.41", "regex", "0.1.41", "0", "1", "41"],
    ]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_captures_static() {
    named!(rm< &str,Vec<Vec<&str>> >, re_captures_static!(r"([[:alpha:]]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm("blah nom 0.3.11pouet"), Done("pouet", vec![vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]]));
    assert_eq!(rm("blah"), Error(error_code!(ErrorKind::RegexpCapture)));
    assert_eq!(rm("hello nom 0.3.11 world regex 0.1.41 aaa"), Done(" aaa", vec![
     vec!["nom 0.3.11",   "nom",   "0.3.11", "0", "3", "11"],
     vec!["regex 0.1.41", "regex", "0.1.41", "0", "1", "41"],
    ]));
  }

  #[test]
  fn re_bytes_match() {
    named!(rm, re_bytes_match!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm(&b"2015-09-07"[..]), Done(&b""[..], &b"2015-09-07"[..]));
    assert_eq!(rm(&b"blah"[..]), Error(error_code!(ErrorKind::RegexpMatch)));
    assert_eq!(rm(&b"2015-09-07blah"[..]), Done(&b""[..], &b"2015-09-07blah"[..]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_bytes_match_static() {
    named!(rm, re_bytes_match_static!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm(&b"2015-09-07"[..]), Done(&b""[..], &b"2015-09-07"[..]));
    assert_eq!(rm(&b"blah"[..]), Error(error_code!(ErrorKind::RegexpMatch)));
    assert_eq!(rm(&b"2015-09-07blah"[..]), Done(&b""[..], &b"2015-09-07blah"[..]));
  }

  #[test]
  fn re_bytes_find() {
    named!(rm, re_bytes_find!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm(&b"2015-09-07"[..]), Done(&b""[..], &b"2015-09-07"[..]));
    assert_eq!(rm(&b"blah"[..]), Error(error_code!(ErrorKind::RegexpFind)));
    assert_eq!(rm(&b"2015-09-07blah"[..]), Done(&b"blah"[..], &b"2015-09-07"[..]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_bytes_find_static() {
    named!(rm, re_bytes_find_static!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm(&b"2015-09-07"[..]), Done(&b""[..], &b"2015-09-07"[..]));
    assert_eq!(rm(&b"blah"[..]), Error(error_code!(ErrorKind::RegexpFind)));
    assert_eq!(rm(&b"2015-09-07blah"[..]), Done(&b"blah"[..], &b"2015-09-07"[..]));
  }

  #[test]
  fn re_bytes_matches() {
    named!(rm<Vec<&[u8]> >, re_bytes_matches!(r"\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm(&b"2015-09-07"[..]), Done(&b""[..], vec![&b"2015-09-07"[..]]));
    assert_eq!(rm(&b"blah"[..]), Error(error_code!(ErrorKind::RegexpMatches)));
    assert_eq!(rm(&b"aaa2015-09-07blah2015-09-09pouet"[..]), Done(&b"pouet"[..], vec![&b"2015-09-07"[..], &b"2015-09-09"[..]]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_bytes_matches_static() {
    named!(rm<Vec<&[u8]> >, re_bytes_matches_static!(r"\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm(&b"2015-09-07"[..]), Done(&b""[..], vec![&b"2015-09-07"[..]]));
    assert_eq!(rm(&b"blah"[..]), Error(error_code!(ErrorKind::RegexpMatches)));
    assert_eq!(rm(&b"aaa2015-09-07blah2015-09-09pouet"[..]), Done(&b"pouet"[..], vec![&b"2015-09-07"[..], &b"2015-09-09"[..]]));
  }

  #[test]
  fn re_bytes_capture() {
    named!(rm<Vec<&[u8]> >, re_bytes_capture!(r"([[:alpha:]]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm(&b"blah nom 0.3.11pouet"[..]), Done(&b"pouet"[..], vec![&b"nom 0.3.11"[..], &b"nom"[..], &b"0.3.11"[..], &b"0"[..], &b"3"[..], &b"11"[..]]));
    assert_eq!(rm(&b"blah"[..]), Error(error_code!(ErrorKind::RegexpCapture)));
    assert_eq!(rm(&b"hello nom 0.3.11 world regex 0.1.41"[..]), Done(&b" world regex 0.1.41"[..], vec![&b"nom 0.3.11"[..], &b"nom"[..], &b"0.3.11"[..], &b"0"[..], &b"3"[..], &b"11"[..]]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_bytes_capture_static() {
    named!(rm< Vec<&[u8]> >, re_bytes_capture_static!(r"([[:alpha:]]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm(&b"blah nom 0.3.11pouet"[..]), Done(&b"pouet"[..], vec![&b"nom 0.3.11"[..], &b"nom"[..], &b"0.3.11"[..], &b"0"[..], &b"3"[..], &b"11"[..]]));
    assert_eq!(rm(&b"blah"[..]), Error(error_code!(ErrorKind::RegexpCapture)));
    assert_eq!(rm(&b"hello nom 0.3.11 world regex 0.1.41"[..]), Done(&b" world regex 0.1.41"[..], vec![&b"nom 0.3.11"[..], &b"nom"[..], &b"0.3.11"[..], &b"0"[..], &b"3"[..], &b"11"[..]]));
  }

  #[test]
  fn re_bytes_captures() {
    named!(rm< Vec<Vec<&[u8]>> >, re_bytes_captures!(r"([[:alpha:]]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm(&b"blah nom 0.3.11pouet"[..]), Done(&b"pouet"[..], vec![vec![&b"nom 0.3.11"[..], &b"nom"[..], &b"0.3.11"[..], &b"0"[..], &b"3"[..], &b"11"[..]]]));
    assert_eq!(rm(&b"blah"[..]), Error(error_code!(ErrorKind::RegexpCapture)));
    assert_eq!(rm(&b"hello nom 0.3.11 world regex 0.1.41 aaa"[..]), Done(&b" aaa"[..], vec![
     vec![&b"nom 0.3.11"[..],   &b"nom"[..],   &b"0.3.11"[..], &b"0"[..], &b"3"[..], &b"11"[..]],
     vec![&b"regex 0.1.41"[..], &b"regex"[..], &b"0.1.41"[..], &b"0"[..], &b"1"[..], &b"41"[..]],
    ]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_bytes_captures_static() {
    named!(rm< Vec<Vec<&[u8]>> >, re_bytes_captures_static!(r"([[:alpha:]]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm(&b"blah nom 0.3.11pouet"[..]), Done(&b"pouet"[..], vec![vec![&b"nom 0.3.11"[..], &b"nom"[..], &b"0.3.11"[..], &b"0"[..], &b"3"[..], &b"11"[..]]]));
    assert_eq!(rm(&b"blah"[..]), Error(error_code!(ErrorKind::RegexpCapture)));
    assert_eq!(rm(&b"hello nom 0.3.11 world regex 0.1.41 aaa"[..]), Done(&b" aaa"[..], vec![
     vec![&b"nom 0.3.11"[..],   &b"nom"[..],   &b"0.3.11"[..], &b"0"[..], &b"3"[..], &b"11"[..]],
     vec![&b"regex 0.1.41"[..], &b"regex"[..], &b"0.1.41"[..], &b"0"[..], &b"1"[..], &b"41"[..]],
    ]));
  }
}
