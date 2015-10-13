/// `re_match!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the whole input if a match is found
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_match (
  ($i:expr, $re:expr) => (
    {
      let re = ::regex::Regex::new($re).unwrap();
      if re.is_match($i) {
        $crate::IResult::Done(&""[..], $i)
      } else {
        $crate::IResult::Error($crate::Err::Code($crate::ErrorCode::RegexpMatch as u32))
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
      let re = regex!($re);
      if re.is_match($i) {
        $crate::IResult::Done(&""[..], $i)
      } else {
        $crate::IResult::Error($crate::Err::Code($crate::ErrorCode::RegexpMatch as u32))
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
      let re = ::regex::Regex::new($re).unwrap();
      if let Some((begin, end)) = re.find($i) {
        $crate::IResult::Done(&$i[end..], &$i[begin..end])
      } else {
        $crate::IResult::Error($crate::Err::Code($crate::ErrorCode::RegexpFind as u32))
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_find!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the first match. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_find_static (
  ($i:expr, $re:expr) => (
    {
      let re = regex!($re);
      if let Some((begin, end)) = re.find($i) {
        $crate::IResult::Done(&$i[end..], &$i[begin..end])
      } else {
        $crate::IResult::Error($crate::Err::Code($crate::ErrorCode::RegexpFind as u32))
      }
    }

  )
);

/// `re_matches!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns all the matched parts
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_matches (
  ($i:expr, $re:expr) => (
    {
      let re = ::regex::Regex::new($re).unwrap();
      let v: Vec<&str> = re.find_iter($i).map(|(begin,end)| &$i[begin..end]).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done(&$i[offset..], v)
      } else {
        $crate::IResult::Error($crate::Err::Code($crate::ErrorCode::RegexpMatches as u32))
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_matches!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns all the matched parts. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_matches_static (
  ($i:expr, $re:expr) => (
    {
      let re = regex!($re);
      let v: Vec<&str> = re.find_iter($i).map(|(begin,end)| &$i[begin..end]).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done(&$i[offset..], v)
      } else {
        $crate::IResult::Error($crate::Err::Code($crate::ErrorCode::RegexpMatches as u32))
      }
    }
  )
);

/// `re_capture!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the first capture group
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_capture (
  ($i:expr, $re:expr) => (
    {
      let re = ::regex::Regex::new($re).unwrap();
      if let Some(c) = re.captures($i) {
        let v:Vec<&str> = c.iter_pos().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|(begin,end)| &$i[begin..end]).collect();
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done(&$i[offset..], v)
      } else {
        $crate::IResult::Error($crate::Err::Code($crate::ErrorCode::RegexpCapture as u32))
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_capture!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns the first capture group. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_capture_static (
  ($i:expr, $re:expr) => (
    {
      let re = regex!($re);
      if let Some(c) = re.captures($i) {
        let v:Vec<&str> = c.iter_pos().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|(begin,end)| &$i[begin..end]).collect();
        let offset = {
          let end = v.last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done(&$i[offset..], v)
      } else {
        $crate::IResult::Error($crate::Err::Code($crate::ErrorCode::RegexpCapture as u32))
      }
    }
  )
);

/// `re_captures!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns all the capture groups
///
/// requires the `regexp` feature
#[macro_export]
macro_rules! re_captures (
  ($i:expr, $re:expr) => (
    {
      let re = ::regex::Regex::new($re).unwrap();
      let v:Vec<Vec<&str>> = re.captures_iter($i).map(|c| c.iter_pos().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|(begin,end)| &$i[begin..end]).collect()).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap().last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done(&$i[offset..], v)
      } else {
        $crate::IResult::Error($crate::Err::Code($crate::ErrorCode::RegexpCapture as u32))
      }
    }
  )
);

#[cfg(feature = "regexp_macros")]
/// `re_captures!(regexp) => &[T] -> IResult<&[T], &[T]>`
/// Returns all the capture groups. Regular expression calculated at compile time
///
/// requires the `regexp_macros` feature
#[macro_export]
macro_rules! re_captures_static (
  ($i:expr, $re:expr) => (
    {
      let re = regex!($re);
      let v:Vec<Vec<&str>> = re.captures_iter($i).map(|c| c.iter_pos().filter(|el| el.is_some()).map(|el| el.unwrap()).map(|(begin,end)| &$i[begin..end]).collect()).collect();
      if v.len() != 0 {
        let offset = {
          let end = v.last().unwrap().last().unwrap();
          end.as_ptr() as usize + end.len() - $i.as_ptr() as usize
        };
        $crate::IResult::Done(&$i[offset..], v)
      } else {
        $crate::IResult::Error($crate::Err::Code($crate::ErrorCode::RegexpCapture as u32))
      }
    }
  )
);

#[cfg(test)]
mod tests {
  use internal::IResult::*;
  use internal::Err::*;
  use util::ErrorCode;

  #[test]
  fn re_match() {
    named!(rm<&str,&str>, re_match!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", "2015-09-07"));
    assert_eq!(rm("blah"), Error(Code(ErrorCode::RegexpMatch as u32)));
    assert_eq!(rm("2015-09-07blah"), Done("", "2015-09-07blah"));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_match_static() {
    named!(rm<&str,&str>, re_match_static!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", "2015-09-07"));
    assert_eq!(rm("blah"), Error(Code(ErrorCode::RegexpMatch as u32)));
    assert_eq!(rm("2015-09-07blah"), Done("", "2015-09-07blah"));
  }

  #[test]
  fn re_find() {
    named!(rm<&str,&str>, re_find!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", "2015-09-07"));
    assert_eq!(rm("blah"), Error(Code(ErrorCode::RegexpFind as u32)));
    assert_eq!(rm("2015-09-07blah"), Done("blah", "2015-09-07"));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_find_static() {
    named!(rm<&str,&str>, re_find_static!(r"^\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", "2015-09-07"));
    assert_eq!(rm("blah"), Error(Code(ErrorCode::RegexpFind as u32)));
    assert_eq!(rm("2015-09-07blah"), Done("blah", "2015-09-07"));
  }

  #[test]
  fn re_matches() {
    named!(rm< &str,Vec<&str> >, re_matches!(r"\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", vec!["2015-09-07"]));
    assert_eq!(rm("blah"), Error(Code(ErrorCode::RegexpMatches as u32)));
    assert_eq!(rm("aaa2015-09-07blah2015-09-09pouet"), Done("pouet", vec!["2015-09-07", "2015-09-09"]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_matches_static() {
    named!(rm< &str,Vec<&str> >, re_matches_static!(r"\d{4}-\d{2}-\d{2}"));
    assert_eq!(rm("2015-09-07"), Done("", vec!["2015-09-07"]));
    assert_eq!(rm("blah"), Error(Code(ErrorCode::RegexpMatches as u32)));
    assert_eq!(rm("aaa2015-09-07blah2015-09-09pouet"), Done("pouet", vec!["2015-09-07", "2015-09-09"]));
  }

  #[test]
  fn re_capture() {
    named!(rm< &str,Vec<&str> >, re_capture!(r"([:alpha:]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm("blah nom 0.3.11pouet"), Done("pouet", vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]));
    assert_eq!(rm("blah"), Error(Code(ErrorCode::RegexpCapture as u32)));
    assert_eq!(rm("hello nom 0.3.11 world regex 0.1.41"), Done(" world regex 0.1.41", vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_capture_static() {
    named!(rm< &str,Vec<&str> >, re_capture_static!(r"([:alpha:]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm("blah nom 0.3.11pouet"), Done("pouet", vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]));
    assert_eq!(rm("blah"), Error(Code(ErrorCode::RegexpCapture as u32)));
    assert_eq!(rm("hello nom 0.3.11 world regex 0.1.41"), Done(" world regex 0.1.41", vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]));
  }

  #[test]
  fn re_captures() {
    named!(rm< &str,Vec<Vec<&str>> >, re_captures!(r"([:alpha:]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm("blah nom 0.3.11pouet"), Done("pouet", vec![vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]]));
    assert_eq!(rm("blah"), Error(Code(ErrorCode::RegexpCapture as u32)));
    assert_eq!(rm("hello nom 0.3.11 world regex 0.1.41 aaa"), Done(" aaa", vec![
     vec!["nom 0.3.11",   "nom",   "0.3.11", "0", "3", "11"],
     vec!["regex 0.1.41", "regex", "0.1.41", "0", "1", "41"],
    ]));
  }

  #[cfg(feature = "regexp_macros")]
  #[test]
  fn re_captures_static() {
    named!(rm< &str,Vec<Vec<&str>> >, re_captures_static!(r"([:alpha:]+)\s+((\d+).(\d+).(\d+))"));
    assert_eq!(rm("blah nom 0.3.11pouet"), Done("pouet", vec![vec!["nom 0.3.11", "nom", "0.3.11", "0", "3", "11"]]));
    assert_eq!(rm("blah"), Error(Code(ErrorCode::RegexpCapture as u32)));
    assert_eq!(rm("hello nom 0.3.11 world regex 0.1.41 aaa"), Done(" aaa", vec![
     vec!["nom 0.3.11",   "nom",   "0.3.11", "0", "3", "11"],
     vec!["regex 0.1.41", "regex", "0.1.41", "0", "1", "41"],
    ]));
  }

}
