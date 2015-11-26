//! Parsers and helper functions operating on strings, especially useful when writing parsers for
//! text-based formats.

/// `tag_str!(&str) => &str -> IResult<&str, &str>`
/// declares a string as a suite to recognize
///
/// consumes the recognized characters
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self,Done};
/// # fn main() {
///  fn test(input: &str) -> IResult<&str, &str> {
///    tag_str!(input, "abcd")
///  }
///  let r = test("abcdefgh");
///  assert_eq!(r, Done("efgh", "abcd"));
/// # }
/// ```
#[macro_export]
macro_rules! tag_str (
  ($i:expr, $tag: expr) => (
    {
      let res: $crate::IResult<&str,&str> = if $tag.len() > $i.len() {
        $crate::IResult::Incomplete($crate::Needed::Size($tag.len()))
      //} else if &$i[0..$tag.len()] == $tag {
      } else if ($i).starts_with($tag) {
        $crate::IResult::Done(&$i[$tag.len()..], &$i[0..$tag.len()])
      } else {
        $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::TagStr, $i))
      };
      res
    }
  );
);

/// `take_s!(nb) => &str -> IResult<&str, &str>`
/// generates a parser consuming the specified number of characters
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  // Desmond parser
///  named!(take5<&str,&str>, take_s!( 5 ) );
///
///  let a = "abcdefgh";
///
///  assert_eq!(take5(a), Done("fgh", "abcde"));
/// # }
/// ```
#[macro_export]
macro_rules! take_s (
  ($i:expr, $count:expr) => (
    {
      let cnt = $count as usize;
      let res: $crate::IResult<&str,&str> = if $i.len() < cnt {
        $crate::IResult::Incomplete($crate::Needed::Size(cnt))
      } else {
        $crate::IResult::Done(&$i[cnt..],&$i[0..cnt])
      };
      res
    }
  );
);

/// `is_not_s!(&str) => &str -> IResult<&str, &str>`
/// returns the longest list of characters that do not appear in the provided array
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!( not_space<&str,&str>, is_not_s!( " \t\r\n" ) );
///
///  let r = not_space("abcdefgh\nijkl");
///  assert_eq!(r, Done("\nijkl", "abcdefgh"));
///  # }
/// ```
#[macro_export]
macro_rules! is_not_s (
  ($input:expr, $arr:expr) => (
    {
      let res: $crate::IResult<&str,&str> = match $input.chars().position(|c| {
        for i in $arr.chars() {
          if c == i { return true }
        }
        false
      }) {
        Some(0) => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::IsNotStr,$input)),
        Some(n) => {
          let res = $crate::IResult::Done(&$input[n..], &$input[..n]);
          res
        },
        None    => {
          $crate::IResult::Done("", $input)
        }
      };
      res
    }
  );
);

/// `is_a_s!(&str) => &str -> IResult<&str, &str>`
/// returns the longest list of characters that appear in the provided array
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # fn main() {
///  named!(abcd<&str, &str>, is_a_s!( "abcd" ));
///
///  let r1 = abcd("aaaaefgh");
///  assert_eq!(r1, Done("efgh", "aaaa"));
///
///  let r2 = abcd("dcbaefgh");
///  assert_eq!(r2, Done("efgh", "dcba"));
/// # }
/// ```
#[macro_export]
macro_rules! is_a_s (
  ($input:expr, $arr:expr) => (
    {
      let res: $crate::IResult<&str,&str> = match $input.chars().position(|c| {
        for i in $arr.chars() {
          if c == i { return false }
        }
        true
      }) {
        Some(0) => $crate::IResult::Error($crate::Err::Position($crate::ErrorKind::IsAStr,$input)),
        Some(n) => {
          let res: $crate::IResult<&str,&str> = $crate::IResult::Done(&$input[n..], &$input[..n]);
          res
        },
        None    => {
          $crate::IResult::Done("", $input)
        }
      };
      res
    }
  );
);

#[cfg(test)]
mod test {
    use ::IResult;

    #[test]
    fn tag_str_succeed() {
        const INPUT: &'static str = "Hello World!";
        const TAG: &'static str = "Hello";
        fn test(input: &str) -> IResult<&str, &str> {
          tag_str!(input, TAG)
        }

        match test(INPUT) {
            IResult::Done(extra, output) => {
                assert!(extra == " World!", "Parser `tag_str` consumed leftover input.");
                assert!(output == TAG,
                    "Parser `tag_str` doesn't return the tag it matched on success. \
                     Expected `{}`, got `{}`.", TAG, output);
            },
            other => panic!("Parser `tag_str` didn't succeed when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
    fn tag_str_incomplete() {
        const INPUT: &'static str = "Hello";
        const TAG: &'static str = "Hello World!";

        match tag_str!(INPUT, TAG) {
            IResult::Incomplete(_) => (),
            other => {
                panic!("Parser `tag_str` didn't require more input when it should have. \
                        Got `{:?}`.", other);
            }
        };
    }

    #[test]
    fn tag_str_error() {
        const INPUT: &'static str = "Hello World!";
        const TAG: &'static str = "Random"; // TAG must be closer than INPUT.

        match tag_str!(INPUT, TAG) {
            IResult::Error(_) => (),
            other => {
                panic!("Parser `tag_str` didn't fail when it should have. Got `{:?}`.`", other);
            },
        };
    }
}
