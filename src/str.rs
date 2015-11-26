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
