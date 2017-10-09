//! Parsers and helper functions operating on strings, especially useful when writing parsers for
//! text-based formats.

/// `tag_s!(&str) => &str -> IResult<&str, &str>`
/// declares a string as a suite to recognize
///
/// consumes the recognized characters
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self,Done};
/// # fn main() {
///  fn test(input: &str) -> IResult<&str, &str> {
///    tag_s!(input, "abcd")
///  }
///  let r = test("abcdefgh");
///  assert_eq!(r, Done("efgh", "abcd"));
/// # }
/// ```
#[macro_export]
macro_rules! tag_s (
  ($i:expr, $tag: expr) => (
    {
      tag!($i, $tag)
    }
  );
);

/// `tag_no_case_s!(&str) => &str -> IResult<&str, &str>`
/// declares a case-insensitive string as a suite to recognize
///
/// consumes the recognized characters
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::{self,Done};
/// # fn main() {
///  fn test(input: &str) -> IResult<&str, &str> {
///    tag_no_case_s!(input, "ABcd")
///  }
///  let r = test("aBCdefgh");
///  assert_eq!(r, Done("efgh", "aBCd"));
/// # }
/// ```
#[macro_export]
macro_rules! tag_no_case_s (
  ($i:expr, $tag: expr) => (
    {
      tag_no_case!($i, $tag)
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
///
///  let b = "12345";
///
///  assert_eq!(take5(b), Done("", "12345"));
/// # }
/// ```
#[macro_export]
macro_rules! take_s (
  ($i:expr, $count:expr) => (
    {
      let input = $i;
      let cnt = $count as usize;
      take!(input, cnt)
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
      is_not!($input, $arr)
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
      is_a!($input, $arr)
    }
  );
);


/// `take_while_s!(char -> bool) => &str -> IResult<&str, &str>`
/// returns the longest list of characters until the provided function fails.
///
/// The argument is either a function `char -> bool` or a macro returning a `bool
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # use nom::is_alphanumeric;
/// # fn main() {
///  fn alphabetic(chr: char) -> bool { (chr >= 0x41 as char && chr <= 0x5A as char) || (chr >= 0x61 as char && chr <= 0x7A as char) }
///  named!( alpha<&str,&str>, take_while_s!( alphabetic ) );
///
///  let r = alpha("abcd\nefgh");
///  assert_eq!(r, Done("\nefgh", "abcd"));
/// # }
/// ```
#[macro_export]
macro_rules! take_while_s (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      take_while!($input, $submac!($($args)*))
    }
  );
  ($input:expr, $f:expr) => (
    take_while_s!($input, call!($f));
  );
);

/// `take_while1_s!(char -> bool) => &str -> IResult<&str, &str>`
/// returns the longest (non empty) list of characters until the provided function fails.
///
/// The argument is either a function `char -> bool` or a macro returning a `bool`
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult::Done;
/// # use nom::is_alphanumeric;
/// # fn main() {
///  fn alphabetic(chr: char) -> bool { (chr >= 0x41 as char && chr <= 0x5A as char) || (chr >= 0x61 as char && chr <= 0x7A as char) }
///  named!( alpha<&str,&str>, take_while1_s!( alphabetic ) );
///
///  let r = alpha("abcd\nefgh");
///  assert_eq!(r, Done("\nefgh", "abcd"));
/// # }
/// ```
#[macro_export]
macro_rules! take_while1_s (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    take_while1!($input, $submac!($($args)*))
  );
  ($input:expr, $f:expr) => (
    take_while1_s!($input, call!($f));
  );
);


/// `take_till_s!(char -> bool) => &str -> IResult<&str, &str>`
/// returns the longest list of characters until the provided function succeeds
///
/// The argument is either a function `char -> bool` or a macro returning a `bool
#[macro_export]
macro_rules! take_till_s (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      take_till!($input, $submac!($($args)*))
    }
  );
  ($input:expr, $f:expr) => (
    take_till_s!($input, call!($f));
  );
);

/// `take_till1_s!(char -> bool) => &str -> IResult<&str, &str>`
/// returns the longest non empty list of characters until the provided function succeeds
///
/// The argument is either a function `char -> bool` or a macro returning a `bool
#[macro_export]
macro_rules! take_till1_s (
  ($input:expr, $submac:ident!( $($args:tt)* )) => (
    {
      take_till1!($input, $submac!($($args)*))
    }
  );
  ($input:expr, $f:expr) => (
    take_till1_s!($input, call!($f));
  );
);

/// `take_until_and_consume_s!(&str) => &str -> IResult<&str, &str>`
/// generates a parser consuming all chars until the specified string is found and consumes it
#[macro_export]
macro_rules! take_until_and_consume_s (
  ($input:expr, $substr:expr) => (
    {
      take_until_and_consume!($input, $substr)
    }
  );
);

/// `take_until_s!(&str) => &str -> IResult<&str, &str>`
/// generates a parser consuming all chars until the specified string is found and leaves it in the remaining input
#[macro_export]
macro_rules! take_until_s (
  ($input:expr, $substr:expr) => (
    {
      take_until!($input, $substr)
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
          tag_s!(input, TAG)
        }

        match test(INPUT) {
            IResult::Done(extra, output) => {
                assert!(extra == " World!", "Parser `tag_s` consumed leftover input.");
                assert!(output == TAG,
                    "Parser `tag_s` doesn't return the tag it matched on success. \
                     Expected `{}`, got `{}`.", TAG, output);
            },
            other => panic!("Parser `tag_s` didn't succeed when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
    fn tag_str_incomplete() {
        const INPUT: &'static str = "Hello";
        const TAG: &'static str = "Hello World!";

        match tag_s!(INPUT, TAG) {
            IResult::Incomplete(_) => (),
            other => {
                panic!("Parser `tag_s` didn't require more input when it should have. \
                        Got `{:?}`.", other);
            }
        };
    }

    #[test]
    fn tag_str_error() {
        const INPUT: &'static str = "Hello World!";
        const TAG: &'static str = "Random"; // TAG must be closer than INPUT.

        match tag_s!(INPUT, TAG) {
            IResult::Error(_) => (),
            other => {
                panic!("Parser `tag_s` didn't fail when it should have. Got `{:?}`.`", other);
            },
        };
    }

    #[test]
    fn take_s_succeed() {
        const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
        const CONSUMED: &'static str = "βèƒôřèÂßÇ";
        const LEFTOVER: &'static str = "áƒƭèř";

        match take_s!(INPUT, 9) {
             IResult::Done(extra, output) => {
                assert!(extra == LEFTOVER, "Parser `take_s` consumed leftover input. Leftover `{}`.", extra);
                assert!(output == CONSUMED,
                    "Parser `take_s` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
                    CONSUMED, output);
            },
            other => panic!("Parser `take_s` didn't succeed when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
    fn take_until_s_succeed() {
        const INPUT: &'static str = "βèƒôřèÂßÇ∂áƒƭèř";
        const FIND: &'static str = "ÂßÇ∂";
        const CONSUMED: &'static str = "βèƒôřè";
        const LEFTOVER: &'static str = "ÂßÇ∂áƒƭèř";

        match take_until_s!(INPUT, FIND) {
            IResult::Done(extra, output) => {
                assert!(extra == LEFTOVER, "Parser `take_until_s`\
                  consumed leftover input. Leftover `{}`.", extra);
                assert!(output == CONSUMED, "Parser `take_until_s`\
                  doens't return the string it consumed on success. Expected `{}`, got `{}`.",
                  CONSUMED, output);
            }
            other => panic!("Parser `take_until_s` didn't succeed when it should have. \
             Got `{:?}`.", other),
        };
    }

    #[test]
    fn take_s_incomplete() {
        const INPUT: &'static str = "βèƒôřèÂßÇá";

        match take_s!(INPUT, 13) {
            IResult::Incomplete(_) => (),
            other => panic!("Parser `take_s` didn't require more input when it should have. \
                             Got `{:?}`.", other),
        }
    }

  use internal::IResult::{Done, Error, Incomplete};
  use internal::Needed;
  use util::ErrorKind;

  pub fn is_alphabetic(c:char) -> bool {
    (c as u8 >= 0x41 && c as u8 <= 0x5A) || (c as u8 >= 0x61 && c as u8 <= 0x7A)
  }
  #[test]
  fn take_while_s() {
    named!(f<&str,&str>, take_while_s!(is_alphabetic));
    let a = "";
    let b = "abcd";
    let c = "abcd123";
    let d = "123";

    assert_eq!(f(&a[..]), Done(&a[..], &a[..]));
    assert_eq!(f(&b[..]), Done(&a[..], &b[..]));
    assert_eq!(f(&c[..]), Done(&d[..], &b[..]));
    assert_eq!(f(&d[..]), Done(&d[..], &a[..]));
  }

  #[test]
  fn take_while1_s() {
    named!(f<&str,&str>, take_while1_s!(is_alphabetic));
    let a = "";
    let b = "abcd";
    let c = "abcd123";
    let d = "123";

    assert_eq!(f(&a[..]), Incomplete(Needed::Size(1)));
    assert_eq!(f(&b[..]), Done(&a[..], &b[..]));
    assert_eq!(f(&c[..]), Done(&"123"[..], &b[..]));
    assert_eq!(f(&d[..]), Error(error_position!(ErrorKind::TakeWhile1, &d[..])));
  }

  #[test]
  fn take_till_s_succeed() {
    const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
    const CONSUMED: &'static str = "βèƒôřèÂßÇ";
    const LEFTOVER: &'static str = "áƒƭèř";
    fn till_s(c: char) -> bool {
      c == 'á'
    }
    fn test(input: &str) -> IResult<&str, &str> {
      take_till_s!(input, till_s)
    }
    match test(INPUT) {
      IResult::Done(extra, output) => {
        assert!(extra == LEFTOVER, "Parser `take_till_s` consumed leftover input.");
        assert!(output == CONSUMED,
        "Parser `take_till_s` doesn't return the string it consumed on success. \
                     Expected `{}`, got `{}`.", CONSUMED, output);
      },
      other => panic!("Parser `take_till_s` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    };
  }

  #[test]
  fn take_while_s_succeed_none() {
    const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
    const CONSUMED: &'static str = "";
    const LEFTOVER: &'static str = "βèƒôřèÂßÇáƒƭèř";
    fn while_s(c: char) -> bool {
      c == '9'
    }
    fn test(input: &str) -> IResult<&str, &str> {
      take_while_s!(input, while_s)
    }
    match test(INPUT) {
      IResult::Done(extra, output) => {
        assert!(extra == LEFTOVER, "Parser `take_while_s` consumed leftover input.");
        assert!(output == CONSUMED,
        "Parser `take_while_s` doesn't return the string it consumed on success. \
                     Expected `{}`, got `{}`.", CONSUMED, output);
      },
      other => panic!("Parser `take_while_s` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    };
  }

  #[test]
  fn is_not_s_succeed() {
    const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
    const AVOID: &'static str = "£úçƙ¥á";
    const CONSUMED: &'static str = "βèƒôřèÂßÇ";
    const LEFTOVER: &'static str = "áƒƭèř";
    fn test(input: &str) -> IResult<&str, &str> {
      is_not_s!(input, AVOID)
    }
    match test(INPUT) {
      IResult::Done(extra, output) => {
        assert!(extra == LEFTOVER, "Parser `is_not_s` consumed leftover input. Leftover `{}`.", extra);
        assert!(output == CONSUMED,
        "Parser `is_not_s` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
        CONSUMED, output);
      },
      other => panic!("Parser `is_not_s` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    };
  }

  #[test]
  fn take_until_and_consume_s_succeed() {
    const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
    const FIND: &'static str = "ÂßÇ";
    const OUTPUT: &'static str = "βèƒôřè";
    const LEFTOVER: &'static str = "áƒƭèř";

    match take_until_and_consume_s!(INPUT, FIND) {
      IResult::Done(extra, output) => {
        assert!(extra == LEFTOVER, "Parser `take_until_and_consume_s`\
                    consumed leftover input. Leftover `{}`.", extra);
        assert!(output == OUTPUT, "Parser `take_until_and_consume_s`\
                    doens't return the string it selected on success. Expected `{}`, got `{}`.",
                    OUTPUT, output);
      }
      other => panic!("Parser `take_until_and_consume_s` didn't succeed when it should have. \
                             Got `{:?}`.", other),
    };
  }

    #[test]
    fn take_while_s_succeed_some() {
        const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
        const CONSUMED: &'static str = "βèƒôřèÂßÇ";
        const LEFTOVER: &'static str = "áƒƭèř";
        fn while_s(c: char) -> bool {
            c == 'β' || c == 'è' || c == 'ƒ' || c == 'ô' || c == 'ř' ||
            c == 'è' || c == 'Â' || c == 'ß' || c == 'Ç'
        }
        fn test(input: &str) -> IResult<&str, &str> {
          take_while_s!(input, while_s)
        }
        match test(INPUT) {
            IResult::Done(extra, output) => {
                assert!(extra == LEFTOVER, "Parser `take_while_s` consumed leftover input.");
                assert!(output == CONSUMED,
                    "Parser `take_while_s` doesn't return the string it consumed on success. \
                     Expected `{}`, got `{}`.", CONSUMED, output);
            },
            other => panic!("Parser `take_while_s` didn't succeed when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
    fn is_not_s_fail() {
        const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
        const AVOID: &'static str = "βúçƙ¥";
        fn test(input: &str) -> IResult<&str, &str> {
            is_not_s!(input, AVOID)
        }
        match test(INPUT) {
            IResult::Error(_) => (),
            other => panic!("Parser `is_not_s` didn't fail when it should have. Got `{:?}`.", other),
        };
    }

    #[test]
    fn take_while1_s_succeed() {
        const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
        const CONSUMED: &'static str = "βèƒôřèÂßÇ";
        const LEFTOVER: &'static str = "áƒƭèř";
        fn while1_s(c: char) -> bool {
            c == 'β' || c == 'è' || c == 'ƒ' || c == 'ô' || c == 'ř' ||
            c == 'è' || c == 'Â' || c == 'ß' || c == 'Ç'
        }
        fn test(input: &str) -> IResult<&str, &str> {
          take_while1_s!(input, while1_s)
        }
        match test(INPUT) {
            IResult::Done(extra, output) => {
                assert!(extra == LEFTOVER, "Parser `take_while1_s` consumed leftover input.");
                assert!(output == CONSUMED,
                    "Parser `take_while1_s` doesn't return the string it consumed on success. \
                     Expected `{}`, got `{}`.", CONSUMED, output);
            },
            other => panic!("Parser `take_while1_s` didn't succeed when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
    fn take_until_and_consume_s_incomplete() {
        const INPUT: &'static str = "βèƒôřè";
        const FIND: &'static str = "βèƒôřèÂßÇ";

        match take_until_and_consume_s!(INPUT, FIND) {
            IResult::Incomplete(_) => (),
            other => panic!("Parser `take_until_and_consume_s` didn't require more input when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
    fn take_until_s_incomplete() {
        const INPUT: &'static str = "βèƒôřè";
        const FIND: &'static str = "βèƒôřèÂßÇ";

        match take_until_s!(INPUT, FIND) {
            IResult::Incomplete(_) => (),
            other => panic!("Parser `take_until_s` didn't require more input when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
    fn is_a_s_succeed() {
        const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
        const MATCH: &'static str = "βèƒôřèÂßÇ";
        const CONSUMED: &'static str = "βèƒôřèÂßÇ";
        const LEFTOVER: &'static str = "áƒƭèř";
        fn test(input: &str) -> IResult<&str, &str> {
            is_a_s!(input, MATCH)
        }
        match test(INPUT) {
             IResult::Done(extra, output) => {
                assert!(extra == LEFTOVER, "Parser `is_a_s` consumed leftover input. Leftover `{}`.", extra);
                assert!(output == CONSUMED,
                    "Parser `is_a_s` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
                    CONSUMED, output);
            },
            other => panic!("Parser `is_a_s` didn't succeed when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
    fn take_while1_s_fail() {
        const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
        fn while1_s(c: char) -> bool {
            c == '9'
        }
        fn test(input: &str) -> IResult<&str, &str> {
          take_while1_s!(input, while1_s)
        }
        match test(INPUT) {
            IResult::Error(_) => (),
            other => panic!("Parser `take_while1_s` didn't fail when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
    fn is_a_s_fail() {
        const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
        const MATCH: &'static str = "Ûñℓúçƙ¥";
        fn test(input: &str) -> IResult<&str, &str> {
            is_a_s!(input, MATCH)
        }
        match test(INPUT) {
            IResult::Error(_) => (),
            other => panic!("Parser `is_a_s` didn't fail when it should have. Got `{:?}`.", other),
        };
    }

    #[test]
    fn take_until_and_consume_s_error() {
        const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
        const FIND: &'static str = "Ráñδô₥";

        match take_until_and_consume_s!(INPUT, FIND) {
            IResult::Error(_) => (),
            other => panic!("Parser `take_until_and_consume_s` didn't fail when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
    fn take_until_s_error() {
        const INPUT: &'static str = "βèƒôřèÂßÇáƒƭèř";
        const FIND: &'static str = "Ráñδô₥";

        match take_until_s!(INPUT, FIND) {
            IResult::Error(_) => (),
            other => panic!("Parser `take_until_and_consume_s` didn't fail when it should have. \
                             Got `{:?}`.", other),
        };
    }

    #[test]
  #[cfg(feature = "std")]
    fn recognize_is_a_s() {
    let a = "aabbab";
    let b = "ababcd";

    named!(f <&str,&str>, recognize!(many1!(alt!( tag_s!("a") | tag_s!("b") ))));

    assert_eq!(f(&a[..]), Done(&a[6..], &a[..]));
    assert_eq!(f(&b[..]), Done(&b[4..], &b[..4]));

    }

    #[test]
    fn utf8_indexing() {
      named!(dot(&str) -> &str,
        tag_s!(".")
      );

      dot("點");
    }

  #[test]
  fn case_insensitive() {
    named!(test<&str,&str>, tag_no_case!("ABcd"));
    assert_eq!(test("aBCdefgh"), Done("efgh", "aBCd"));
    assert_eq!(test("abcdefgh"), Done("efgh", "abcd"));
    assert_eq!(test("ABCDefgh"), Done("efgh", "ABCD"));

    named!(test2<&str,&str>, tag_no_case!("ABcd"));
    assert_eq!(test2("aBCdefgh"), Done("efgh", "aBCd"));
    assert_eq!(test2("abcdefgh"), Done("efgh", "abcd"));
    assert_eq!(test2("ABCDefgh"), Done("efgh", "ABCD"));
  }
}
