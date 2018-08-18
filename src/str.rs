//! Parsers and helper functions operating on strings, especially useful when writing parsers for
//! text-based formats.

/// `tag_s!(&str) => &str -> IResult<&str, &str>`
/// declares a string as a suite to recognize
///
/// consumes the recognized characters
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::IResult;
/// # fn main() {
///  fn test(input: &str) -> IResult<&str, &str> {
///    tag_s!(input, "abcd")
///  }
///  let r = test("abcdefgh");
///  assert_eq!(r,Ok(("efgh", "abcd")));
/// # }
/// ```
#[macro_export]
#[deprecated(since = "4.0.0", note = "Please use `tag` instead")]
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
/// # use nom::IResult;
/// # use nom::InputLength;
/// #[cfg(feature = "alloc")]
/// # fn main() {
///  fn test(input: &str) -> IResult<&str, &str> {
///    tag_no_case_s!(input, "ABcd")
///  }
///  let r = test("aBCdefgh");
///  assert_eq!(r,Ok(("efgh", "aBCd")));
/// # }
/// # #[cfg(not(feature = "alloc"))]
/// # fn main() {}
/// ```
#[macro_export]
#[deprecated(since = "4.0.0", note = "Please use `tag_no_case` instead")]
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
/// # fn main() {
///  // Desmond parser
///  named!(take5<&str,&str>, take_s!( 5 ) );
///
///  let a = "abcdefgh";
///
///  assert_eq!(take5(a),Ok(("fgh", "abcde")));
///
///  let b = "12345";
///
///  assert_eq!(take5(b),Ok(("", "12345")));
/// # }
/// ```
#[macro_export]
#[deprecated(since = "4.0.0", note = "Please use `take` instead")]
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
/// # fn main() {
///  named!( not_space<&str,&str>, is_not_s!( " \t\r\n" ) );
///
///  let r = not_space("abcdefgh\nijkl");
///  assert_eq!(r,Ok(("\nijkl", "abcdefgh")));
///  # }
/// ```
#[macro_export]
#[deprecated(since = "4.0.0", note = "Please use `is_not` instead")]
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
/// # fn main() {
///  named!(abcd<&str, &str>, is_a_s!( "abcd" ));
///
///  let r1 = abcd("aaaaefgh");
///  assert_eq!(r1,Ok(("efgh", "aaaa")));
///
///  let r2 = abcd("dcbaefgh");
///  assert_eq!(r2,Ok(("efgh", "dcba")));
/// # }
/// ```
#[macro_export]
#[deprecated(since = "4.0.0", note = "Please use `is_a` instead")]
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
/// # fn main() {
///  fn alphabetic(chr: char) -> bool { (chr >= 0x41 as char && chr <= 0x5A as char) || (chr >= 0x61 as char && chr <= 0x7A as char) }
///  named!( alpha<&str,&str>, take_while_s!( alphabetic ) );
///
///  let r = alpha("abcd\nefgh");
///  assert_eq!(r,Ok(("\nefgh", "abcd")));
/// # }
/// ```
#[macro_export]
#[deprecated(since = "4.0.0", note = "Please use `take_while` instead")]
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
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::is_alphanumeric;
/// # fn main() {
///  fn alphabetic(chr: char) -> bool { (chr >= 0x41 as char && chr <= 0x5A as char) || (chr >= 0x61 as char && chr <= 0x7A as char) }
///  named!( alpha<&str,&str>, take_while1_s!( alphabetic ) );
///
///  let r = alpha("abcd\nefgh");
///  assert_eq!(r, Ok(("\nefgh", "abcd")));
/// # }
/// ```
#[macro_export]
#[deprecated(since = "4.0.0", note = "Please use `take_while1` instead")]
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
#[deprecated(since = "4.0.0", note = "Please use `take_till` instead")]
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
#[deprecated(since = "4.0.0", note = "Please use `take_till1` instead")]
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
#[deprecated(since = "4.0.0", note = "Please use `take_until_and_consume` instead")]
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
#[deprecated(since = "4.0.0", note = "Please use `take_until` instead")]
macro_rules! take_until_s (
  ($input:expr, $substr:expr) => (
    {
      take_until!($input, $substr)
    }
  );
);

#[cfg(test)]
mod test {
  use {Err, ErrorKind, IResult};

  #[test]
  fn tag_str_succeed() {
    const INPUT: &str = "Hello World!";
    const TAG: &str = "Hello";
    fn test(input: &str) -> IResult<&str, &str> {
      tag_s!(input, TAG)
    }

    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra == " World!",
          "Parser `tag_s` consumed leftover input."
        );
        assert!(
          output == TAG,
          "Parser `tag_s` doesn't return the tag it matched on success. \
           Expected `{}`, got `{}`.",
          TAG,
          output
        );
      }
      other => panic!(
        "Parser `tag_s` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn tag_str_incomplete() {
    const INPUT: &str = "Hello";
    const TAG: &str = "Hello World!";

    match tag_s!(INPUT, TAG) {
      Err(Err::Incomplete(_)) => (),
      other => {
        panic!(
          "Parser `tag_s` didn't require more input when it should have. \
           Got `{:?}`.",
          other
        );
      }
    };
  }

  #[test]
  fn tag_str_error() {
    const INPUT: &str = "Hello World!";
    const TAG: &str = "Random"; // TAG must be closer than INPUT.

    match tag_s!(INPUT, TAG) {
      Err(Err::Error(_)) => (),
      other => {
        panic!(
          "Parser `tag_s` didn't fail when it should have. Got `{:?}`.`",
          other
        );
      }
    };
  }

  #[test]
  fn take_s_succeed() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";

    match take_s!(INPUT, 9) {
      Ok((extra, output)) => {
        assert!(
          extra == LEFTOVER,
          "Parser `take_s` consumed leftover input. Leftover `{}`.",
          extra
        );
        assert!(
          output == CONSUMED,
          "Parser `take_s` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
          CONSUMED,
          output
        );
      }
      other => panic!(
        "Parser `take_s` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_until_s_succeed() {
    const INPUT: &str = "βèƒôřèÂßÇ∂áƒƭèř";
    const FIND: &str = "ÂßÇ∂";
    const CONSUMED: &str = "βèƒôřè";
    const LEFTOVER: &str = "ÂßÇ∂áƒƭèř";

    match take_until_s!(INPUT, FIND) {
      Ok((extra, output)) => {
        assert!(
          extra == LEFTOVER,
          "Parser `take_until_s`\
           consumed leftover input. Leftover `{}`.",
          extra
        );
        assert!(
          output == CONSUMED,
          "Parser `take_until_s`\
           doens't return the string it consumed on success. Expected `{}`, got `{}`.",
          CONSUMED,
          output
        );
      }
      other => panic!(
        "Parser `take_until_s` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_s_incomplete() {
    const INPUT: &str = "βèƒôřèÂßÇá";

    match take_s!(INPUT, 13) {
      Err(Err::Incomplete(_)) => (),
      other => panic!(
        "Parser `take_s` didn't require more input when it should have. \
         Got `{:?}`.",
        other
      ),
    }
  }

  use internal::Needed;

  pub fn is_alphabetic(c: char) -> bool {
    (c as u8 >= 0x41 && c as u8 <= 0x5A) || (c as u8 >= 0x61 && c as u8 <= 0x7A)
  }
  #[test]
  fn take_while_s() {
    named!(f<&str,&str>, take_while_s!(is_alphabetic));
    let a = "";
    let b = "abcd";
    let c = "abcd123";
    let d = "123";

    assert_eq!(f(&a[..]), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(f(&b[..]), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(f(&c[..]), Ok((&d[..], &b[..])));
    assert_eq!(f(&d[..]), Ok((&d[..], &a[..])));
  }

  #[test]
  fn take_while1_s() {
    named!(f<&str,&str>, take_while1_s!(is_alphabetic));
    let a = "";
    let b = "abcd";
    let c = "abcd123";
    let d = "123";

    assert_eq!(f(&a[..]), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(f(&b[..]), Err(Err::Incomplete(Needed::Size(1))));
    assert_eq!(f(&c[..]), Ok((&"123"[..], &b[..])));
    assert_eq!(
      f(&d[..]),
      Err(Err::Error(error_position!(&d[..], ErrorKind::TakeWhile1)))
    );
  }

  #[test]
  fn take_till_s_succeed() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";
    fn till_s(c: char) -> bool {
      c == 'á'
    }
    fn test(input: &str) -> IResult<&str, &str> {
      take_till_s!(input, till_s)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra == LEFTOVER,
          "Parser `take_till_s` consumed leftover input."
        );
        assert!(
          output == CONSUMED,
          "Parser `take_till_s` doesn't return the string it consumed on success. \
           Expected `{}`, got `{}`.",
          CONSUMED,
          output
        );
      }
      other => panic!(
        "Parser `take_till_s` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_while_s_succeed_none() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const CONSUMED: &str = "";
    const LEFTOVER: &str = "βèƒôřèÂßÇáƒƭèř";
    fn while_s(c: char) -> bool {
      c == '9'
    }
    fn test(input: &str) -> IResult<&str, &str> {
      take_while_s!(input, while_s)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra == LEFTOVER,
          "Parser `take_while_s` consumed leftover input."
        );
        assert!(
          output == CONSUMED,
          "Parser `take_while_s` doesn't return the string it consumed on success. \
           Expected `{}`, got `{}`.",
          CONSUMED,
          output
        );
      }
      other => panic!(
        "Parser `take_while_s` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn is_not_s_succeed() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const AVOID: &str = "£úçƙ¥á";
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";
    fn test(input: &str) -> IResult<&str, &str> {
      is_not_s!(input, AVOID)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra == LEFTOVER,
          "Parser `is_not_s` consumed leftover input. Leftover `{}`.",
          extra
        );
        assert!(
          output == CONSUMED,
          "Parser `is_not_s` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
          CONSUMED,
          output
        );
      }
      other => panic!(
        "Parser `is_not_s` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_until_and_consume_s_succeed() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const FIND: &str = "ÂßÇ";
    const OUTPUT: &str = "βèƒôřè";
    const LEFTOVER: &str = "áƒƭèř";

    match take_until_and_consume_s!(INPUT, FIND) {
      Ok((extra, output)) => {
        assert!(
          extra == LEFTOVER,
          "Parser `take_until_and_consume_s`\
           consumed leftover input. Leftover `{}`.",
          extra
        );
        assert!(
          output == OUTPUT,
          "Parser `take_until_and_consume_s`\
           doens't return the string it selected on success. Expected `{}`, got `{}`.",
          OUTPUT,
          output
        );
      }
      other => panic!(
        "Parser `take_until_and_consume_s` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_while_s_succeed_some() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";
    fn while_s(c: char) -> bool {
      c == 'β' || c == 'è' || c == 'ƒ' || c == 'ô' || c == 'ř' || c == 'è' || c == 'Â' || c == 'ß' || c == 'Ç'
    }
    fn test(input: &str) -> IResult<&str, &str> {
      take_while_s!(input, while_s)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra == LEFTOVER,
          "Parser `take_while_s` consumed leftover input."
        );
        assert!(
          output == CONSUMED,
          "Parser `take_while_s` doesn't return the string it consumed on success. \
           Expected `{}`, got `{}`.",
          CONSUMED,
          output
        );
      }
      other => panic!(
        "Parser `take_while_s` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn is_not_s_fail() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const AVOID: &str = "βúçƙ¥";
    fn test(input: &str) -> IResult<&str, &str> {
      is_not_s!(input, AVOID)
    }
    match test(INPUT) {
      Err(Err::Error(_)) => (),
      other => panic!(
        "Parser `is_not_s` didn't fail when it should have. Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_while1_s_succeed() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";
    fn while1_s(c: char) -> bool {
      c == 'β' || c == 'è' || c == 'ƒ' || c == 'ô' || c == 'ř' || c == 'è' || c == 'Â' || c == 'ß' || c == 'Ç'
    }
    fn test(input: &str) -> IResult<&str, &str> {
      take_while1_s!(input, while1_s)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra == LEFTOVER,
          "Parser `take_while1_s` consumed leftover input."
        );
        assert!(
          output == CONSUMED,
          "Parser `take_while1_s` doesn't return the string it consumed on success. \
           Expected `{}`, got `{}`.",
          CONSUMED,
          output
        );
      }
      other => panic!(
        "Parser `take_while1_s` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_until_and_consume_s_incomplete() {
    const INPUT: &str = "βèƒôřè";
    const FIND: &str = "βèƒôřèÂßÇ";

    match take_until_and_consume_s!(INPUT, FIND) {
      Err(Err::Incomplete(_)) => (),
      other => panic!(
        "Parser `take_until_and_consume_s` didn't require more input when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_until_s_incomplete() {
    const INPUT: &str = "βèƒôřè";
    const FIND: &str = "βèƒôřèÂßÇ";

    match take_until_s!(INPUT, FIND) {
      Err(Err::Incomplete(_)) => (),
      other => panic!(
        "Parser `take_until_s` didn't require more input when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn is_a_s_succeed() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const MATCH: &str = "βèƒôřèÂßÇ";
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";
    fn test(input: &str) -> IResult<&str, &str> {
      is_a_s!(input, MATCH)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra == LEFTOVER,
          "Parser `is_a_s` consumed leftover input. Leftover `{}`.",
          extra
        );
        assert!(
          output == CONSUMED,
          "Parser `is_a_s` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
          CONSUMED,
          output
        );
      }
      other => panic!(
        "Parser `is_a_s` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_while1_s_fail() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    fn while1_s(c: char) -> bool {
      c == '9'
    }
    fn test(input: &str) -> IResult<&str, &str> {
      take_while1_s!(input, while1_s)
    }
    match test(INPUT) {
      Err(Err::Error(_)) => (),
      other => panic!(
        "Parser `take_while1_s` didn't fail when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn is_a_s_fail() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const MATCH: &str = "Ûñℓúçƙ¥";
    fn test(input: &str) -> IResult<&str, &str> {
      is_a_s!(input, MATCH)
    }
    match test(INPUT) {
      Err(Err::Error(_)) => (),
      other => panic!(
        "Parser `is_a_s` didn't fail when it should have. Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_until_and_consume_s_error() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const FIND: &str = "Ráñδô₥";

    match take_until_and_consume_s!(INPUT, FIND) {
      Err(Err::Incomplete(_)) => (),
      other => panic!(
        "Parser `take_until_and_consume_s` didn't fail when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_until_s_error() {
    const INPUT: &str = "βèƒôřèÂßÇáƒƭèř";
    const FIND: &str = "Ráñδô₥";

    match take_until_s!(INPUT, FIND) {
      Err(Err::Incomplete(_)) => (),
      other => panic!(
        "Parser `take_until_and_consume_s` didn't fail when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  #[cfg(feature = "alloc")]
  fn recognize_is_a_s() {
    let a = "aabbab";
    let b = "ababcd";

    named!(f <&str,&str>, recognize!(many1!(complete!(alt!( tag_s!("a") | tag_s!("b") )))));

    assert_eq!(f(&a[..]), Ok((&a[6..], &a[..])));
    assert_eq!(f(&b[..]), Ok((&b[4..], &b[..4])));
  }

  #[test]
  fn utf8_indexing() {
    named!(dot(&str) -> &str,
        tag_s!(".")
      );

    let _ = dot("點");
  }

  #[cfg(feature = "alloc")]
  #[test]
  fn case_insensitive() {
    named!(test<&str,&str>, tag_no_case!("ABcd"));
    assert_eq!(test("aBCdefgh"), Ok(("efgh", "aBCd")));
    assert_eq!(test("abcdefgh"), Ok(("efgh", "abcd")));
    assert_eq!(test("ABCDefgh"), Ok(("efgh", "ABCD")));

    named!(test2<&str,&str>, tag_no_case!("ABcd"));
    assert_eq!(test2("aBCdefgh"), Ok(("efgh", "aBCd")));
    assert_eq!(test2("abcdefgh"), Ok(("efgh", "abcd")));
    assert_eq!(test2("ABCDefgh"), Ok(("efgh", "ABCD")));
  }
}
