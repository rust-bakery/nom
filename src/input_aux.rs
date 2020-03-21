/// Struct to carry auxiliary data along with the input.
#[derive(Debug, Clone)]
pub struct InputAux<Aux, I> {
  /// Auxiliary data for the parsing logic.
  pub aux: Aux,

  /// Input to parse.
  pub input: I
}

impl <Aux, I> InputAux<Aux, I> {
  /// Create a new instance.
  pub fn new(aux: Aux, buf: I) -> Self {
    InputAux{aux, input: buf}
  }
}

impl <Aux: Copy, I> InputAux<Aux, I> {
  /// Create a new instance with a copy of the auxiliary data.
  pub fn wrap_with(&self, buf: I) -> Self {
    Self::new(self.aux, buf)
  }

  /// Create new instances, each with a copy of the auxiliary data.
  pub fn split_aux(&self, t1: I, t2: I) -> (Self, Self) {
    (Self::new(self.aux, t1), Self::new(self.aux, t2))
  }
}

impl <Aux: Default, I> From<I> for InputAux<Aux, I> {
  fn from(i: I) -> Self { InputAux::new(Default::default(), i) }
}

impl <Aux, I: PartialEq> PartialEq for InputAux<Aux, I> {
  fn eq(&self, rhs: &Self) -> bool {
    self.input == rhs.input
  }
}

impl <Aux, I: Eq> Eq for InputAux<Aux, I> { }

impl <Aux: Copy, I: Copy> Copy for InputAux<Aux, I> { }

impl <Aux, I> std::borrow::Borrow<I> for InputAux<Aux, &I> {
  fn borrow(&self) -> &I {
    self.input
  }
}

#[cfg(test)]
mod test {
  use crate::{error, error::ErrorKind, Err, IResult};
  use crate::InputAux;

  #[test]
  fn tagtr_succeed() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "Hello World!" };
    const TAG: &str = "Hello";
    fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
      tag!(input, TAG)
    }

    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(extra.input == " World!", "Parser `tag` consumed leftover input.");
        assert!(
          output.input == TAG,
          "Parser `tag` doesn't return the tag it matched on success. \
           Expected `{}`, got `{}`.",
          TAG,
          output.input
        );
      }
      other => panic!(
        "Parser `tag` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn tagtr_incomplete() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "Hello"  };
    const TAG: &str = "Hello World!";

    let res: IResult<_, _, error::Error<_>> = tag!(INPUT, TAG);
    match res {
      Err(Err::Incomplete(_)) => (),
      other => {
        panic!(
          "Parser `tag` didn't require more input when it should have. \
           Got `{:?}`.",
          other
        );
      }
    };
  }

  #[test]
  fn tagtr_error() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "Hello World!"  };
    const TAG: &str = "Random"; // TAG must be closer than INPUT.

    let res: IResult<_, _, error::Error<_>> = tag!(INPUT, TAG);
    match res {
      Err(Err::Error(_)) => (),
      other => {
        panic!(
          "Parser `tag` didn't fail when it should have. Got `{:?}`.`",
          other
        );
      }
    };
  }

  #[test]
  fn take_s_succeed() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"  };
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";

    let res: IResult<_, _, error::Error<_>> = take!(INPUT, 9);
    match res {
      Ok((extra, output)) => {
        assert!(
          extra.input == LEFTOVER,
          "Parser `take_s` consumed leftover input. Leftover `{}`.",
          extra.input
        );
        assert!(
          output.input == CONSUMED,
          "Parser `take_s` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
          CONSUMED,
          output.input
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
  fn take_until_succeed() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇ∂áƒƭèř"  };
    const FIND: &str = "ÂßÇ∂";
    const CONSUMED: &str = "βèƒôřè";
    const LEFTOVER: &str = "ÂßÇ∂áƒƭèř";

    let res: IResult<_, _, (_, ErrorKind)> = take_until!(INPUT, FIND);
    match res {
      Ok((extra, output)) => {
        assert!(
          extra.input == LEFTOVER,
          "Parser `take_until`\
           consumed leftover input. Leftover `{}`.",
          extra.input
        );
        assert!(
          output.input == CONSUMED,
          "Parser `take_until`\
           doens't return the string it consumed on success. Expected `{}`, got `{}`.",
          CONSUMED,
          output.input
        );
      }
      other => panic!(
        "Parser `take_until` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_s_incomplete() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇá"  };

    let res: IResult<_, _, (_, ErrorKind)> = take!(INPUT, 13);
    match res {
      Err(Err::Incomplete(_)) => (),
      other => panic!(
        "Parser `take` didn't require more input when it should have. \
         Got `{:?}`.",
        other
      ),
    }
  }

  use crate::internal::Needed;

  fn is_alphabetic(c: char) -> bool {
    (c as u8 >= 0x41 && c as u8 <= 0x5A) || (c as u8 >= 0x61 && c as u8 <= 0x7A)
  }

  #[test]
  fn take_while() {
    named!(f<InputAux<(), &str>,InputAux<(), &str>>, take_while!(is_alphabetic));
    let a = "";
    let b = "abcd";
    let c = "abcd123";
    let d = "123";

    assert_eq!(f((&a[..]).into()), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f((&b[..]).into()), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f((&c[..]).into()), Ok(((&d[..]).into(), (&b[..]).into())));
    assert_eq!(f((&d[..]).into()), Ok(((&d[..]).into(), (&a[..]).into())));
  }

  #[test]
  fn take_while1() {
    named!(f<InputAux<(), &str>,InputAux<(), &str>>, take_while1!(is_alphabetic));
    let a = "";
    let b = "abcd";
    let c = "abcd123";
    let d = "123";

    assert_eq!(f((&a[..]).into()), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f((&b[..]).into()), Err(Err::Incomplete(Needed::new(1))));
    assert_eq!(f((&c[..]).into()), Ok(((&"123"[..]).into(), (&b[..]).into())));
    assert_eq!(
      f((&d[..]).into()),
      Err(Err::Error(error_position!((&d[..]).into(), ErrorKind::TakeWhile1)))
    );
  }

  #[test]
  fn take_till_s_succeed() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"  };
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";
    fn till_s(c: char) -> bool {
      c == 'á'
    }
    fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
      take_till!(input, till_s)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra.input == LEFTOVER,
          "Parser `take_till` consumed leftover input."
        );
        assert!(
          output.input == CONSUMED,
          "Parser `take_till` doesn't return the string it consumed on success. \
           Expected `{}`, got `{}`.",
          CONSUMED,
          output.input
        );
      }
      other => panic!(
        "Parser `take_till` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_while_succeed_none() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"  };
    const CONSUMED: &str = "";
    const LEFTOVER: &str = "βèƒôřèÂßÇáƒƭèř";
    fn while_s(c: char) -> bool {
      c == '9'
    }
    fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
      take_while!(input, while_s)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra.input == LEFTOVER,
          "Parser `take_while` consumed leftover input."
        );
        assert!(
          output.input == CONSUMED,
          "Parser `take_while` doesn't return the string it consumed on success. \
           Expected `{}`, got `{}`.",
          CONSUMED,
          output.input
        );
      }
      other => panic!(
        "Parser `take_while` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn is_not_succeed() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"  };
    const AVOID: &str = "£úçƙ¥á";
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";
    fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
      is_not!(input, AVOID)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra.input == LEFTOVER,
          "Parser `is_not` consumed leftover input. Leftover `{}`.",
          extra.input
        );
        assert!(
          output.input == CONSUMED,
          "Parser `is_not` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
          CONSUMED,
          output.input
        );
      }
      other => panic!(
        "Parser `is_not` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_while_succeed_some() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"  };
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";
    fn while_s(c: char) -> bool {
      c == 'β'
        || c == 'è'
        || c == 'ƒ'
        || c == 'ô'
        || c == 'ř'
        || c == 'è'
        || c == 'Â'
        || c == 'ß'
        || c == 'Ç'
    }
    fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
      take_while!(input, while_s)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra.input == LEFTOVER,
          "Parser `take_while` consumed leftover input."
        );
        assert!(
          output.input == CONSUMED,
          "Parser `take_while` doesn't return the string it consumed on success. \
           Expected `{}`, got `{}`.",
          CONSUMED,
          output.input
        );
      }
      other => panic!(
        "Parser `take_while` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn is_not_fail() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"  };
    const AVOID: InputAux<(), &str> = InputAux { aux: (), input: "βúçƙ¥"  };
    fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
      is_not!(input, AVOID)
    }
    match test(INPUT) {
      Err(Err::Error(_)) => (),
      other => panic!(
        "Parser `is_not` didn't fail when it should have. Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_while1_succeed() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"  };
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";
    fn while1_s(c: char) -> bool {
      c == 'β'
        || c == 'è'
        || c == 'ƒ'
        || c == 'ô'
        || c == 'ř'
        || c == 'è'
        || c == 'Â'
        || c == 'ß'
        || c == 'Ç'
    }
    fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
      take_while1!(input, while1_s)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra.input == LEFTOVER,
          "Parser `take_while1` consumed leftover input."
        );
        assert!(
          output.input == CONSUMED,
          "Parser `take_while1` doesn't return the string it consumed on success. \
           Expected `{}`, got `{}`.",
          CONSUMED,
          output.input
        );
      }
      other => panic!(
        "Parser `take_while1` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_until_incomplete() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřè"  };
    const FIND: &str = "βèƒôřèÂßÇ";

    let res: IResult<_, _, (_, ErrorKind)> = take_until!(INPUT, FIND);
    match res {
      Err(Err::Incomplete(_)) => (),
      other => panic!(
        "Parser `take_until` didn't require more input when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn is_a_succeed() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"  };
    const MATCH: &str = "βèƒôřèÂßÇ";
    const CONSUMED: &str = "βèƒôřèÂßÇ";
    const LEFTOVER: &str = "áƒƭèř";
    fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
      is_a!(input, MATCH)
    }
    match test(INPUT) {
      Ok((extra, output)) => {
        assert!(
          extra.input == LEFTOVER,
          "Parser `is_a` consumed leftover input. Leftover `{}`.",
          extra.input
        );
        assert!(
          output.input == CONSUMED,
          "Parser `is_a` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
          CONSUMED,
          output.input
        );
      }
      other => panic!(
        "Parser `is_a` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_while1_fail() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"  };
    fn while1_s(c: char) -> bool {
      c == '9'
    }
    fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
      take_while1!(input, while1_s)
    }
    match test(INPUT) {
      Err(Err::Error(_)) => (),
      other => panic!(
        "Parser `take_while1` didn't fail when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn is_a_fail() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"  };
    const MATCH: &str = "Ûñℓúçƙ¥";
    fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
      is_a!(input, MATCH)
    }
    match test(INPUT) {
      Err(Err::Error(_)) => (),
      other => panic!(
        "Parser `is_a` didn't fail when it should have. Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  fn take_until_error() {
    const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř" };
    const FIND: &str = "Ráñδô₥";

    let res: IResult<_, _, (_, ErrorKind)> = take_until!(INPUT, FIND);
    match res {
      Err(Err::Incomplete(_)) => (),
      other => panic!(
        "Parser `take_until` didn't fail when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }

  #[test]
  #[cfg(feature = "alloc")]
  fn recognize_is_a() {
    let a = "aabbab";
    let b = "ababcd";

    named!(f <InputAux<(), &str>,InputAux<(), &str>>, recognize!(many1!(complete!(alt!( tag!("a") | tag!("b") )))));

    assert_eq!(f((&a[..]).into()), Ok(((&a[6..]).into(), (&a[..]).into())));
    assert_eq!(f((&b[..]).into()), Ok(((&b[4..]).into(), (&b[..4]).into())));
  }

  #[test]
  fn utf8_indexing() {
    named!(dot(InputAux<(), &str>) -> InputAux<(), &str>,
      tag!(".")
    );

    let _ = dot("點".into());
  }

  #[cfg(feature = "alloc")]
  #[test]
  fn case_insensitive() {
    named!(test<InputAux<(), &str>,InputAux<(), &str>>, tag_no_case!("ABcd"));
    assert_eq!(test("aBCdefgh".into()), Ok(("efgh".into(), "aBCd".into())));
    assert_eq!(test("abcdefgh".into()), Ok(("efgh".into(), "abcd".into())));
    assert_eq!(test("ABCDefgh".into()), Ok(("efgh".into(), "ABCD".into())));

    named!(test2<InputAux<(), &str>,InputAux<(), &str>>, tag_no_case!("ABcd"));
    assert_eq!(test2("aBCdefgh".into()), Ok(("efgh".into(), "aBCd".into())));
    assert_eq!(test2("abcdefgh".into()), Ok(("efgh".into(), "abcd".into())));
    assert_eq!(test2("ABCDefgh".into()), Ok(("efgh".into(), "ABCD".into())));
  }

  #[test]
  fn recurse_limit() {
    use crate::branch::alt;
    use crate::bytes::complete::tag;
    use crate::sequence::delimited;

    const DEPTH: i32 = 8;
    const INPUT: InputAux<i32, &str> = InputAux { aux: 0, input: "([([([([x])])])]) World!" };

    fn test(depth: i32, mut input: InputAux<i32, &str>) -> crate::IResult<InputAux<i32, &str>, InputAux<i32, &str>> {
      fn cp(mut i: InputAux<i32, &str>) -> crate::IResult<InputAux<i32, &str>, InputAux<i32, &str>> {
        i.aux -= 1;
        if i.aux < 0 {
          tag("never match")(i)
        } else {
          delimited(tag("("), alt((tag("x"), cp, csp)), tag(")"))(i)
        }
      }
      fn csp(mut i: InputAux<i32, &str>) -> crate::IResult<InputAux<i32, &str>, InputAux<i32, &str>> {
        i.aux -= 1;
        if i.aux < 0 {
          tag("never match")(i)
        } else {
          delimited(tag("["), alt((tag("x"), cp, csp)), tag("]"))(i)
        }
      }
      input.aux = depth;
      alt((cp, csp))(input)
    }

    match test(DEPTH, INPUT) {
      Ok((extra, output)) => {
        assert!(extra.input == " World!", "Parser `tag` consumed leftover input.");
        assert!(output.aux == 0, "Depth left over not what should be {} != 0.", output.aux);
        assert!(
          output.input == "x",
          "Parser `tag` doesn't return the tag it matched on success. \
           Expected `{}`, got `{}`.",
          "x",
          output.input
        );
      }
      other => panic!(
        "Parser `tag` didn't succeed when it should have. \
         Got `{:?}`.",
        other
      ),
    };

    match test(DEPTH - 1, INPUT) {
      Err(Err::Error(_)) => (),
      other => panic!(
        "Parser didn't reach max depth when it should have. \
         Got `{:?}`.",
        other
      ),
    };
  }
}
