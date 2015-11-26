//! Parsers and helper functions operating on strings, especially useful when writing parsers for
//! text-based formats.

use ::{
    Err,
    ErrorKind,
    IResult,
    Needed,

};

/// Parses the input for the supplied tag, and returns it on success.
// TODO: Examples once we have figured out a way to do str-based parsing in Nom.
pub fn tag_str<'a>(input: &'a str, tag: &str) -> IResult<&'a str, &'a str> {
    if input.len() < tag.len() {
        IResult::Incomplete(Needed::Size(input.len()))
    } else if input.starts_with(tag) {
        IResult::Done(&input[tag.len()..], &input[0..tag.len()])
    } else {
        IResult::Error(Err::Position(ErrorKind::Tag, input))
    }
}

#[cfg(test)]
mod test {
    use ::IResult;
    use super::tag_str;

    #[test]
    fn tag_str_succeed() {
        const INPUT: &'static str = "Hello World!";
        const TAG: &'static str = "Hello";

        match tag_str(INPUT, TAG) {
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

        match tag_str(INPUT, TAG) {
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

        match tag_str(INPUT, TAG) {
            IResult::Error(_) => (),
            other => {
                panic!("Parser `tag_str` didn't fail when it should have. Got `{:?}`.`", other);
            },
        };
    }
}
