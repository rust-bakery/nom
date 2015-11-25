use ::{
    Err,
    ErrorKind,
    IResult,
    Needed,

};

fn tag_str<'a, E>(input: &'a str, tag: &str) -> IResult<&'a str, &'a str, E> {
    if input.len() < tag.len() {
        IResult::Incomplete(Needed::Size(input.len()))
    } else if input.starts_with(tag) {
        IResult::Done(&input[tag.len()..], &input[0..tag.len()])
    } else {
        IResult::Error(Err::Position(ErrorKind::Tag, input))
    }
}
