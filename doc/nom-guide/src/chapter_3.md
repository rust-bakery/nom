# Chapter 3: Alternatives and Composition

In the last chapter, we saw how to create simple parsers using the `tag` function;
and some of Nom's prebuilt parsers.

In this chapter, we explore two other widely used features of Nom:
alternatives and composition.

## Alternatives

Sometimes, we might want to choose between two parsers; and we're happy with
either being used.

Nom gives us a similar ability through the `alt()` combinator.

```rust
# extern crate nom;
use nom::branch::alt;
```

The `alt()` combinator will execute each parser in a tuple until it finds one
that does not error. If all error, then by default you are given the error from 
the last error.

We can see a basic example of `alt()` below.

```rust
# extern crate nom;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::IResult;
# use std::error::Error;

fn parse_abc_or_def(input: &str) -> IResult<&str, &str> {
    alt((
        tag("abc"),
        tag("def")
    ))(input)
}

fn main() -> Result<(), Box<dyn Error>> {
    let (leftover_input, output) = parse_abc_or_def("abcWorld")?;
    assert_eq!(leftover_input, "World");
    assert_eq!(output, "abc");

    assert!(parse_abc_or_def("ghiWorld").is_err());
#   Ok(())
}
```

## Composition

Now that we can create more interesting regexes, we can compose them together.
The simplest way to do this is just to evaluate them in sequence:

```rust
# extern crate nom;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::IResult;
# use std::error::Error;

fn parse_abc(input: &str) -> IResult<&str, &str> {
    tag("abc")(input)
}
fn parse_def_or_ghi(input: &str) -> IResult<&str, &str> {
    alt((
        tag("def"),
        tag("ghi")
    ))(input)
}

fn main() -> Result<(), Box<dyn Error>> {
    let input = "abcghi";
    let (remainder, abc) = parse_abc(input)?;
    let (remainder, def_or_ghi) = parse_def_or_ghi(remainder)?;
    println!("first parsed: {abc}; then parsed: {def_or_ghi};");
    
#   Ok(())
}
```

Composing tags is such a common requirement that, in fact, Nom has a few built in
combinators to do it. The simplest of these is `tuple()`. The `tuple()` combinator takes a tuple of parsers,
and either returns `Ok` with a tuple of all of their successful parses, or it 
returns the `Err` of the first failed parser.

```rust
# extern crate nom;
use nom::sequence::tuple;
```


```rust
# extern crate nom;
use nom::branch::alt;
use nom::sequence::tuple;
use nom::bytes::complete::tag_no_case;
use nom::character::complete::{digit1};
use nom::IResult;
# use std::error::Error;

fn parse_base(input: &str) -> IResult<&str, &str> {
    alt((
        tag_no_case("a"),
        tag_no_case("t"),
        tag_no_case("c"),
        tag_no_case("g")
    ))(input)
}

fn parse_pair(input: &str) -> IResult<&str, (&str, &str)> {
    // the many_m_n combinator might also be appropriate here.
    tuple((
        parse_base,
        parse_base,
    ))(input)
}

fn main() -> Result<(), Box<dyn Error>> {
    let (remaining, parsed) = parse_pair("aTcG")?;
    assert_eq!(parsed, ("a", "T"));
    assert_eq!(remaining, "cG");
    
    assert!(parse_pair("Dct").is_err());

#   Ok(())
}
```


## Extra Nom Tools

After using `alt()` and `tuple()`, you might also be interested in a few other parsers that do similar things:

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [delimited](https://docs.rs/nom/latest/nom/sequence/fn.delimited.html) | `delimited(char('('), take(2), char(')'))` | `"(ab)cd"` | `Ok(("cd", "ab"))` ||
| [preceded](https://docs.rs/nom/latest/nom/sequence/fn.preceded.html) | `preceded(tag("ab"), tag("XY"))` | `"abXYZ"` | `Ok(("Z", "XY"))` ||
| [terminated](https://docs.rs/nom/latest/nom/sequence/fn.terminated.html) | `terminated(tag("ab"), tag("XY"))` | `"abXYZ"` | `Ok(("Z", "ab"))` ||
| [pair](https://docs.rs/nom/latest/nom/sequence/fn.pair.html) | `pair(tag("ab"), tag("XY"))` | `"abXYZ"` | `Ok(("Z", ("ab", "XY")))` ||
| [separated_pair](https://docs.rs/nom/latest/nom/sequence/fn.separated_pair.html) | `separated_pair(tag("hello"), char(','), tag("world"))` | `"hello,world!"` | `Ok(("!", ("hello", "world")))` ||
