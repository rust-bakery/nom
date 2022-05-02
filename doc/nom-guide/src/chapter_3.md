# Chapter 3: Alternatives and Composition

In the last chapter, we saw how to convert a simple regex into a nom parser.
In this chapter, we explore features two other very important features of Nom,
alternatives, and composition.

## Alternatives

In regex, we can write `/(^abc|^def)/`, which means "match either `/^abc/` or `/^def/`".
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

fn parse_abc_or_def(input: &str) -> IResult<&str, &str> {
    alt((
        tag("abc"),
        tag("def")
    ))(input)
}

    match parse_abc_or_def("abcWorld") {
        Ok((leftover_input, output)) => {
            assert_eq!(leftover_input, "World");
            assert_eq!(output, "abc");
        },
        Err(_) => unreachable!()
    }

    match parse_abc_or_def("ghiWorld") {
        Ok((leftover_input, output)) => unreachable!(),
        Err(_) => assert!(true),
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

fn parse_abc(input: &str) -> IResult<&str, &str> {
    tag("abc")(input)
}
fn parse_def_or_ghi(input: &str) -> IResult<&str, &str> {
    alt((
        tag("def"),
        tag("ghi")
    ))(input)
}

    let input = "abcghi";
    if let Ok((remainder, abc)) = parse_abc(input) {
        if let Ok((remainder, def_or_ghi)) = parse_def_or_ghi(remainder) {
            println!("first parsed: {abc}; then parsed: {def_or_ghi};");
        }
    }
    
```

Composing tags is such a common requirement that, in fact, Nom has a few built in
combinators to do it. The simplest of these is `tuple()`. The `tuple()` combinator takes a tuple of parsers,
and either returns `Ok` with a tuple of all of their successful parses, or it 
returns the `Err` of the first failed parser.

```rust
# extern crate nom;
use nom::branch::alt;
use nom::bytes::complete::{tag};
use nom::character::complete::{digit1};
use nom::IResult;

fn parse_numbers_or_abc(input: &str) -> IResult<&str, &str> {
    alt((
        tag("abc"),
        digit1
    ))(input)
}


    let input = "abc";
    let parsed_input = parse_numbers_or_abc(input);
    match parsed_input {
        Ok((_, matched_str)) => assert_eq!(matched_str, "abc"),
        Err(_) => unreachable!()
    }
    

    let input = "def";
    let parsed_input = parse_numbers_or_abc(input);
    match parsed_input {
        Ok(_) => unreachable!(),
        Err(_) => assert!(true)
    }
```


## Extra Nom Tools

After using `alt()` and `tuple()`, you might also be interested in the `permutation()` parser, which
requires all of the parsers it contains to succeed, but in any order.

```rust
# extern crate nom;
use nom::branch::permutation;
```
